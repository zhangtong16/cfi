#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"

#include "mlta.h"
#include "utils.h"

using namespace llvm;

#define DEBUG 0

#define LOG(x)              \
    x->print(llvm::errs()); \
    llvm::errs() << "\n"
#define LOG_STR(x) llvm::errs() << x << "\n"

static std::vector<Function *> AddrTakenFuncs;
static std::vector<CallBase *> ICalls;

static llvm::DenseMap<std::pair<Value *, Value *>, std::vector<Value *>> InstPaths;
static llvm::DenseMap<std::pair<Value *, Value *>, std::vector<Value *>> GVPaths;
static std::vector<Value *> Path;
static std::unordered_set<PHINode *> VisitedPHINodes;
static std::unordered_set<GlobalVariable *> VisitedGlobalVars;

static std::unordered_set<llvm::Function *> GVFuncs;
static std::unordered_set<llvm::Function *> InstFuncs;

#if DEBUG
static void
printPath(raw_ostream &OutS, const llvm::DenseMap<std::pair<Value *, Value *>, std::vector<Value *>> InstPaths);
static void
printContainedFuncs(raw_ostream &OutS, const std::unordered_set<Function *> ContainedFPtrs);
#endif

// we assume that a InstPath is consisted with
// [select, phi_node, or store] -> [gep, load] -> alloca/global/call/args
// `Val` will be a `class User`
// `class User` can be divided into 4 categories:
//   1. Instruction
//   2. Operator
//   3. Constant <- ConstantExpr (we do not consider it)
//   4. DerivedUser (we do not consider it)
//   5. GlobalVariable
// Example:
// `getelementptr` has 3 implementations:
//   1. GetElementPtrConstantExpr (may be not used?)
//   2. GetElementPtrInst
//   3. GEPOperator
// We need handle these.
// if `Val` is a AllocaInst, or a GlobalVariable, return
static void
getInstPath(Value *Val)
{
    if (isa<Instruction>(Val))
    {

        if (isa<CallBase>(Val) || isa<ICmpInst>(Val))
        {
            Path.push_back(Val);
            return;
        }
        // store value, ptr
        if (auto SI = dyn_cast<StoreInst>(Val))
        {
            Path.push_back(SI);
            getInstPath(SI->getPointerOperand());
            return;
        }
        // value = getelementptr ptr, 0, index
        if (auto GEPI = dyn_cast<GetElementPtrInst>(Val))
        {
            Path.push_back(GEPI);
            // There are some codes which gep from a func_pointer.
            // check BPF JIT.
            // terminator.
            if (isFuncPtrTy(GEPI->getPointerOperand()->stripPointerCasts()->getType()))
            {
                return;
            }
            getInstPath(GEPI->getPointerOperand());
            return;
        }
        // value = load ptr
        if (auto LI = dyn_cast<LoadInst>(Val))
        {
            Path.push_back(LI);
            getInstPath(LI->getPointerOperand());
            return;
        }
        // value = alloc. terminator.
        if (auto LI = dyn_cast<AllocaInst>(Val))
        {
            Path.push_back(LI);
            return;
        }
        // bitcast value to <ty>
        if (auto BC = dyn_cast<BitCastInst>(Val))
        {
            Path.push_back(BC);
            // BitCastInst is a UnaryInstruction
            getInstPath(BC->getOperand(0));
            return;
        }
        // value = select i1, val1, val2
        if (auto SI = dyn_cast<SelectInst>(Val))
        { // if val1 is fptr <ty>. We need track value.
            if (isFuncPtrTy(SI->getTrueValue()->stripPointerCasts()->getType()) ||
                isFuncPtrTy(SI->getFalseValue()->stripPointerCasts()->getType()))
            {
                Path.push_back(SI);
                for (auto &&U : SI->users())
                {
                    getInstPath(U);
                }
            }
            else
            {
                Path.push_back(SI);
                getInstPath(SI->getTrueValue());
                getInstPath(SI->getFalseValue());
            }

            return;
        }
        // value = phi [val1, label1], [val2, label2]
        if (auto PN = dyn_cast<PHINode>(Val))
        {
            // if PHINode close a loop, there may be recusive PHINodes.
            // %53 = phi %49, %147
            // %147 = phi %84, %53
            // We must break this infinite recusive.
            if (VisitedPHINodes.find(PN) != VisitedPHINodes.end())
            {
                Path.push_back(Val);
                return;
            }
            VisitedPHINodes.insert(PN);

            bool NeedTrack = false;
            for (auto &&InComingVal : PN->incoming_values())
            {
                if (isFuncPtrTy(InComingVal->stripPointerCasts()->getType()))
                {
                    NeedTrack = true;
                    break;
                }
            }
            // %0 = phi [bitcast func1 to <ty>, label], []
            // %1 = phi [func1, label], [func2, label2]
            // Store %1, addr
            if (NeedTrack)
            {
                Path.push_back(PN);
                for (auto &&U : PN->users())
                {
                    getInstPath(U);
                }
            }
            else
            {
                Path.push_back(PN);
                for (auto &&InComingVal : PN->incoming_values())
                {
                    getInstPath(InComingVal);
                }
            }
            return;
        }
        // int2ptr cast. terminator
        if (auto I2PI = dyn_cast<IntToPtrInst>(Val))
        {
            Path.push_back(I2PI);
            return;
        }
        // return. terminator
        if (auto RI = dyn_cast<ReturnInst>(Val))
        {
            Path.push_back(RI);
            return;
        }
        // add, sub, mult, div ... terminator.
        if (auto BOI = dyn_cast<BinaryOperator>(Val))
        {
            Path.push_back(BOI);
            return;
        }

        LOG(Val);
        assert(false && "The Val is a instruction but we cannot handle!!!");
    }

    if (isa<Operator>(Val))
    {
        if (auto GEPOp = dyn_cast<GEPOperator>(Val))
        {
            Path.push_back(GEPOp);
            getInstPath(GEPOp->getPointerOperand());
            return;
        }
        if (auto BCOp = dyn_cast<BitCastOperator>(Val))
        {
            if (Path.empty())
            {
                // bitcast func to <ty>
                // Store bitcast func to <ty>, addr
                // Then we need handle Store
                Path.push_back(BCOp);
                for (auto &&U : BCOp->users())
                {
                    getInstPath(U);
                }
            }
            else
            {
                // bitcast addr to <ty>
                // Store func, bitcast addr to <ty>
                // Then We need handle addr
                Path.push_back(BCOp);
                Path.push_back(BCOp->getOperand(0));
            }
            return;
        }

        if (auto P2IOp = dyn_cast<PtrToIntOperator>(Val))
        {
            Path.push_back(P2IOp);
            for (auto &&U : P2IOp->users())
            {
                getInstPath(U);
            }
            return;
        }
    }
    // some terminators.
    if (isa<ConstantData>(Val) || isa<ConstantExpr>(Val) || isa<ConstantAggregate>(Val) || isa<GlobalVariable>(Val) || isa<Argument>(Val) || isa<BlockAddress>(Val))
    {
        Path.push_back(Val);
        return;
    }
    // In case we miss some check, add this to break;
    if (isa<Function>(Val))
    {
        return;
    }
    LOG(Val);
    assert(false && "We do not know which Type the Val is!!!\n");
}

static void
getGVPath(Value *Val)
{
    if (isa<Instruction>(Val))
    {
        return;
    }

       // These Constants my be used as unamed global values
    if (isa<GlobalAlias>(Val) || isa<BlockAddress>(Val) || isa<ConstantAggregate>(Val) || isa<ConstantData>(Val) || isa<ConstantExpr>(Val))
    {
        auto Const = dyn_cast<Constant>(Val);
        Path.push_back(Const);
        for (auto &&User : Const->users())
        {
            getGVPath(User);
        }
        return;
    }

    if (isa<Operator>(Val))
    {
        if (auto GEPOp = dyn_cast<GEPOperator>(Val))
        {
            Path.push_back(GEPOp);
            for (auto &&User : GEPOp->users())
            {
                if (!isa<Instruction>(User))
                    getGVPath(User);
            }
            return;
        }

        if (auto BCOp = dyn_cast<BitCastOperator>(Val))
        {
            Path.push_back(BCOp);
            for (auto &&User : BCOp->users())
            {
                if (!isa<Instruction>(User))
                    getGVPath(User);
            }
            return;
        }

        if (auto P2IOp = dyn_cast<PtrToIntOperator>(Val))
        {
            Path.push_back(P2IOp);
            for (auto &&User : P2IOp->users())
            {
                if (!isa<Instruction>(User))
                    getGVPath(User);
            }
            return;
        }
        LOG(Val);
        assert(false && "Unhandled Operators!!!");
    }

 

    if (auto GV = dyn_cast<GlobalVariable>(Val))
    {
        // break up the recusive chain.
        if (VisitedGlobalVars.find(GV) != VisitedGlobalVars.end())
        {
            Path.push_back(GV);
            return;
        }
        VisitedGlobalVars.insert(GV);
        Path.push_back(GV);

        for (auto &&User : GV->users())
        {
            getGVPath(User);
        }
        return;
    }

    LOG(Val);
    assert(false && "Unhandled corner case!!!");
}

static void
analysis(Module &M)
{
    for (auto &Func : M)
    {
        // FIXME:
        if (Func.hasAddressTaken())
        {
            AddrTakenFuncs.push_back(&Func);
        }

        for (auto &BB : Func)
        {
            for (auto &Inst : BB)
            {
                auto *CB = dyn_cast<CallBase>(&Inst);
                if (nullptr != CB && CB->isIndirectCall())
                {
                    ICalls.push_back(CB);
                }
            }
        }
    }
}

static bool
isGVContained(User *U)
{
    bool isContained = false;

    if (nullptr == U || isa<Instruction>(U))
    {
        return false;
    }

    if (isa<GlobalVariable>(U))
    {
        return true;
    }

    for (auto &&User : U->users())
    {
        if (isGVContained(User))
        {
            isContained = true;
            break;
        }
    }
    return isContained;
}

static bool
isInstContained(User *U)
{
    bool isContained = false;

    if (nullptr == U || isa<GlobalVariable>(U) || isa<CallBase>(U))
    {
        return false;
    }
    if (isa<StoreInst>(U) || isa<SelectInst>(U) || isa<PHINode>(U))
    {
        return true;
    }
    for (auto &&User : U->users())
    {
        if (isInstContained(User))
        {
            isContained = true;
            break;
        }
    }
    return isContained;
}

static void
collectContainedFunc()
{
    for (auto &&Func : AddrTakenFuncs)
    {
        if (isGVContained(Func))
        {
            GVFuncs.insert(Func);
        }
        if (isInstContained(Func))
        {
            InstFuncs.insert(Func);
        }
    }
}

static void
getFuncInstPath()
{
    for (auto &&Func : InstFuncs)
    {
        for (auto &&User : Func->users())
        {
            Path.clear();
            VisitedPHINodes.clear();
            getInstPath(User);
            if (!Path.empty())
            {
                auto Pair1 = std::pair<Value *, Value *>(Func, User);
                auto Pair2 = std::pair<std::pair<Value *, Value *>, std::vector<Value *>>(Pair1, Path);
                InstPaths.insert(Pair2);
            }
        }
    }

    for (auto &&Path : InstPaths)
    {
        if (Path.getSecond().size() == 1)
        {
            InstPaths.erase(Path.getFirst());
        }
    }
    Path.clear();
}

static void
getFuncGVPath()
{
    for (auto &&Func : GVFuncs)
    {
        for (auto &&User : Func->users())
        {
            Path.clear();
            VisitedGlobalVars.clear();
            getGVPath(User);
            if (!Path.empty())
            {
                auto Pair1 = std::pair<Value *, Value *>(Func, User);
                auto Pair2 = std::pair<std::pair<Value *, Value *>, std::vector<Value *>>(Pair1, Path);
                GVPaths.insert(Pair2);
            }
        }
    }
    Path.clear();
}

void MLTA::runOnModule(Module &M)
{
    analysis(M);
    collectContainedFunc();
    getFuncInstPath();
    getFuncGVPath();
}

PreservedAnalyses
MLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
    runOnModule(M);
    return PreservedAnalyses::none();
}

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getMLTAPluginInfo()
{
    return {LLVM_PLUGIN_API_VERSION, "MLTA", LLVM_VERSION_STRING,
            [](PassBuilder &PB)
            {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, ModulePassManager &MPM,
                       ArrayRef<PassBuilder::PipelineElement>)
                    {
                        if (Name == "mlta")
                        {
                            MPM.addPass(MLTA());
                            return true;
                        }
                        return false;
                    });
            }};
}

// This is the core interface for pass plugins. It guarantees that 'opt' will
// be able to recognize HelloWorld when added to the pass pipeline on the
// command line, i.e. via '-passes=hello-world'
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo()
{
    return getMLTAPluginInfo();
}

// Helper functions
#if DEBUG
static void
printPath(raw_ostream &OutS, const llvm::DenseMap<std::pair<Value *, Value *>, std::vector<Value *>> Paths)
{
    for (auto &Elem : Paths)
    {
        OutS << "===============The Begin Users================";
        OutS << "\n";
        OutS << Elem.first.first->getName();
        OutS << "\n";
        Elem.first.second->print(OutS);
        OutS << "\n";
        OutS << "=====================PATH=======================";
        OutS << "\n";
        for (auto &Val : Elem.second)
        {
            if (Val->getName().empty())
            {
                Val->print(OutS);
                OutS << "\n";
            }
            else 
            {
                OutS << Val->getName();
                OutS << "\n";
            }
        }
        OutS << "\n";
        OutS << "\n";
    }
}

static void
printContainedFuncs(raw_ostream &OutS, const std::unordered_set<Function *> ContainedFPtrs)
{
    for (auto &&ContainedFPtr : ContainedFPtrs)
    {
        LOG_STR(ContainedFPtr->getName());
    }
}
#endif