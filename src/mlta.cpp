#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"

#include "mlta.h"
#include "utils.h"

using namespace llvm;

#define DEBUG 1

static std::vector<Function *> AddrTakenFuncs;
static std::vector<CallBase *> ICalls;

static std::unordered_set<llvm::Function *> GVFuncs;
static std::unordered_set<llvm::Function *> InstFuncs;

///////////////////////////////////////////////////////////////////
//// (func, use) -> [path]
using PathsTy = std::map<std::pair<Value *, Value *>, std::vector<Value *>>;
static PathsTy InstPaths;
static PathsTy GVPaths;
//// helper data structures
static std::vector<Value *> Path;
static std::unordered_set<PHINode *> VisitedPHINodes;
static std::unordered_set<Value *> VisitedConstants;
static bool STOREINST = false;

///////////////////////////////////////////////////////////////////
//// Type only analysis data strutures
using IndiceTy = uint32_t;
using StructIdx = std::pair<Type *, IndiceTy>;
using FuncStructMap = std::map<Type *, std::vector<StructIdx>>;
static FuncStructMap FP2S;
using Struct2StructMap = std::map<Type *, std::vector<StructIdx>>;
static Struct2StructMap S2S;

//////////////////////////////////////////////////////////////////
//// For Multi-Layered Type
//// There is no field sensitivity currently
using MLT = std::vector<Type *>;
using MLT2Func = std::map<std::vector<Type *>, std::unordered_set<Value *>>;
using MLT2FuncElem = std::pair<MLT, std::unordered_set<Value *>>;
static MLT2Func MLT2FuncMap;

#ifdef DEBUG
static void printFP2StructMapping();
static void printS2SMapping();
static void printFuncs();
static void printPaths(std::map<std::pair<Value *, Value *>, std::vector<Value *>> Paths);
static void printMLTMapping();
#endif

static bool isGVFunc(User *U);
static bool isInstFunc(User *U);
static void getInstPath(Value *Val);
static void getGVPath(Value *Val);
static void addStructMapping(std::map<Type *, std::vector<StructIdx>> &Map, Type *Key, StructIdx ValueElem);
static void addMLT2FuncMapping(MLT2Func &Map, MLT &Key, Value *ValueElem);

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

static void
divideFunc()
{
    for (auto &&Func : AddrTakenFuncs)
    {
        if (isGVFunc(Func))
            GVFuncs.insert(Func);
        if (isInstFunc(Func))
            InstFuncs.insert(Func);
    }
}

static void
getInstFuncPath()
{
    for (auto &&Func : InstFuncs)
        for (auto &&U : Func->users())
        {
            STOREINST = false;
            Path.clear();
            VisitedPHINodes.clear();
            getInstPath(U);
            if (!Path.empty() && STOREINST)
            {
                auto Pair1 = std::pair<Value *, Value *>(Func, U);
                auto Pair2 = std::pair<std::pair<Value *, Value *>, std::vector<Value *>>(Pair1, Path);
                InstPaths.insert(Pair2);
            }
        }
    // clean
    Path.clear();
}

static void
getGVFuncPath()
{
    for (auto &&Func : GVFuncs)
        for (auto &&U : Func->users())
        {
            Path.clear();
            VisitedConstants.clear();
            getGVPath(U);
            if (!Path.empty())
            {
                auto Pair1 = std::pair<Value *, Value *>(Func, U);
                auto Pair2 = std::pair<std::pair<Value *, Value *>, std::vector<Value *>>(Pair1, Path);
                GVPaths.insert(Pair2);
            }
        }
    // clean
    Path.clear();
}

static void
makeStructMapping(Module &M)
{
    for (auto &&StructTy : M.getIdentifiedStructTypes())
    {
        for (unsigned int i = 0; i < StructTy->getNumElements(); i++)
        {
            auto ElemType = extractTy(StructTy->getElementType(i));

            if (ElemType->isIntegerTy())
            {
                continue;
            }
            if (ElemType->isStructTy())
            {
                if ((ElemType->getNumContainedTypes() != 0))
                    addStructMapping(S2S, ElemType, StructIdx(StructTy, i));
                continue;
            }
            if (isFuncPtrTy(ElemType))
            {
                addStructMapping(FP2S, ElemType, StructIdx(StructTy, i));
                continue;
            }

            LOG(ElemType);
            LOG(StructTy);
            llvm_unreachable("Unknown Type!!!");
        }
    }
}

static void
makeMLT2InstFuncMapping()
{
    MLT MLTy;
    for (auto &&Path : InstPaths)
    {
        auto Func = Path.first.first;
        MLTy.clear();
        for (auto &&Val : Path.second)
        {
            if (auto GEPI = dyn_cast<GetElementPtrInst>(Val))
            {
                auto Ty = GEPI->getPointerOperandType();

                if (std::find(MLTy.begin(), MLTy.end(), Ty) == MLTy.end())
                    MLTy.push_back(Ty);

                if (isI8PtrTy(Ty))
                    break;
                continue;
            }

            if (auto SI = dyn_cast<StoreInst>(Val))
            {
                auto Ty = SI->getValueOperand()->stripPointerCasts()->getType();
                if (std::find(MLTy.begin(), MLTy.end(), Ty) == MLTy.end())
                    MLTy.push_back(Ty);
                continue;
            }

            if (auto GEPOp = dyn_cast<GEPOperator>(Val))
            {
                auto Ty = GEPOp->getPointerOperandType();

                if (std::find(MLTy.begin(), MLTy.end(), Ty) == MLTy.end())
                    MLTy.push_back(Ty);

                if (isI8PtrTy(Ty))
                    break;
                continue;
            }
        }
        addMLT2FuncMapping(MLT2FuncMap, MLTy, Func);
    }
}

static void
makeMLT2GVFuncMapping()
{
    MLT MLTy;
    
    for (auto &&Path : GVPaths)
    {
        auto Func = Path.first.first;
        MLTy.clear();
        MLTy.push_back(Func->getType());
        for (auto &&Val : Path.second)
        {
            if (auto GV = dyn_cast<GlobalValue>(Val))
            {
                auto Ty = extractArrayTy(GV->getType());
                auto Lambda = [&Ty](const auto &Elem){return isIdenticalType(Ty, Elem);};
                if (std::find_if(MLTy.begin(), MLTy.end(), Lambda) == MLTy.end())
                    MLTy.push_back(Ty);
            }
        }
        addMLT2FuncMapping(MLT2FuncMap, MLTy, Func);
    }
}

// TODO: Verify Inst and GV Path


void MLTA::runOnModule(Module &M)
{
    makeStructMapping(M);
    analysis(M);
    divideFunc();
    getInstFuncPath();
    getGVFuncPath();
    makeMLT2InstFuncMapping();
    makeMLT2GVFuncMapping();
}

PreservedAnalyses
MLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
    runOnModule(M);
    printFuncs();
    printPaths(GVPaths);
    printMLTMapping();
    return PreservedAnalyses::none();
}

// An valid InstPath is consisted with
// [select/phi/store] -> [gep/load] -> [alloc/global val/call/args]
// source -------------> propagation-> sink
static void
getInstPath(Value *Val)
{
    if (isa<Instruction>(Val))
    {
        // sink
        if (isa<CallBase>(Val) || isa<ICmpInst>(Val) || isa<AllocaInst>(Val) || isa<BinaryOperator>(Val) || isa<ReturnInst>(Val) || isa<IntToPtrInst>(Val) || isa<AllocaInst>(Val))
        {
            Path.push_back(Val);
            return;
        }

        // source
        // StoreInst is necessary
        if (auto SI = dyn_cast<StoreInst>(Val))
        {
            Path.push_back(SI);
            STOREINST = true;
            getInstPath(SI->getPointerOperand());
            return;
        }
        if (auto PN = dyn_cast<PHINode>(Val))
        {
            if (VisitedPHINodes.find(PN) != VisitedPHINodes.end())
                return;
            VisitedPHINodes.insert(PN);

            Path.push_back(PN);

            bool TrackUser = false;
            for (auto &&InComingVal : PN->incoming_values())
            {
                if (isFuncPtrTy(InComingVal->stripPointerCasts()->getType()))
                {
                    TrackUser = true;
                    break;
                }
            }
            if (TrackUser)
            {
                for (auto &&U : PN->users())
                    getInstPath(U);
            }
            else
            {
                for (auto &&InComingVal : PN->incoming_values())
                    getInstPath(InComingVal);
            }
            return;
        }
        if (auto SI = dyn_cast<SelectInst>(Val))
        {
            Path.push_back(SI);
            if (isFuncPtrTy(SI->getTrueValue()->stripPointerCasts()->getType()) || isFuncPtrTy(SI->getFalseValue()->stripPointerCasts()->getType()))
            {
                for (auto &&U : SI->users())
                    getInstPath(U);
            }
            else
            {
                getInstPath(SI->getTrueValue());
                getInstPath(SI->getFalseValue());
            }
            return;
        }

        // propagation
        if (auto LI = dyn_cast<LoadInst>(Val))
        {
            Path.push_back(LI);
            getInstPath(LI->getPointerOperand());
            return;
        }
        if (auto GEPI = dyn_cast<GetElementPtrInst>(Val))
        {
            Path.push_back(GEPI);
            if (isFuncPtrTy(GEPI->getPointerOperand()->stripPointerCasts()->getType()))
            { // some case using gep to get fptr
                return;
            }
            getInstPath(GEPI->getPointerOperand());
            return;
        }
        if (auto BC = dyn_cast<BitCastInst>(Val))
        {
            Path.push_back(BC);
            getInstPath(BC->getOperand(0));
            return;
        }
        LOG(Val);
        llvm_unreachable("The Val is a Instruction but we cannot handle!!!");
    }
    if (isa<Operator>(Val))
    {
        // propagation
        if (auto GEPOp = dyn_cast<GEPOperator>(Val))
        {
            Path.push_back(GEPOp);
            getInstPath(GEPOp->getPointerOperand());
            return;
        }
        if (auto BCOp = dyn_cast<BitCastOperator>(Val))
        {
            Path.push_back(BCOp);
            // bitcast func to <ty>
            if (Path.empty())
                for (auto &&U : BCOp->users())
                    getInstPath(U);
            // bitcast %reg to <ty>
            else
                Path.push_back(BCOp->getOperand(0));
            return;
        }
        if (auto P2IOp = dyn_cast<PtrToIntOperator>(Val))
        {
            Path.push_back(P2IOp);
            for (auto &&U : P2IOp->users())
                getInstPath(U);
            return;
        }
    }
    // sink
    if (isa<Argument>(Val) || isa<Constant>(Val))
    {
        Path.push_back(Val);
        return;
    }

    LOG(Val);
    llvm_unreachable("We do not know which Type the Val is!!!");
}

static void
getGVPath(Value *Val)
{
    if (isa<Constant>(Val))
    {
        if (VisitedConstants.find(Val) != VisitedConstants.end())
            return;
        VisitedConstants.insert(Val);
        if (isa<GlobalValue>(Val))
            Path.push_back(Val);

        for (auto &&U : Val->users())
        {
            if (!isa<Instruction>(U))
                getGVPath(U);
        }
        return;
    }

    // BitCast, GEP, Ptr2int, ...
    if (isa<Operator>(Val))
    {
        for (auto &&U : Val->users())
            if (!isa<Instruction>(U))
            {
                getGVPath(Val);
            }
        return;
    }

    if (isa<Instruction>(Val) || nullptr == Val)
        return;
    LOG(Val);
    llvm_unreachable("Unhandled GVPath!!!");
}

static bool
isGVFunc(User *U)
{
    bool rc = false;
    if (nullptr == U || isa<Instruction>(U))
        return false;

    if (isa<GlobalVariable>(U))
        return true;

    for (auto &&User : U->users())
    {
        if (isGVFunc(User))
        {
            rc = true;
            break;
        }
    }
    return rc;
}

static bool
isInstFunc(User *U)
{
    bool rc = false;
    if (nullptr == U || isa<GlobalVariable>(U) || isa<CallBase>(U))
        return false;

    if (isa<StoreInst>(U) || isa<SelectInst>(U) || isa<PHINode>(U))
        return true;

    for (auto &&User : U->users())
    {
        if (isInstFunc(User))
        {
            rc = true;
            break;
        }
    }
    return rc;
}

static void
addStructMapping(std::map<Type *, std::vector<StructIdx>> &Map, Type *Key, StructIdx ValueElem)
{
    if (Map.find(Key) == Map.end())
    {
        std::vector<StructIdx> Value;
        Value.push_back(ValueElem);
        auto Pair = std::pair<Type *, std::vector<StructIdx>>(Key, Value);
        Map.insert(Pair);
    }
    else
    {
        auto Pair = Map.find(Key);
        (*Pair).second.push_back(ValueElem);
    }
}

static void addMLT2FuncMapping(MLT2Func &Map, MLT &Key, Value *ValueElem)
{
    if (Map.find(Key) == Map.end())
    {
        std::unordered_set<Value *> Value;
        Value.insert(ValueElem);
        auto Pair = MLT2FuncElem(Key, Value);
        Map.insert(Pair);
    }
    else
    {
        auto Pair = Map.find(Key);
        (*Pair).second.insert(ValueElem);
    }
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
static void printFP2StructMapping()
{
    for (auto &&Map : FP2S)
    {
        LOG_STR("======== FuncPtrTy ========");
        LOG(Map.first);
        LOG_STR("======== StructTy ========");
        for (auto &&StructIdx : Map.second)
        {
            LOG(StructIdx.first);
            LOG_STR(StructIdx.second);
        }
        LOG_STR("");
    }
}

static void printS2SMapping()
{
    for (auto &&Map : S2S)
    {
        LOG_STR("======== StructTy ========");
        LOG(Map.first);
        LOG_STR("======== StructTy ========");
        for (auto &&StructIdx : Map.second)
        {
            LOG(StructIdx.first);
            LOG_STR(StructIdx.second);
        }
        LOG_STR("");
    }
}

static void printFuncs()
{
    LOG_STR("========== InstFuncs =========");
    for (auto &&Func : InstFuncs)
        LOG_STR(Func->getName());
    LOG_STR("========== GVFuncs =========");
    for (auto &&Func : GVFuncs)
        LOG_STR(Func->getName());
}

static void printPaths(std::map<std::pair<Value *, Value *>, std::vector<Value *>> Paths)
{
    for (auto &&Elem : Paths)
    {
        LOG_STR("=========== USER ===========");
        LOG_STR(Elem.first.first->getName());
        LOG(Elem.first.second);
        LOG_STR("=========== PATH ===========");
        for (auto &Val : Elem.second)
        {
            if (Val->getName().empty())
            {
                LOG(Val);
            }
            else
            {
                LOG_STR(Val->getName());
            }
        }
        LOG_STR("");
    }
}

static void printMLTMapping()
{
    for (auto &&Elem : MLT2FuncMap)
    {
        for (auto &&Ty : Elem.first)
        {
            LOG(Ty);
        }
        for (auto &&Func : Elem.second)
        {
            LOG_STR(Func->getName());
        }
        LOG_STR("");
    }
}
#endif