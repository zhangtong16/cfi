#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"

#include "flta.h"
#include "utils.h"

using namespace llvm;

#define LOG(X)                            \
	X->print(llvm::errs());               \
	llvm::errs() << "\n";                 \
	X->getDebugLoc().print(llvm::errs()); \
	llvm::errs() << "\n"

#define DEBUG 0

#if (DEBUG)
static void
printFLTAResult(raw_ostream &OutS, const SmallVector<FunctionType *> &Vals);
static void
printTypeMapResult(raw_ostream &OutS, const llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs);
static void
printICallTargets(raw_ostream &OutS, const std::vector<CallBase *> ICalls);
static void
printFuncs(raw_ostream &OutS, const std::vector<Function *> Funcs);
static void
printCompare(raw_ostream &OutS, const CallBase *ICall);
static void
printICalls(raw_ostream &OutS, const std::vector<CallBase *> ICalls);
static void
printIDMapResult(raw_ostream &OutS, const llvm::DenseMap<uint64_t, std::vector<uint64_t>> ICallID2FuncID);
#endif

static std::vector<CallBase *> ICalls;
static std::vector<FunctionType *> ICallTypes;

static std::vector<Function *> AddrTakenFuncs;
static std::vector<FunctionType *> AddrTakenFuncTypes;

// Initialized via createType2FuncMapping()
static llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs; /* The Type has a numeric suffix */

// Initialized via makeFuncAddrArray()
static std::vector<Constant *> FuncAddrs;
// Initialized via makeICallAddrArray
// ICallAddr means the address of such asm snippets: 
// ----------    
//     mov 0x0, %arg1
//     mov 0x1, %arg2
//     call %eax
// ----------
// We cannot accurately get the address of `call eax` instruction, 
// because We are at the IR level, not the MIR level.
static std::vector<Constant *> ICallAddrs;

#define FUNC_ADDRS_SYMBOL   "__cfi_func_addr_array"
#define FUNC_ADDRS_LEN      FuncAddrs.size()

#define ICALL_ADDRS_SYMBOL  "__cfi_icall_addr_array"
#define ICALL_ADDRS_LEN     ICallAddrs.size()

#define FUNC_ADDRS_SECTION  ".__cfi_func_addrs"
#define ICALL_ADDRS_SECTION ".__cfi_icall_addrs"

#define LOOP_PRINTER "__cfi_loop_printer"
enum PRINTEE {FUNC_ADDRS, ICALL_ADDRS};

// Containing the map from the ICall ID to Func ID.
// ICall ID is the ICalladdr, Func ID is the FuncAddrs.
// We assume that the order of these addrs keeps consistant.
static llvm::DenseMap<uint64_t, std::vector<uint64_t>> ICallID2FuncID;

static void
createType2FuncMapping()
{
	std::vector<Function *> Funcs;
	for (auto &Type : AddrTakenFuncTypes)
	{
		Funcs.clear();
		for (auto &Func : AddrTakenFuncs)
		{
			if (Func->getFunctionType() == Type)
			{
				Funcs.push_back(Func);
			}
		}
		if (Type2Funcs.find(Type) == Type2Funcs.end())
		{
			Type2Funcs.insert(
				std::pair<FunctionType *, std::vector<Function *>>(Type, Funcs));
		}
	}
}

static std::vector<Function *>
resolveICallTarget(CallBase *ICall)
{
	std::vector<Function *> Targets;
	Targets.clear();
	for (auto &Elem : Type2Funcs)
	{

		if (isIdenticalType(ICall->getFunctionType(), Elem.first))
		{
			Targets.insert(std::end(Targets), std::begin(Elem.second), std::end(Elem.second));
		}
	}

	return Targets;
}

static void
analysis(Module &M)
{
	for (auto &Func : M)
	{
		if (Func.hasAddressTaken())
		{
			AddrTakenFuncs.push_back(&Func);
			AddrTakenFuncTypes.push_back(Func.getFunctionType());
		}

		for (auto &BB : Func)
		{
			for (auto &Inst : BB)
			{
				auto *CB = dyn_cast<CallBase>(&Inst);
				if (nullptr != CB && CB->isIndirectCall())
				{
					ICalls.push_back(CB);
					ICallTypes.push_back(CB->getFunctionType());
				}
			}
		}
	}
}

// Create ICallAddrArray -> [i8* * N]
// an array contains the address of ICalls
// N is determined in compile time
static void
makeICallAddrArray(Module &M)
{
	/* Break BB into two pieces. */
	/* ICall is always at the front of the BB*/
	for (auto &&ICall : ICalls)
	{

		ICallAddrs.push_back(
			BlockAddress::get(
				ICall->getParent()->splitBasicBlock(
					ICall,
					".icall")));
	}

	ArrayType *ICallAddrArrayTy = ArrayType::get(
		IntegerType::getInt8PtrTy(
			M.getContext()),
		ICalls.size());
	M.getOrInsertGlobal(ICALL_ADDRS_SYMBOL, ICallAddrArrayTy);
	GlobalVariable *ICallAddrArray = M.getNamedGlobal(ICALL_ADDRS_SYMBOL);
	ICallAddrArray->setLinkage(GlobalValue::ExternalLinkage);
	ICallAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				Type::getInt8PtrTy(M.getContext()),
				ICalls.size()),
			llvm::makeArrayRef(ICallAddrs)));
	ICallAddrArray->setSection(ICALL_ADDRS_SECTION);
}

// Create FuncAddrArray -> [i8* * N]
// an array contains the address of address-taken functions
// N is determined in compile time
static void
makeFuncAddrArray(Module &M)
{

	for (auto &Func : AddrTakenFuncs)
	{
		/* llvm::Function is llvm::Constant */
		/* bitcast Function* to int8* */
		FuncAddrs.push_back(
			ConstantExpr::getBitCast(
				Func,
				PointerType::getInt8PtrTy(
					M.getContext())));
	}

	ArrayType *FuncAddrArrayTy = ArrayType::get(
		IntegerType::getInt8PtrTy(
			M.getContext()),
		AddrTakenFuncs.size());
	M.getOrInsertGlobal(FUNC_ADDRS_SYMBOL, FuncAddrArrayTy);
	GlobalVariable *FuncAddrArray = M.getNamedGlobal(FUNC_ADDRS_SYMBOL);
	FuncAddrArray->setLinkage(GlobalValue::ExternalLinkage);
	FuncAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				Type::getInt8PtrTy(M.getContext()),
				AddrTakenFuncs.size()),
			llvm::makeArrayRef(FuncAddrs)));
	FuncAddrArray->setSection(FUNC_ADDRS_SECTION);
}

static uint64_t
getFuncID(Function *Func)
{
	uint64_t id = 0;
	auto it = std::find(AddrTakenFuncs.begin(), AddrTakenFuncs.end(), Func);

	/* If not Found, It must be a fatal. */
	assert(it != AddrTakenFuncs.end() && "Can't find the FuncID!");
	assert(it >= AddrTakenFuncs.begin() && "Something bad happend when look for FuncID!");
	id = it - AddrTakenFuncs.begin();
	return id;
}

static std::vector<uint64_t>
getFuncIDList(std::vector<Function *> Funcs)
{
	std::vector<uint64_t> FuncIDs;
	for (auto &&Func : Funcs)
	{
		FuncIDs.push_back(getFuncID(Func));
	}
	return FuncIDs;
}

static void
makeICallID2FuncIDMapping()
{
	uint64_t ICallIDCounter = 0;

	for (auto &&ICall : ICalls)
	{
		auto FuncIDs = getFuncIDList(resolveICallTarget(ICall));
		ICallID2FuncID.insert(
			std::pair<uint64_t, std::vector<uint64_t>>(
				ICallIDCounter,
				FuncIDs));
		ICallIDCounter++;
	}
}

// HashArray contains the value of `sha1(icall_addr xor icall_target)`
// `icall_addr` and `icall_target` are determinded in load-time.
// Which means the `sha1()` can only be evaluated in runtime.
// Thus we also need a instrumentation to evaluate the sha1.
// See `static void makeHashArrayEval()`

#define HASH_ARRAY_LENGTH 1000000
static void
makeHashArray()
{
}

//////////////////////////// INSTRUMENTATION /////////////////////////////////

// instrument a loop to print an array of addrs
static Function *
makeLoopPrinter(Module &M)
{
	// check if we had make LoopPrinter earlier.
	auto Func = M.getFunction(LOOP_PRINTER);
	if (nullptr != Func)
	{
		return Func;
	}

	/* create printf(i8*, ...) declarations*/
	std::vector<Type *> PrintfProtoTypeArgs;
	PrintfProtoTypeArgs.push_back(Type::getInt8PtrTy(M.getContext()));
	FunctionType *PrintfTy = FunctionType::get(
		Type::getInt32Ty(M.getContext()),
		true);

	M.getOrInsertFunction("printf", PrintfTy);
	Function *Printf = M.getFunction("printf");
	//-----------------------------//
	/* uint64_t *p, uint64_t len */
	std::vector<Type *> ArgTys;
	ArgTys.push_back(Type::getInt64PtrTy(M.getContext()));
	ArgTys.push_back(Type::getInt32Ty(M.getContext()));
	/* void (uint64_t *) */
	FunctionType *FuncTy = FunctionType::get(
		Type::getVoidTy(M.getContext()),
		ArgTys, false);
	Func = Function::Create(
		FuncTy,
		Function::ExternalLinkage,
		LOOP_PRINTER,
		M);

	// prepare the args' names
	auto Args = Func->arg_begin();
	auto *Arg1 = Args++;
	Arg1->setName("p");
	auto *Arg2 = Args++;
	Arg2->setName("len");

	// create the entry basic block
	BasicBlock *EntryBB = BasicBlock::Create(M.getContext(), "entry", Func);
	BasicBlock *ForCond = BasicBlock::Create(M.getContext(), "for.cond", Func);
	BasicBlock *ForBody = BasicBlock::Create(M.getContext(), "for.body", Func);
	BasicBlock *ForInc = BasicBlock::Create(M.getContext(), "for.inc", Func);
	BasicBlock *ForEnd = BasicBlock::Create(M.getContext(), "for.end", Func);

	// entry
	IRBuilder<> Builder(EntryBB);
	// %p.addr = alloca i64*
	// %i      = alloc i32
	auto *P_Addr = Builder.CreateAlloca(Type::getInt64PtrTy(M.getContext()), 0, "p.addr");
	auto *I_Addr = Builder.CreateAlloca(Type::getInt32Ty(M.getContext()), 0, "i");
	// store i64* %p, i64** %p.addr
	// store i32 0  , i32 %i*
	Builder.CreateStore(Arg1, P_Addr);
	Builder.CreateStore(ConstantInt::get(Type::getInt32Ty(M.getContext()), 0), I_Addr);
	// br label %for.cond
	Builder.CreateBr(ForCond);
	// for.cond
	Builder.SetInsertPoint(ForCond);
	// %0 = load i32, i32* %i
	// %cmp = icmp slt i32 %0, %len
	// br i1 %cmp, label %for.body, label %for.end
	auto I = Builder.CreateLoad(Type::getInt32Ty(M.getContext()), I_Addr);
	auto CMP = Builder.CreateICmpSLT(I, Arg2);
	Builder.CreateCondBr(CMP, ForBody, ForEnd);
	// for.body
	// 	%P = load i32, i32* %P_Addr
	//  %I_64 = sext i32 %3 to i64
	//  %Elem_Addr = getelementptr inbounds i64, i64* %P, i64 %I__64
	//  %Elem = load i64, i64* %Elem_Addr
	Builder.SetInsertPoint(ForBody);
	auto P = Builder.CreateLoad(Type::getInt64PtrTy(M.getContext()), P_Addr);
	auto I_64 = Builder.CreateSExt(
		I,
		Type::getInt64Ty(M.getContext()));
	auto Elem_Addr = Builder.CreateGEP(Type::getInt64Ty(M.getContext()), P, I_64);
	auto Elem = Builder.CreateLoad(Type::getInt64Ty(M.getContext()), Elem_Addr);
	// call @printf("%p\n", Elem)
	std::vector<Value *> PrintArgs;
	auto FormatStr = Builder.CreateGlobalStringPtr("%p\n");
	PrintArgs.push_back(FormatStr);
	PrintArgs.push_back(Elem);
	Builder.CreateCall(Printf, PrintArgs);
	// br label %for.inc
	Builder.CreateBr(ForInc);
	// for.inc
	Builder.SetInsertPoint(ForInc);
	I = Builder.CreateLoad(Type::getInt32Ty(M.getContext()), I_Addr);
	auto Inc = Builder.CreateNSWAdd(
		I,
		ConstantInt::get(
			Type::getInt32Ty(M.getContext()),
			1));
	Builder.CreateStore(Inc, I_Addr);
	Builder.CreateBr(ForCond);

	// for.end
	Builder.SetInsertPoint(ForEnd);
	// ret void
	Builder.CreateRetVoid();
	return Func;
}

static void
makeLoopPrinterInstrument(Module &M, StringRef FName, enum PRINTEE Printee)
{
	Function *LoopPrinter = makeLoopPrinter(M);
	Function *TargetFunc = M.getFunction(FName);
	IRBuilder<> MainBuilder(&*TargetFunc->getEntryBlock().getFirstInsertionPt());
	std::vector<Value *> CalleeArgs;
	GlobalVariable *GV = nullptr;
	Value *BitCast = nullptr;
	switch (Printee)
	{
	case FUNC_ADDRS:
		GV = M.getGlobalVariable(FUNC_ADDRS_SYMBOL, true);
		BitCast = MainBuilder.CreateBitCast(
						GV,
						Type::getInt64PtrTy(M.getContext()));
		CalleeArgs.push_back(BitCast);
		CalleeArgs.push_back(ConstantInt::get(
						Type::getInt32Ty(M.getContext()),
						FUNC_ADDRS_LEN));
		break;
	case ICALL_ADDRS:
		GV = M.getGlobalVariable(ICALL_ADDRS_SYMBOL, true);
		BitCast = MainBuilder.CreateBitCast(
						GV,
						Type::getInt64PtrTy(M.getContext()));
		CalleeArgs.push_back(BitCast);
		CalleeArgs.push_back(ConstantInt::get(
						Type::getInt32Ty(M.getContext()),
						ICALL_ADDRS_LEN));
		break;
	default:
		llvm_unreachable("Printee is invalid!");
		break;
	}

	MainBuilder.CreateCall(LoopPrinter, CalleeArgs);
}

// Naive hash
static void
makeHashArrayEval()
{
}

static void
makeInstrumentCheck()
{
}

FLTA::Result
FLTA::runOnModule(Module &M)
{
	analysis(M);
	makeICallAddrArray(M);
	makeFuncAddrArray(M);
	makeLoopPrinterInstrument(M, "main", FUNC_ADDRS);
	makeLoopPrinterInstrument(M, "main", ICALL_ADDRS);
}

PreservedAnalyses
FLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
	runOnModule(M);
	// printFuncs(llvm::errs(), AddrTakenFuncs);
	createType2FuncMapping();
	makeICallID2FuncIDMapping();
	// printIDMapResult(llvm::errs(), ICallID2FuncID);
	// printCompare(llvm::errs(), (CallBase *)0x555556835b60);
	// printMapResult(llvm::errs(), Type2Funcs);
	// printFLTAResult(llvm::errs(), AddrTakenFuncTypes);
	// printICallTargets(llvm::errs(), ICalls);
	// printICalls(llvm::errs(), ICalls);
	return PreservedAnalyses::none();
}

//-----------------------------------------------------------------------------
// New PM Registration
//-----------------------------------------------------------------------------
llvm::PassPluginLibraryInfo getFLTAPluginInfo()
{
	return {LLVM_PLUGIN_API_VERSION, "FLTA", LLVM_VERSION_STRING,
			[](PassBuilder &PB)
			{
				PB.registerPipelineParsingCallback(
					[](StringRef Name, ModulePassManager &MPM,
					   ArrayRef<PassBuilder::PipelineElement>)
					{
						if (Name == "flta")
						{
							MPM.addPass(FLTA());
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
	return getFLTAPluginInfo();
}

//------------------------------------------------------------------------------
// Helper functions
//------------------------------------------------------------------------------
#if (DEBUG)
static void printFLTAResult(raw_ostream &OutS, const std::vector<FunctionType *> &Vals)
{
	OutS << "================================================="
		 << "\n";
	OutS << "FLTA implemetations\n";
	OutS << "=================================================\n";
	const char *str1 = "ICALL INSTURCTIONS";

	OutS << format("%-20s\n", str1);
	OutS << "-------------------------------------------------"
		 << "\n";

	for (auto &Val : Vals)
	{
		Val->print(OutS);
		OutS << "\n";
	}

	OutS << "-------------------------------------------------"
		 << "\n\n";
}

static void
printFuncs(raw_ostream &OutS, const std::vector<Function *> Funcs)
{
	for (auto &&Func : Funcs)
	{
		OutS << Func->getName();
		OutS << "\n";
	}
}

static void
printTypeMapResult(raw_ostream &OutS, const llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs)
{
	for (auto &Elem : Type2Funcs)
	{
		OutS << "===============FUNCTION  TYPE================";
		OutS << "\n";
		Elem.first->print(OutS);
		OutS << "\n";
		OutS << "=================FUNCTIONs===================";
		OutS << "\n";
		for (auto &Func : Elem.second)
		{
			OutS << Func->getName();
			OutS << "\n";
		}
		OutS << "\n";
		OutS << "\n";
	}
}

static void
printIDMapResult(raw_ostream &OutS, const llvm::DenseMap<uint64_t, std::vector<uint64_t>> ICallID2FuncID)
{
	for (auto &Elem : ICallID2FuncID)
	{
		OutS << "=================ICALL  ID===================";
		OutS << "\n";
		OutS << Elem.first << " ";
		ICalls[Elem.first]->print(OutS);
		OutS << "\n";
		OutS << "=================FUNC   ID===================";
		OutS << "\n";
		for (auto &FuncID : Elem.second)
		{
			OutS << FuncID << " ";
			OutS << AddrTakenFuncs[FuncID]->getName();
			OutS << "\n";
		}
		OutS << "\n";
		OutS << "\n";
	}
}

static void printICallTargets(raw_ostream &OutS, const std::vector<CallBase *> &ICalls)
{
	for (auto &ICall : ICalls)
	{
		OutS << "===============ICALL================ \n";
		LOG(ICall);
		OutS << ICall << "\n";
		OutS << "==============TARGETS=============== \n";
		for (auto &Target : resolveICallTarget(ICall))
		{
			OutS << Target->getName();
			OutS << "\n";
		}
		OutS << "\n\n";
	}
}

static void printCompare(raw_ostream &OutS, const CallBase *ICall)
{
	for (auto &Func : AddrTakenFuncs)
	{
		if (Func->getName().equals("ngx_writev_chain"))
		{
			ICall->print(OutS);
			OutS << "\n";
			if (isIdenticalType(ICall->getFunctionType(), Func->getFunctionType()))
			{
				OutS << "ok\n";
			}
		}
	}
}

static void printICalls(raw_ostream &OutS, const std::vector<CallBase *> ICalls)
{
	for (auto &&ICall : ICalls)
	{
		LOG(ICall);
	}
}
#endif