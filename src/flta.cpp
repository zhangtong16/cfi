#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

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

#define ICALL_CHECKER "__cfi_icall_checker"

// Containing the map from the ICall ID to Func ID.
// ICall ID is the ICalladdr, Func ID is the FuncAddrs.
// We assume that the order of these addrs keeps consistant.
static llvm::DenseMap<uint64_t, std::vector<uint64_t>> ICallID2FuncID;

#define VoidTy Type::getVoidTy(M.getContext())
#define I1Ty Type::getInt1Ty(M.getContext())
#define I32Ty Type::getInt32Ty(M.getContext())
#define I64Ty Type::getInt64Ty(M.getContext())

#define I8PtrTy Type::getInt8PtrTy(M.getContext())
#define I32PtrTy Type::getInt32PtrTy(M.getContext())
#define I64PtrTy Type::getInt64PtrTy(M.getContext())

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
					// CB->getCalledOperand()->print(llvm::errs());
				}
			}
		}
	}
}

// Make ICallAddrArray -> [i8* X N]
// an array contains the address of ICalls
// N is determined in compile time
static GlobalVariable *
makeICallAddrArray(Module &M)
{
	GlobalVariable *ICallAddrArray = M.getNamedGlobal(ICALL_ADDRS_SYMBOL);
	if (nullptr != ICallAddrArray)
		return ICallAddrArray;
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
		I8PtrTy,
		ICALL_ADDRS_LEN);
	M.getOrInsertGlobal(ICALL_ADDRS_SYMBOL, ICallAddrArrayTy);
	ICallAddrArray = M.getNamedGlobal(ICALL_ADDRS_SYMBOL);
	ICallAddrArray->setLinkage(GlobalValue::ExternalLinkage);
	ICallAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				I8PtrTy,
				ICALL_ADDRS_LEN),
			llvm::makeArrayRef(ICallAddrs)));
	ICallAddrArray->setSection(ICALL_ADDRS_SECTION);
	return ICallAddrArray;
}

// Make FuncAddrArray -> [i8* X N]
// an array contains the address of address-taken functions
// N is determined in compile time
static GlobalVariable *
makeFuncAddrArray(Module &M)
{
	GlobalVariable *FuncAddrArray = M.getNamedGlobal(FUNC_ADDRS_SYMBOL);
	if (nullptr != FuncAddrArray)
		return FuncAddrArray;
	for (auto &Func : AddrTakenFuncs)
	{
		/* llvm::Function is llvm::Constant */
		/* bitcast Function* to int8* */
		FuncAddrs.push_back(
			ConstantExpr::getBitCast(
				Func,
				I8PtrTy));
	}

	ArrayType *FuncAddrArrayTy = ArrayType::get(
		I8PtrTy,
		FUNC_ADDRS_LEN);
	M.getOrInsertGlobal(FUNC_ADDRS_SYMBOL, FuncAddrArrayTy);
	FuncAddrArray = M.getNamedGlobal(FUNC_ADDRS_SYMBOL);
	FuncAddrArray->setLinkage(GlobalValue::ExternalLinkage);
	FuncAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				I8PtrTy,
				FUNC_ADDRS_LEN),
			llvm::makeArrayRef(FuncAddrs)));
	FuncAddrArray->setSection(FUNC_ADDRS_SECTION);
	return FuncAddrArray;
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
CreateICallID2FuncIDMapping()
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
	PrintfProtoTypeArgs.push_back(I8PtrTy);
	FunctionType *PrintfTy = FunctionType::get(
		I32Ty,
		true);

	M.getOrInsertFunction("printf", PrintfTy);
	Function *Printf = M.getFunction("printf");
	//-----------------------------//
	/* uint64_t *p, uint64_t len */
	std::vector<Type *> ArgTys;
	ArgTys.push_back(I64PtrTy);
	ArgTys.push_back(I32Ty);
	/* void (uint64_t *) */
	FunctionType *FuncTy = FunctionType::get(
		VoidTy,
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

	// create the basic blocks
	BasicBlock *EntryBB = BasicBlock::Create(M.getContext(), "entry", Func);
	BasicBlock *ForCond = BasicBlock::Create(M.getContext(), "for.cond", Func);
	BasicBlock *ForBody = BasicBlock::Create(M.getContext(), "for.body", Func);
	BasicBlock *ForInc = BasicBlock::Create(M.getContext(), "for.inc", Func);
	BasicBlock *ForEnd = BasicBlock::Create(M.getContext(), "for.end", Func);

	// entry
	IRBuilder<> Builder(EntryBB);
	// %p.addr = alloca i64*
	// %i      = alloc i32
	auto *P_Addr = Builder.CreateAlloca(I64PtrTy, 0, "p.addr");
	auto *I_Addr = Builder.CreateAlloca(I32Ty, 0, "i");
	// store i64* %p, i64** %p.addr
	// store i32 0  , i32 %i*
	Builder.CreateStore(Arg1, P_Addr);
	Builder.CreateStore(ConstantInt::get(I32Ty, 0), I_Addr);
	// br label %for.cond
	Builder.CreateBr(ForCond);
	// for.cond
	Builder.SetInsertPoint(ForCond);
	// %0 = load i32, i32* %i
	// %cmp = icmp slt i32 %0, %len
	// br i1 %cmp, label %for.body, label %for.end
	auto I = Builder.CreateLoad(I32Ty, I_Addr);
	auto CMP = Builder.CreateICmpSLT(I, Arg2);
	Builder.CreateCondBr(CMP, ForBody, ForEnd);
	// for.body
	// 	%P = load i32, i32* %P_Addr
	//  %I_64 = sext i32 %3 to i64
	//  %Elem_Addr = getelementptr inbounds i64, i64* %P, i64 %I__64
	//  %Elem = load i64, i64* %Elem_Addr
	Builder.SetInsertPoint(ForBody);
	auto P = Builder.CreateLoad(I64PtrTy, P_Addr);
	auto I_64 = Builder.CreateSExt(
		I,
		I64Ty);
	auto Elem_Addr = Builder.CreateGEP(I64Ty, P, I_64);
	auto Elem = Builder.CreateLoad(I64Ty, Elem_Addr);
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
	I = Builder.CreateLoad(I32Ty, I_Addr);
	auto Inc = Builder.CreateNSWAdd(
		I,
		ConstantInt::get(
			I32Ty,
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
	IRBuilder<> Builder(&*TargetFunc->getEntryBlock().getFirstInsertionPt());
	std::vector<Value *> CalleeArgs;
	GlobalVariable *GV = nullptr;
	Value *BitCast = nullptr;
	switch (Printee)
	{
	case FUNC_ADDRS:
		GV = M.getGlobalVariable(FUNC_ADDRS_SYMBOL, true);
		BitCast = Builder.CreateBitCast(
						GV,
						I64PtrTy);
		CalleeArgs.push_back(BitCast);
		CalleeArgs.push_back(ConstantInt::get(
						I32Ty,
						FUNC_ADDRS_LEN));
		break;
	case ICALL_ADDRS:
		GV = M.getGlobalVariable(ICALL_ADDRS_SYMBOL, true);
		BitCast = Builder.CreateBitCast(
						GV,
						I64PtrTy);
		CalleeArgs.push_back(BitCast);
		CalleeArgs.push_back(ConstantInt::get(
						I32Ty,
						ICALL_ADDRS_LEN));
		break;
	default:
		llvm_unreachable("Printee is invalid!");
		break;
	}

	Builder.CreateCall(LoopPrinter, CalleeArgs);
}

static Function *
makeICallChecker(Module &M)
{
	// check if we had make ICallChecker earlier.
	auto Func = M.getFunction(ICALL_CHECKER);
	if (nullptr != Func)
	{
		return Func;
	}

	/*(i64, i8*)*/
	std::vector<Type *> ArgTys;
	ArgTys.push_back(I64Ty);
	ArgTys.push_back(I64Ty);
	
	/* i32 (*__cfi_icall_checker)(i64, i64)*/
	FunctionType *FuncTy = FunctionType::get(
		I32Ty,
		ArgTys, false);
	Func = Function::Create(
		FuncTy,
		Function::ExternalLinkage,
		ICALL_CHECKER,
		M);

	// prepare the args' names
	auto Args = Func->arg_begin();
	auto *Arg1 = Args++;
	Arg1->setName("func_id");
	auto *Arg2 = Args++;
	Arg2->setName("target");

	// create the basic blocks
	BasicBlock *EntryBB = BasicBlock::Create(M.getContext(), "entry", Func);
	BasicBlock *IfThenBB = BasicBlock::Create(M.getContext(), "if.then", Func);
	BasicBlock *IfElseBB = BasicBlock::Create(M.getContext(), "if.else", Func);
	BasicBlock *RetBB = BasicBlock::Create(M.getContext(), "return", Func);

	// entry
	IRBuilder<> Builder(EntryBB);
	auto RetVal = Builder.CreateAlloca(I32Ty, 0, "retval");
	auto FunIDAddr = Builder.CreateAlloca(I64Ty, 0, "func_id.addr");
	auto TargetAddr = Builder.CreateAlloca(I64Ty, 0, "target.addr");

	Builder.CreateStore(Arg1, FunIDAddr);
	Builder.CreateStore(Arg2, TargetAddr);

	auto FunID = Builder.CreateLoad(I64Ty, FunIDAddr);

	auto FunAddrArray = M.getNamedGlobal(FUNC_ADDRS_SYMBOL);
	auto BitCast = Builder.CreateBitCast(FunAddrArray, I64PtrTy);
	auto GEP = Builder.CreateGEP(BitCast, FunID);
	  
	auto ExpectedTarget = Builder.CreateLoad(I64Ty, GEP);	
	auto Target = Builder.CreateLoad(I64Ty, TargetAddr);

	auto CMP = Builder.CreateICmpEQ(ExpectedTarget, Target);
	Builder.CreateCondBr(CMP, IfThenBB, IfElseBB);

	// if.then
	Builder.SetInsertPoint(IfThenBB);
	Builder.CreateStore(ConstantInt::get(I32Ty, 0), RetVal);
	Builder.CreateBr(RetBB);

	// if.else
	Builder.SetInsertPoint(IfElseBB);
	Builder.CreateStore(ConstantInt::get(I32Ty, -1), RetVal);
	Builder.CreateBr(RetBB);
 
	// ret
	Builder.SetInsertPoint(RetBB);
	auto Ret = Builder.CreateLoad(I32Ty, RetVal);
	Builder.CreateRet(Ret);
	return Func;
}

static void
makeICallCheckerInstrument(Module &M)
{
	auto Func = makeICallChecker(M);
	uint64_t Counter = 0;
	std::vector<Value *> ICallCheckerArgs;
	llvm::SmallVector<Value *> RetVals;

	/* create void abort(void) declarations */
	std::vector<Type *> AbortProtoTypeArgs;
	AbortProtoTypeArgs.push_back(VoidTy);
	FunctionType *AbortTy = FunctionType::get(VoidTy, true);
	M.getOrInsertFunction("abort", AbortTy);
	Function *Abort = M.getFunction("abort");
	std::vector<Value *> AbortArgs;

	/* create i32 dprintf(i32, i8*, ...) declarations */
	std::vector<Type *> DprintfProtoTypeArgs;
	DprintfProtoTypeArgs.push_back(I32Ty);
	DprintfProtoTypeArgs.push_back(I8PtrTy);
	FunctionType *PrintfTy = FunctionType::get(I32Ty, true);
	M.getOrInsertFunction("dprintf", PrintfTy);
	Function *Dprintf = M.getFunction("dprintf");
	std::vector<Value *> DprintfArgs;

	for (auto &&ICall : ICalls)
	{
		// get target's IDs
		auto Iter = ICallID2FuncID.find(Counter);
		assert(Iter != ICallID2FuncID.end() && "Can not find target!!!!");
		auto Targets = (*Iter).second;
		IRBuilder<> Builder(ICall);
		AbortArgs.clear();
		RetVals.clear();
		RetVals.push_back(ConstantInt::get(I32Ty, -1));
		for (auto &&TargetID : Targets)
		{
			ICallCheckerArgs.clear();	
			auto FuncAddr = Builder.CreatePtrToInt(ICall->getCalledOperand(), I64Ty);
			ICallCheckerArgs.push_back(ConstantInt::get(I64Ty, TargetID));
			ICallCheckerArgs.push_back(FuncAddr);
			auto RetVal = Builder.CreateCall(Func, ICallCheckerArgs);
			RetVals.push_back(RetVal);
		}
		
		auto Res = Builder.CreateAnd(RetVals);
		auto CMP = Builder.CreateICmpNE(Res, ConstantInt::get(I32Ty, 0));
		auto Term = SplitBlockAndInsertIfThen(CMP, ICall, false);
		
		Builder.SetInsertPoint(Term);
		// BOOM
		// stderr => 2
		DprintfArgs.push_back(ConstantInt::get(I32Ty, 2));
		auto FormatStr = Builder.CreateGlobalStringPtr("CFI violation detected!!!\n");
		DprintfArgs.push_back(FormatStr);
		Builder.CreateCall(Dprintf, DprintfArgs);
	 	Builder.CreateCall(Abort, AbortArgs);	
		Counter++; 
	}
	
}

FLTA::Result
FLTA::runOnModule(Module &M)
{
	analysis(M);
	createType2FuncMapping();
	CreateICallID2FuncIDMapping();
}

PreservedAnalyses
FLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
	runOnModule(M);
	makeICallAddrArray(M);
	makeFuncAddrArray(M);
	#if DEBUG
	makeLoopPrinterInstrument(M, "main", FUNC_ADDRS);
	makeLoopPrinterInstrument(M, "main", ICALL_ADDRS);
	#endif
	makeICallCheckerInstrument(M);
	// printFuncs(llvm::errs(), AddrTakenFuncs);
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