#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"

#include "flta.h"
#include "utils.h"

using namespace llvm;

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
printICalls(raw_ostream &OutS, const std::vector<CallBase*> ICalls);
static void
printIDMapResult(raw_ostream &OutS, const llvm::DenseMap<uint64_t, std::vector<uint64_t>> ICallID2FuncID);

#define LOG(X)                            \
	X->print(llvm::errs());               \
	llvm::errs() << "\n";                 \
	X->getDebugLoc().print(llvm::errs()); \
	llvm::errs() << "\n"

#define DEBUG 1

static std::vector<CallBase *> ICalls;
static std::vector<FunctionType *> ICallTypes;

static std::vector<Function *> AddrTakenFuncs;
static std::vector<FunctionType *> AddrTakenFuncTypes;

// Initialized via createType2FuncMapping()
static llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs; /* The Type has a numeric suffix */

// Initialized via makeFuncAddrArray()
static std::vector<Constant *> FuncAddrs;
// Initialized via makeICallAddrArray
static std::vector<Constant *> ICallAddrs;

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
					// LOG(CB);
					// LOG(CB->getFunctionType());
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
					".icall"
					)));
	}

	ArrayType *ICallAddrArrayTy = ArrayType::get(
		IntegerType::getInt8PtrTy(
			M.getContext()),
		ICalls.size());

	GlobalVariable *ICallAddrArray = new GlobalVariable(
		M,
		ICallAddrArrayTy,
		true,
		GlobalValue::ExternalLinkage,
		0,
		"icall_addr_array");
    
	ICallAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				Type::getInt8PtrTy(M.getContext()),
				ICalls.size()),
			llvm::makeArrayRef(ICallAddrs)));
	ICallAddrArray->setSection(".icall_addrs");
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
	GlobalVariable *FuncAddrArray = new GlobalVariable(
		M,
		FuncAddrArrayTy,
		true,
		GlobalValue::ExternalLinkage,
		0,
		"func_addr_array");
	FuncAddrArray->setInitializer(
		ConstantArray::get(
			ArrayType::get(
				Type::getInt8PtrTy(M.getContext()),
				AddrTakenFuncs.size()),
			llvm::makeArrayRef(FuncAddrs)));
	FuncAddrArray->setSection(".func_addrs");
}

static uint64_t
getFuncID(Function *Func)
{
	uint64_t id = 0;
	auto it = std::find(AddrTakenFuncs.begin(), AddrTakenFuncs.end(), Func);

	/* If not Found, It must be a fatal. */
	assert(it != AddrTakenFuncs.end() 
	       && "Can't find the FuncID!");
	
	assert(it >= AddrTakenFuncs.begin() 
	       && "Something bad happend when look for FuncID!"); 
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
				FuncIDs
			)
		);
		ICallIDCounter++;
	}
}

// HashArray contains the value of `sha1(icall_addr xor icall_target)`
// `icall_addr` and `icall_target` are determinded in load-time.
// Which means the `sha1()` can only be evaluated in runtime.
// Thus we also need a instrumentation to evaluate the sha1.
// See `static void makeHashArrayEval()`
static void
makeHashArray()
{

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
}

PreservedAnalyses
FLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
	runOnModule(M);
	// printFuncs(llvm::errs(), AddrTakenFuncs);
	createType2FuncMapping();
	makeICallID2FuncIDMapping();
	printIDMapResult(llvm::errs(), ICallID2FuncID);
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

static void printICalls(raw_ostream &OutS, const std::vector<CallBase*> ICalls)
{
	for (auto &&ICall : ICalls)
	{
		LOG(ICall);
	}
}