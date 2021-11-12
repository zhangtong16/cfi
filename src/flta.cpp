#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Instructions.h"

#include "flta.h"
#include "utils.h"

using namespace llvm;

static void
printFLTAResult(raw_ostream &OutS, const SmallVector<FunctionType *> &Vals);
static void
printMapResult(raw_ostream &OutS, const llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs);
static void
printICallTargets(raw_ostream &OutS, const std::vector<CallBase *> ICalls);
static void
printFuncs(raw_ostream &OutS, const std::vector<Function *> Funcs);
static void
printCompare(raw_ostream &OutS, const CallBase *ICall);

#define LOG(X)                            \
	X->print(llvm::errs());               \
	llvm::errs() << "\n";                 \
	X->getDebugLoc().print(llvm::errs()); \
	llvm::errs() << "\n"

static std::vector<CallBase *> ICalls;
static std::vector<FunctionType *> ICallTypes;

static std::vector<Function *> AddrTakenFuncs;
static std::vector<FunctionType *> AddrTakenFuncTypes;
static llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs;

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
	// if (Type2Funcs.find(ICall->getFunctionType()) != Type2Funcs.end())
	// {
	// 	Targets = Type2Funcs[ICall->getFunctionType()];
	// }
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

FLTA::Result
FLTA::runOnModule(Module &M)
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

PreservedAnalyses
FLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
	runOnModule(M);
	// printFuncs(llvm::errs(), AddrTakenFuncs);
	createType2FuncMapping();
	// printCompare(llvm::errs(), (CallBase *)0x555556835b60);
	// printMapResult(llvm::errs(), Type2Funcs);
	// printFLTAResult(llvm::errs(), AddrTakenFuncTypes);
	printICallTargets(llvm::errs(), ICalls);
	return PreservedAnalyses::all();
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
printMapResult(raw_ostream &OutS, const llvm::DenseMap<FunctionType *, std::vector<Function *>> Type2Funcs)
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

static void printICallTargets(raw_ostream &OutS, const std::vector<CallBase *> ICalls)
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