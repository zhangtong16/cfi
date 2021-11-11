#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

#include "flta.h"

using namespace llvm;

static void printFLTAResult(raw_ostream &OutS, const ResultVector &ICalls);
// New PM implementation
//

FLTA::Result
FLTA::runOnModule(Module &M)
{
	llvm::SmallVector<const Instruction *> Res;

	for (auto &Func : M)
		for (auto &BB : Func)
			for (auto &Inst : BB)
			{
				auto *CB = dyn_cast<CallBase>(&Inst);
				if (nullptr == CB)
				{
					continue;
				}

				auto CallTarget = CB->getCalledFunction();
				if (CallTarget != nullptr)
				{
					// It is a direct call inst!
					continue;
				}

				// filtering out bitcast, introduced by wllvm
				if (auto *CstExpr = dyn_cast<ConstantExpr>(CB->getCalledOperand()))
				{
					if (CstExpr->isCast())
					{
						continue;
					}
				}
				Res.push_back(CB);
			}

	printFLTAResult(llvm::errs(), Res);
	return Res;
}

PreservedAnalyses
FLTA::run(llvm::Module &M, llvm::ModuleAnalysisManager &)
{
	runOnModule(M);
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
static void printFLTAResult(raw_ostream &OutS, const ResultVector &ICalls)
{
	OutS << "================================================="
		 << "\n";
	OutS << "FLTA implemetations\n";
	OutS << "=================================================\n";
	const char *str1 = "ICALL INSTURCTIONS";

	OutS << format("%-20s\n", str1);
	OutS << "-------------------------------------------------"
		 << "\n";

	for (auto &ICall : ICalls)
	{
		ICall->print(OutS);
		OutS << "\n";
	}

	OutS << "-------------------------------------------------"
		 << "\n\n";
}