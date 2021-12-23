#ifndef __FLTA_H__
#define __FLTA_H__

#include "llvm/ADT/MapVector.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using ResultVector = void;

struct FLTA : public llvm::AnalysisInfoMixin<FLTA>
{
	using Result = ResultVector;
	llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
	Result runOnModule(llvm::Module &M);

	static bool isRequired() { return true; }

private:
	// A special type used by analysis passes to provide an address that
	// identifies that particular analysis pass type.
	static llvm::AnalysisKey Key;
};
#endif // FLTA_H
