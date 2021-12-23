#ifndef __MLTA_H__
#define __MLTA_H__

#include "llvm/ADT/MapVector.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"

#include "utils.h"

using LayeredType = std::pair<llvm::Type *, std::vector<llvm::Value *>>;
using MultiLayeredType = std::vector<LayeredType>;

bool isIdenticalLayeredType(LayeredType &Left, LayeredType &Right)
{
	bool isIdentical = true;

	// if ty1 == ty2, and indices.size() == indices.size()
	if (isIdenticalType(Left.first, Right.first) && Left.second.size() == Right.second.size())
	{
		for (unsigned int i = 0; i < Left.second.size(); i++)
		{
			// FIXME: llvm::Constant is static?
			if (Left.second.at(i) != Right.second.at(i))
			{
				isIdentical = false;
			}
		}
	}
	else
	{
		isIdentical = false;
	}

	return isIdentical;
}

struct MLTA : public llvm::AnalysisInfoMixin<MLTA>
{
	llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &);
	void runOnModule(llvm::Module &M);

	static bool isRequired() { return true; }

private:
	// A special type used by analysis passes to provide an address that
	// identifies that particular analysis pass type.
	static llvm::AnalysisKey Key;
};

#endif // __MLTA_H__