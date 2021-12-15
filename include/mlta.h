#ifndef __MLTA_H__
#define __MLTA_H__

#include "llvm/ADT/MapVector.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"

struct MLTAType
{
	static bool isIdentical(MLTAType *Ty){return true;};
	
	MLTAType(llvm::Value *Elem)
	{
		this->Elem = Elem;
	}

	~MLTAType()
	{
		this->Elem = nullptr;
		this->LayeredType.clear();
	}

	void addType(llvm::Type *Ty)
	{
		this->LayeredType.push_back(Ty);
	}

	std::vector<llvm::Type *>
	getType()
	{
		return this->LayeredType;
	}

private:
	std::vector<llvm::Type *> LayeredType;
	llvm::Value * Elem;
};

struct FuncTy : public MLTAType
{
};

struct ICallTy : public MLTAType
{
};

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