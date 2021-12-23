#ifndef __UTILS_H__
#define __UTILS_H__

#include <llvm/IR/DerivedTypes.h>
#include <llvm/Transforms/Utils/FunctionComparator.h>

#define DEBUG 1

#ifdef DEBUG
#define LOG(x)              \
    x->print(llvm::errs()); \
    llvm::errs() << "\n"
#define LOG_STR(x) llvm::errs() << x << "\n"
#else
#define LOG(x)
#define LOG_STR(x)
#endif

static std::unordered_set<const llvm::Type *> VisitedTypes;

static inline bool isEmptyStructPtr(const llvm::PointerType *PtrTy)
{
    llvm::Type *EleType = PtrTy->getElementType();

    if (EleType->getTypeID() == llvm::Type::StructTyID)
    {
        if (llvm::cast<llvm::StructType>(EleType)->getNumElements() == 0)
        {
            return true;
        }
    }
    return false;
}

static bool isI8PtrTy(llvm::Type *Ty)
{
	bool isI8Ptr = false;
	if (Ty->isPointerTy())
		if (auto PtrElemTy = llvm::dyn_cast<llvm::IntegerType>(Ty->getPointerElementType()))
		{
			if (PtrElemTy->getBitWidth() == 8)
				isI8Ptr = true;
		}
	return isI8Ptr;
}

static bool __isIdenticalType(const llvm::Type *left, const llvm::Type *right)
{

    if (left == right)
        return true;

    if (left->getTypeID() != right->getTypeID())
        return false;
    switch (left->getTypeID())
    {
    case llvm::Type::IntegerTyID:
        return llvm::cast<llvm::IntegerType>(left)->getBitWidth() == llvm::cast<llvm::IntegerType>(right)->getBitWidth();

    // left == right would have returned true earlier, because types are uniqued.
    case llvm::Type::VoidTyID:
    case llvm::Type::FloatTyID:
    case llvm::Type::DoubleTyID:
    case llvm::Type::X86_FP80TyID:
    case llvm::Type::FP128TyID:
    case llvm::Type::PPC_FP128TyID:
    case llvm::Type::LabelTyID:
    case llvm::Type::MetadataTyID:
    case llvm::Type::TokenTyID:
        return true;

    case llvm::Type::PointerTyID:
    {
        auto left_ptr = llvm::cast<llvm::PointerType>(left);
        auto right_ptr = llvm::cast<llvm::PointerType>(right);
        assert(left_ptr && right_ptr && "Both types must be pointers here.");

        // if both of them are opaque
        if (left_ptr->isOpaquePointerTy() && right_ptr->isOpaquePointerTy())
        {
            return true;
        }
        // if one of them is opaque
        else if (left_ptr->isOpaquePointerTy() || right_ptr->isOpaquePointerTy())
        {
            return false;
        }
        // neither

        // { }* cannot be compared with
        // https://lists.llvm.org/pipermail/cfe-dev/2016-November/051513.html
        if (isEmptyStructPtr(left_ptr) || isEmptyStructPtr(right_ptr))
        {
            return true;
        }

        // Avoid infinite recursive
        // struct A
        // {
        //    int i;
        //    struct A *ptr;
        // }

        if (VisitedTypes.find(left_ptr->getElementType()) != VisitedTypes.end())
        {
            return true;
        }
        VisitedTypes.insert(left_ptr->getElementType());

        return __isIdenticalType(left_ptr->getElementType(), right_ptr->getElementType());
    }
    case llvm::Type::StructTyID:
    {
        auto left_struct = llvm::cast<llvm::StructType>(left);
        auto right_struct = llvm::cast<llvm::StructType>(right);

        if (left_struct->getNumElements() == 0 || right_struct->getNumElements() == 0)
        {
            return true;
        }

        if (left_struct->getNumElements() != right_struct->getNumElements())
        {
            return false;
        }

        if (left_struct->isPacked() != right_struct->isPacked())
        {
            return false;
        }

        for (unsigned i = 0, e = left_struct->getNumElements(); i != e; ++i)
        {
            if (!__isIdenticalType(left_struct->getElementType(i), right_struct->getElementType(i)))
                return false;
        }

        return true;
    }

    case llvm::Type::FunctionTyID:
    {
        auto left_function = llvm::cast<llvm::FunctionType>(left);
        auto right_function = llvm::cast<llvm::FunctionType>(right);
        if (left_function->getNumParams() != right_function->getNumParams())
            return false;

        if (left_function->isVarArg() != right_function->isVarArg())
            return false;

        if (!__isIdenticalType(left_function->getReturnType(), right_function->getReturnType()))
            return false;

        for (unsigned i = 0, e = left_function->getNumParams(); i != e; ++i)
        {
            if (!__isIdenticalType(left_function->getParamType(i), right_function->getParamType(i)))
                return false;
        }

        return true;
    }

    case llvm::Type::ArrayTyID:
    {
        auto *STyL = llvm::cast<llvm::ArrayType>(left);
        auto *STyR = llvm::cast<llvm::ArrayType>(right);
        if (STyL->getNumElements() != STyR->getNumElements())
            return false;
        return __isIdenticalType(STyL->getElementType(), STyR->getElementType());
    }
    case llvm::Type::FixedVectorTyID:
    case llvm::Type::ScalableVectorTyID:
    {
        auto left_sequential = llvm::cast<llvm::VectorType>(left);
        auto right_sequential = llvm::cast<llvm::VectorType>(right);

        if (left_sequential->getElementCount().isScalable() != right_sequential->getElementCount().isScalable())
            return false;

        if (left_sequential->getElementCount() != right_sequential->getElementCount())
            return false;

        return __isIdenticalType(left_sequential->getElementType(), right_sequential->getElementType());
    }

    default:
        return false;
    }
}

bool isIdenticalType(const llvm::Type *left, const llvm::Type *right)
{
    VisitedTypes.clear();
    return __isIdenticalType(left, right);
}

bool isFuncPtrTy(const llvm::Type *Ty)
{
    auto *PTy = llvm::dyn_cast<llvm::PointerType>(Ty);
    if (nullptr != PTy)
    {
        return isFuncPtrTy(PTy->getElementType());
    }

    if (Ty->isFunctionTy())
    {
        return true;
    }

    return false;
}

static llvm::Type *extractTy(llvm::Type *Ty)
{
    if (Ty->isArrayTy())
    {
        return extractTy(Ty->getArrayElementType());
    }
    else if (Ty->isPointerTy())
    {
        return extractTy(Ty->getPointerElementType());
    }
    else
    {
        return Ty;
    }
}
#endif // __UTILS_H