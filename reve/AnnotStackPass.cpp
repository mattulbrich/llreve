#include "AnnotStackPass.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

#include <iostream>
#include <set>

llvm::PreservedAnalyses AnnotStackPass::run(llvm::Function &F,
                                            llvm::FunctionAnalysisManager *AM) {
    int StackIndex = -1;
    (void)AM;
    std::set<llvm::Value *> StackVars;
    for (auto &Block : F) {
        for (auto &Inst : Block) {
            if (auto AllocaInst = llvm::dyn_cast<llvm::AllocaInst>(&Inst)) {
                StackIndex -= typeSize(AllocaInst->getAllocatedType());
                markStackInstruction(*AllocaInst, "reve.stack_pointer",
                                     StackIndex);
            }
        }
    }
    return llvm::PreservedAnalyses::none();
}

void markStackInstruction(llvm::Instruction &Inst, std::string MetadataName,
                          int Pointer) {
    llvm::LLVMContext &Ctxt = Inst.getContext();
    llvm::MDNode *N = llvm::MDNode::get(
        Ctxt,
        llvm::MDString::get(Ctxt, "(- " + std::to_string(-Pointer) + ")"));
    Inst.setMetadata(MetadataName, N);
}

int typeSize(llvm::Type *Ty) {
    if (auto IntTy = llvm::dyn_cast<llvm::IntegerType>(Ty)) {
        if (IntTy->getBitWidth() == 32 || IntTy->getBitWidth() == 64 ||
            IntTy->getBitWidth() == 8) {
            return 1;
        }
        llvm::errs() << "Unsupported integer bitwidth: " << IntTy->getBitWidth()
                     << "\n";
    }
    if (auto StructTy = llvm::dyn_cast<llvm::StructType>(Ty)) {
        int Size = 0;
        for (auto ElTy : StructTy->elements()) {
            Size += typeSize(ElTy);
        }
        return Size;
    }
    if (auto ArrayTy = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
        return static_cast<int>(ArrayTy->getNumElements()) *
               typeSize(ArrayTy->getElementType());
    }
    if (llvm::isa<llvm::PointerType>(Ty)) {
        return 1;
    }
    llvm::errs() << "Couldn't calculate size of type\n";
    Ty->print(llvm::errs());
    llvm::errs() << "\n";
    return 0;
}
