#include "AnnotStackPass.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

#include <iostream>
#include <set>

llvm::PreservedAnalyses AnnotStackPass::run(llvm::Function &F,
                                            llvm::FunctionAnalysisManager *AM) {
    (void)AM;
    std::set<llvm::Value *> StackVars;
    for (auto &Block : F) {
        for (auto &Inst : Block) {
            if (llvm::isa<llvm::AllocaInst>(Inst)) {
                StackVars.insert(&Inst);
            } else if (llvm::isa<llvm::LoadInst>(Inst)) {
                llvm::LoadInst &Load = llvm::cast<llvm::LoadInst>(Inst);
                llvm::Value *Val = Load.getPointerOperand();
                if (StackVars.find(Val) != StackVars.end()) {
                    markStackInstruction(Inst, "reve.stack_load");
                }
            } else if (llvm::isa<llvm::StoreInst>(Inst)) {
                llvm::StoreInst &Store = llvm::cast<llvm::StoreInst>(Inst);
                llvm::Value *Val = Store.getPointerOperand();
                if (StackVars.find(Val) != StackVars.end()) {
                    markStackInstruction(Inst, "reve.stack_store");
                }
            }
        }
    }
    return llvm::PreservedAnalyses::none();
}

void markStackInstruction(llvm::Instruction &Inst, std::string MetadataName) {
    llvm::LLVMContext &Ctxt = Inst.getContext();
    llvm::MDNode *N =
        llvm::MDNode::get(Ctxt, llvm::MDString::get(Ctxt, "true"));
    Inst.setMetadata(MetadataName, N);
}
