#pragma once

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class InstCombinePass : public llvm::FunctionPass {
 public:
    static llvm::StringRef name() {
        return "InstCombinePass";
    }
    bool runOnFunction(llvm::Function &Fun) override;
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    InstCombinePass() : llvm::FunctionPass(ID) {}
    static char ID;
};
