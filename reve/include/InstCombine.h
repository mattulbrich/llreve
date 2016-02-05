#pragma once

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class InstCombinePass {
 public:
    static llvm::StringRef name() {
        return "InstCombinePass";
    }
    llvm::PreservedAnalyses run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
};
