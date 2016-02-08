#pragma once

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class SplitEntryBlockPass {
 public:
    static llvm::StringRef name() {
        return "SplitEntryBlockPass";
    }
    llvm::PreservedAnalyses run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
};
