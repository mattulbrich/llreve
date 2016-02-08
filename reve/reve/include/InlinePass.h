#pragma once

#include "llvm/IR/PassManager.h"

class InlinePass {
  public:
    static llvm::StringRef name() { return "MarkAnalysis"; }
    llvm::PreservedAnalyses run(llvm::Function &fun,
                                llvm::FunctionAnalysisManager *am);
};
