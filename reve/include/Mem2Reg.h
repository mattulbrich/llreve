#pragma once

#include "llvm/IR/PassManager.h"

struct PromotePass {
  public:
    PromotePass() = default;
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "PromotePass"; }
};
