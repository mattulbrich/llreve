#pragma once

#include "llvm/IR/PassManager.h"

struct ConstantProp {
  public:
    ConstantProp() = default;
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "ConstantPropPass"; }
};
