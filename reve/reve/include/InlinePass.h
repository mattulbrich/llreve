#pragma once

#include "llvm/IR/LegacyPassManager.h"

class InlinePass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "MarkAnalysis"; }
    bool runOnFunction(llvm::Function &fun);
    static char ID;
    InlinePass() : llvm::FunctionPass(ID) {}
};
