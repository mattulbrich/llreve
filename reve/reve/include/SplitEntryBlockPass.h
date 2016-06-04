#pragma once

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"

class SplitBlockPass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "SplitEntryBlockPass"; }
    bool runOnFunction(llvm::Function &Fun);
    SplitBlockPass() : llvm::FunctionPass(ID) {}
    static char ID;
};
