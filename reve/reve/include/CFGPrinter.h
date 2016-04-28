#pragma once

#include "llvm/IR/LegacyPassManager.h"

class CFGViewerPass : public llvm::FunctionPass {
  public:
    CFGViewerPass() : llvm::FunctionPass(ID) {}
    bool runOnFunction(llvm::Function &F) override;
    static auto name() -> llvm::StringRef { return "CFGViewerPass"; }
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    static char ID;
};
