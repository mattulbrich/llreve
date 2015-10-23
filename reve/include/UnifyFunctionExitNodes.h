#ifndef UNIFYFUNCTIONEXITNODES_H
#define UNIFYFUNCTIONEXITNODES_H

#include "llvm/IR/PassManager.h"

class UnifyFunctionExitNodes {
  public:
    typedef llvm::BasicBlock* Result;
    static llvm::StringRef name() { return "UnifyFunctionExitNodes"; }
    Result run(llvm::Function &F, llvm::FunctionAnalysisManager *AM);
    static void *ID() { return static_cast<void *>(&PassID); }

  private:
    static char PassID;
};

#endif // UNIFYFUNCTIONEXITNODES_H
