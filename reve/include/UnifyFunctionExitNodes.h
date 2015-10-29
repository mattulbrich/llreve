#ifndef UNIFYFUNCTIONEXITNODES_H
#define UNIFYFUNCTIONEXITNODES_H

#include "llvm/IR/PassManager.h"

class UnifyFunctionExitNodes {
  public:
    typedef llvm::BasicBlock* Result;
    static llvm::StringRef name() { return "UnifyFunctionExitNodes"; }
    static void *ID() { return static_cast<void *>(&PassID); }
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);

  private:
    static char PassID;
};

#endif // UNIFYFUNCTIONEXITNODES_H
