#ifndef MARKANALYSIS_H
#define MARKANALYSIS_H

#include "llvm/IR/PassManager.h"

class MarkAnalysis {
  public:
    typedef std::map<int, llvm::BasicBlock *> Result;
    static llvm::StringRef name() { return "MarkAnalysis"; }
    Result run(llvm::Function &F, llvm::FunctionAnalysisManager *AM);
    static void *ID() { return static_cast<void *>(&PassID); }

  private:
    static char PassID;
};

#endif // MARKANALYSIS_H
