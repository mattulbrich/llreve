#ifndef PATHANALYSIS_H
#define PATHANALYSIS_H

#include "llvm/IR/PassManager.h"

class PathAnalysis {
  public:
    typedef bool Result;
    static llvm::StringRef name() { return "PathAnalysis"; }
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
    static void *ID() { return static_cast<void *>(&PassID); }

  private:
    static char PassID;
};

#endif // PATHANALYSIS_H
