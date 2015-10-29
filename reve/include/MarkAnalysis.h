#ifndef MARKANALYSIS_H
#define MARKANALYSIS_H

#include "Mem2Reg.h"

class MarkAnalysis {
  public:
    typedef std::map<int, llvm::BasicBlock *> Result;
    static llvm::StringRef name() { return "MarkAnalysis"; }
    static void *ID() { return static_cast<void *>(&PassID); }
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);

  private:
    static char PassID;
};

#endif // MARKANALYSIS_H
