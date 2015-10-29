#ifndef CFGPRINTER_H
#define CFGPRINTER_H

#include "MarkAnalysis.h"

class CFGViewerPass {
  public:
    auto run(llvm::Function &F, llvm::FunctionAnalysisManager *AM)
        -> llvm::PreservedAnalyses;
    static auto name() -> llvm::StringRef { return "CFGViewerPass"; }
};

#endif // CFGPRINTER_H
