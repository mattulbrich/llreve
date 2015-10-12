#include "llvm/IR/PassManager.h"

class CFGViewerPass {
  public:
    auto run(llvm::Function &F, llvm::FunctionAnalysisManager *AM)
        -> llvm::PreservedAnalyses;
    static auto name() -> llvm::StringRef { return "CFGViewerPass"; }
};
