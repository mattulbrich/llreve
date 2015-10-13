#include "CFGPrinter.h"

#include "llvm/IR/PassManager.h"

llvm::PreservedAnalyses CFGViewerPass::run(llvm::Function &F,
                                           llvm::FunctionAnalysisManager *) {
    F.viewCFG();
    return llvm::PreservedAnalyses::all();
}
