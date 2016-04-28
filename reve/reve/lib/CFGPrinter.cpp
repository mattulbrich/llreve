#include "CFGPrinter.h"

#include "llvm/IR/Function.h"

bool CFGViewerPass::runOnFunction(llvm::Function &F) {
    F.viewCFG();
    return false;
}

void CFGViewerPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
}

char CFGViewerPass::ID = 0;
static llvm::RegisterPass<CFGViewerPass>
    RegisterMarkAnalysis("cfgviewerpass", "View CFG", true, true);
