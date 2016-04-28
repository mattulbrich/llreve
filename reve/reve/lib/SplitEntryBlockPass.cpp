#include "SplitEntryBlockPass.h"

bool SplitEntryBlockPass::runOnFunction(llvm::Function &Fun) {
    auto &Entry = Fun.getEntryBlock();
    Entry.splitBasicBlock(Entry.begin());
    return true;
}

char SplitEntryBlockPass::ID = 0;
static llvm::RegisterPass<SplitEntryBlockPass>
    RegisterMarkAnalysis("split-entry-block", "Split Entry Block", false, false);
