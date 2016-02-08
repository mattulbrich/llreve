#include "SplitEntryBlockPass.h"

llvm::PreservedAnalyses
SplitEntryBlockPass::run(llvm::Function &Fun,
                         llvm::FunctionAnalysisManager * /*unused*/) {
    auto &Entry = Fun.getEntryBlock();
    Entry.splitBasicBlock(Entry.begin());
    return llvm::PreservedAnalyses::none();
}
