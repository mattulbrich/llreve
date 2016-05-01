#pragma once

#include "MarkAnalysis.h"

#include "llvm/Analysis/LoopInfo.h"

void unrollAtMark(llvm::Function &f, int mark, const BidirBlockMarkMap &marks,
                  llvm::LoopInfo &loopInfo, llvm::DominatorTree &dt);

std::set<llvm::BasicBlock *> blocksInLoop(llvm::BasicBlock *start,
                                          const BidirBlockMarkMap &marks);

llvm::BasicBlock *
createUniqueBackedge(llvm::BasicBlock *markedBlock, llvm::BasicBlock *preHeader,
                     const std::vector<llvm::BasicBlock *> &backedgeBlocks,
                     llvm::Function &f);

llvm::BasicBlock *
createPreheader(llvm::BasicBlock *markedBlock,
                const std::vector<llvm::BasicBlock *> &outsideBlocks);
class UnrollPass : public llvm::FunctionPass {
  public:
    static char ID;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    bool runOnFunction(llvm::Function &Fun) override;
    UnrollPass() : llvm::FunctionPass(ID) {}
};
