#pragma once

#include "MarkAnalysis.h"

std::set<llvm::BasicBlock *> blocksInLoop(llvm::BasicBlock *start,
                                          const BidirBlockMarkMap &marks);
llvm::BasicBlock *
createUniqueBackedge(llvm::BasicBlock *markedBlock, llvm::BasicBlock *preHeader,
                     const std::vector<llvm::BasicBlock *> &backedgeBlocks,
                     llvm::Function &f);
llvm::BasicBlock *
createPreheader(llvm::BasicBlock *markedBlock,
                const std::vector<llvm::BasicBlock *> &outsideBlocks);
