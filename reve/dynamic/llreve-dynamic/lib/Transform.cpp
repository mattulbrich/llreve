#include "Transform.h"

#include <queue>

#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using std::vector;
using std::set;
using std::queue;

using llvm::BasicBlock;
using llvm::BranchInst;

set<BasicBlock *> blocksInLoop(llvm::BasicBlock *markedBlock,
                               const BidirBlockMarkMap &marks) {
    set<BasicBlock *> blocks;
    blocks.insert(markedBlock);
    queue<BasicBlock *> workingQueue;
    for (auto succ : successors(markedBlock)) {
        workingQueue.push(succ);
    }
    while (!workingQueue.empty()) {
        BasicBlock *cur = workingQueue.front();
        workingQueue.pop();
        if (blocks.count(cur) == 0 && marks.BlockToMarksMap.count(cur) == 0) {
            blocks.insert(cur);
            for (auto succ : successors(cur)) {
                workingQueue.push(succ);
            }
        }
    }
    return blocks;
}

BasicBlock *createUniqueBackedge(BasicBlock *markedBlock, BasicBlock *preHeader,
                                 const vector<BasicBlock *> &backedgeBlocks,
                                 llvm::Function &f) {
    BasicBlock *backEdge = BasicBlock::Create(
        markedBlock->getContext(), markedBlock->getName() + ".backedge", &f);
    BranchInst *beTerminator = BranchInst::Create(markedBlock, backEdge);

    llvm::Function::iterator insertPos = ++backedgeBlocks.back()->getIterator();
    f.getBasicBlockList().splice(insertPos, f.getBasicBlockList(), backEdge);

    // Now that the block has been inserted into the function, create PHI nodes
    // in
    // the backedge block which correspond to any PHI nodes in the header block.
    for (BasicBlock::iterator I = markedBlock->begin();
         llvm::isa<llvm::PHINode>(I); ++I) {
        llvm::PHINode *PN = llvm::cast<llvm::PHINode>(I);
        llvm::PHINode *NewPN = llvm::PHINode::Create(
            PN->getType(), static_cast<unsigned>(backedgeBlocks.size()),
            PN->getName() + ".be", beTerminator);

        // Loop over the PHI node, moving all entries except the one for the
        // preheader over to the new PHI node.
        unsigned PreheaderIdx = ~0U;
        bool HasUniqueIncomingValue = true;
        llvm::Value *UniqueValue = nullptr;
        for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
            BasicBlock *IBB = PN->getIncomingBlock(i);
            llvm::Value *IV = PN->getIncomingValue(i);
            if (IBB == preHeader) {
                PreheaderIdx = i;
            } else {
                NewPN->addIncoming(IV, IBB);
                if (HasUniqueIncomingValue) {
                    if (!UniqueValue)
                        UniqueValue = IV;
                    else if (UniqueValue != IV)
                        HasUniqueIncomingValue = false;
                }
            }
        }

        // Delete all of the incoming values from the old PN except the
        // preheader's
        assert(PreheaderIdx != ~0U && "PHI has no preheader entry??");
        if (PreheaderIdx != 0) {
            PN->setIncomingValue(0, PN->getIncomingValue(PreheaderIdx));
            PN->setIncomingBlock(0, PN->getIncomingBlock(PreheaderIdx));
        }
        // Nuke all entries except the zero'th.
        for (unsigned i = 0, e = PN->getNumIncomingValues() - 1; i != e; ++i)
            PN->removeIncomingValue(e - i, false);

        // Finally, add the newly constructed PHI node as the entry for the
        // BEBlock.
        PN->addIncoming(NewPN, backEdge);

        // As an optimization, if all incoming values in the new PhiNode (which
        // is a
        // subset of the incoming values of the old PHI node) have the same
        // value,
        // eliminate the PHI Node.
        if (HasUniqueIncomingValue) {
            NewPN->replaceAllUsesWith(UniqueValue);
            backEdge->getInstList().erase(NewPN);
        }
    }

    // Now that all of the PHI nodes have been inserted and adjusted, modify the
    // backedge blocks to just to the BEBlock instead of the header.
    for (unsigned i = 0, e = static_cast<unsigned>(backedgeBlocks.size());
         i != e; ++i) {
        llvm::TerminatorInst *TI = backedgeBlocks[i]->getTerminator();
        for (unsigned Op = 0, e = static_cast<unsigned>(TI->getNumSuccessors());
             Op != e; ++Op)
            if (TI->getSuccessor(Op) == markedBlock)
                TI->setSuccessor(Op, backEdge);
    }
    return backEdge;
}

llvm::BasicBlock *
createPreheader(llvm::BasicBlock *markedBlock,
                const std::vector<llvm::BasicBlock *> &outsideBlocks) {
    BasicBlock *preHeader =
        SplitBlockPredecessors(markedBlock, outsideBlocks, ".preheader");
    return preHeader;
}
