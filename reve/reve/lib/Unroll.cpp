#include "Unroll.h"

#include <iostream>
#include <queue>
#include <set>

#include "llvm/Analysis/LoopIterator.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using std::set;
using std::queue;
using std::vector;

using llvm::BasicBlock;
using llvm::ValueToValueMapTy;
using llvm::BranchInst;

void unrollFactor(llvm::Function &f, int mark, const BidirBlockMarkMap &marks,
                  size_t factor) {
    if (factor <= 1) {
        return;
    }
    assert(marks.MarkToBlocksMap.at(mark).size() == 1);
    BasicBlock *markedBlock = *marks.MarkToBlocksMap.at(mark).begin();
    set<BasicBlock *> loopBlocks = blocksInLoop(markedBlock, marks);

    vector<BasicBlock *> outsideBlocks;
    vector<BasicBlock *> backedgeBlocks;
    for (auto pred : predecessors(markedBlock)) {
        if (loopBlocks.count(pred) == 0) {
            outsideBlocks.push_back(pred);
        } else {
            backedgeBlocks.push_back(pred);
        }
    }

    BasicBlock *preHeader = createPreheader(markedBlock, outsideBlocks);
    BasicBlock *backEdge =
        createUniqueBackedge(markedBlock, preHeader, backedgeBlocks, f);
    loopBlocks.insert(backEdge);

    vector<BasicBlock *> newBlocks;
    vector<BasicBlock *> lastLoop;
    lastLoop.insert(lastLoop.begin(), loopBlocks.begin(), loopBlocks.end());
    ValueToValueMapTy vmap;
    for (size_t i = 1; i < factor; ++i) {
        vector<BasicBlock *> currentLoop;
        for (auto bb : lastLoop) {
            BasicBlock *newBB =
                CloneBasicBlock(bb, vmap, "." + std::to_string(i + 1), &f);
            currentLoop.push_back(newBB);
            newBlocks.push_back(newBB);
            vmap[bb] = newBB;
        }
        for (auto bb : currentLoop) {
            for (auto &i : *bb) {
                RemapInstruction(&i, vmap);
            }
        }
        lastLoop = currentLoop;
    }
    // f.viewCFG();
    // Connect the end of the last cloned loop back to the top
    BasicBlock *lastHeader = markedBlock;
    BasicBlock *lastBackEdge = backEdge;
    for (size_t i = 0; i < factor; ++i) {
        if (vmap[lastHeader]) {
            lastBackEdge->getTerminator()->setSuccessor(
                0, llvm::cast<llvm::BasicBlock>(vmap[lastHeader]));
        } else {
            lastBackEdge->getTerminator()->setSuccessor(
                0, llvm::cast<llvm::BasicBlock>(markedBlock));
            break;
        }
        lastBackEdge = llvm::cast<llvm::BasicBlock>(vmap[lastBackEdge]);
        lastHeader = llvm::cast<llvm::BasicBlock>(vmap[lastHeader]);
    }

    // Remap phis
    for (auto &instr : *markedBlock) {
        auto phi = llvm::dyn_cast<llvm::PHINode>(&instr);
        if (phi == nullptr) {
            break;
        }
        auto val = phi->getIncomingValueForBlock(backEdge);
        // Find the corresponding value in the last header
        for (size_t i = 0; i < factor - 1; ++i) {
            val = vmap[val];
        }
        phi->addIncoming(val, lastBackEdge);

        auto oldPhi = phi;
        auto mappedPhi = llvm::dyn_cast<llvm::PHINode>(vmap[phi]);
        auto lastEdge = backEdge;
        auto oldPhiVal = oldPhi->getIncomingValueForBlock(backEdge);

        phi->removeIncomingValue(backEdge);
        for (size_t i = 0; i < factor - 1; ++i) {
            mappedPhi->addIncoming(oldPhiVal, lastEdge);
            if (vmap[lastEdge]) {
                oldPhiVal = mappedPhi->getIncomingValueForBlock(
                    llvm::cast<llvm::BasicBlock>(vmap[lastEdge]));
            }
            mappedPhi->removeIncomingValue(preHeader);
            // Remove the value from the old backedge, addIncoming is guaranteed
            // to add to the end so we can just reomve the first value
            unsigned idx = 0;
            mappedPhi->removeIncomingValue(idx);
            if (!vmap[mappedPhi]) {
                break;
            }
            oldPhi = mappedPhi;
            mappedPhi = llvm::dyn_cast<llvm::PHINode>(vmap[mappedPhi]);
            lastEdge = llvm::dyn_cast<llvm::BasicBlock>(vmap[lastEdge]);
        }
    }

    f.getBasicBlockList().splice(backEdge->getIterator(), f.getBasicBlockList(),
                                 newBlocks[0]->getIterator(), f.end());

    set<BasicBlock *> originalLoopBlocks = loopBlocks;
    loopBlocks.insert(newBlocks.begin(), newBlocks.end());
    set<llvm::Instruction *> loopInstructions;
    for (auto bb : loopBlocks) {
        for (auto &instr : *bb) {
            loopInstructions.insert(&instr);
        }
    }

    // Merge uses outside the loop
    for (auto bb : originalLoopBlocks) {
        for (auto &instr : *bb) {
            if (instr.getType()->isVoidTy() || !vmap[&instr])
                continue;
            llvm::SSAUpdater ssaUpdate;
            ssaUpdate.Initialize(instr.getType(), instr.getName());
            ssaUpdate.AddAvailableValue(instr.getParent(), &instr);
            // Add all mappings
            auto mappedInstr = llvm::cast<llvm::Instruction>(vmap[&instr]);
            while (true) {
                ssaUpdate.AddAvailableValue(mappedInstr->getParent(),
                                            mappedInstr);
                if (!vmap[mappedInstr]) {
                    break;
                }
                mappedInstr = llvm::cast<llvm::Instruction>(vmap[mappedInstr]);
            }
            vector<llvm::Use *> usesOutsideLoop;
            for (auto &use : instr.uses()) {
                llvm::Instruction *user =
                    llvm::dyn_cast<llvm::Instruction>(use.getUser());
                if (!user) {
                    continue;
                }
                if (loopInstructions.count(user) == 0) {
                    // Find uses outside the loop
                    usesOutsideLoop.push_back(&use);
                }
            }
            for (auto use : usesOutsideLoop) {
                ssaUpdate.RewriteUse(*use);
            }
        }
    }
}

void unrollAtMark(llvm::Function &f, int mark, const BidirBlockMarkMap &marks,
                  llvm::LoopInfo &loopInfo, llvm::DominatorTree &dt) {
    assert(marks.MarkToBlocksMap.at(mark).size() ==
           1); // For now we assume that there is only block per mark
    BasicBlock *markedBlock = *marks.MarkToBlocksMap.at(mark).begin();
    set<BasicBlock *> loopBlocks = blocksInLoop(markedBlock, marks);
    set<llvm::Instruction *> loopInstructions;
    for (auto bb : loopBlocks) {
        for (llvm::Instruction &i : *bb) {
            loopInstructions.insert(&i);
        }
    }

    // Create a preheader
    vector<BasicBlock *> outsideBlocks;
    vector<BasicBlock *> backedgeBlocks;
    for (auto pred : predecessors(markedBlock)) {
        if (loopBlocks.count(pred) == 0) {
            outsideBlocks.push_back(pred);
        } else {
            backedgeBlocks.push_back(pred);
        }
    }

    BasicBlock *preHeader = createPreheader(markedBlock, outsideBlocks);
    BasicBlock *backEdge =
        createUniqueBackedge(markedBlock, preHeader, backedgeBlocks, f);
    loopBlocks.insert(backEdge);
    for (auto &i : *backEdge) {
        loopInstructions.insert(&i);
    }

    BasicBlock *prologPreHeader = SplitEdge(preHeader, markedBlock);
    prologPreHeader->setName(markedBlock->getName() + ".prol.preheader");
    BasicBlock *prologExit =
        SplitBlock(prologPreHeader, prologPreHeader->getTerminator());
    prologExit->setName(markedBlock->getName() + ".prol.loopexit");
    BasicBlock *newPreHeader =
        SplitBlock(prologExit, prologExit->getTerminator());
    newPreHeader->setName(preHeader->getName() + ".new");

    BasicBlock *insertBot = prologExit;
    BasicBlock *insertTop = prologPreHeader;
    vector<BasicBlock *> newBlocks;
    ValueToValueMapTy vmap;

    for (auto bb : loopBlocks) {
        BasicBlock *newBB = CloneBasicBlock(bb, vmap, ".prolog", &f);
        newBlocks.push_back(newBB);
        vmap[bb] = newBB;

        if (bb == markedBlock) {
            // Connect the prolog preheader to the unrolled loop
            insertTop->getTerminator()->setSuccessor(0, newBB);
        }

        if (bb == backEdge) {
            // Jump to insertBot instead of looping
            vmap.erase(bb->getTerminator());
            BranchInst *latchBr =
                llvm::cast<BranchInst>(newBB->getTerminator());
            llvm::IRBuilder<> builder(latchBr);
            builder.CreateBr(insertBot);
            latchBr->eraseFromParent();
        }
    }

    // Change the incoming values to the ones defined in the preheader or cloned
    // loop
    for (auto I = markedBlock->begin(); llvm::isa<llvm::PHINode>(I); ++I) {
        llvm::PHINode *newPHI = llvm::cast<llvm::PHINode>(vmap[&*I]);
        vector<BasicBlock *> toRemove;
        for (auto bb = newPHI->block_begin(); bb != newPHI->block_end(); ++bb) {
            if (*bb != newPreHeader) {
                toRemove.push_back(*bb);
            }
        }
        for (auto bb : toRemove) {
            newPHI->removeIncomingValue(bb);
        }
    }
    vmap[newPreHeader] = prologPreHeader;

    f.getBasicBlockList().splice(insertBot->getIterator(),
                                 f.getBasicBlockList(),
                                 newBlocks[0]->getIterator(), f.end());

    // Rewrite the cloned instruction operands to use the values created when
    // the clone is created
    for (auto bb : newBlocks) {
        for (auto &i : *bb) {
            RemapInstruction(&i, vmap, llvm::RF_NoModuleLevelChanges);
        }
    }

    // Connect the prolog code to the original loop and update the PHI functions
    BasicBlock *latch = backEdge;
    assert(latch);
    BasicBlock *prologLatch = llvm::cast<BasicBlock>(vmap[latch]);

    // Create a PHI node for each outgoing value from the original loop
    // The new PHI node is inserted in the prolog end basic block.
    // The new PHI node value is added as an operand of a PHI node in either the
    // loop header or the loop exit block
    for (auto succ : successors(latch)) {
        for (auto &bbi : *succ) {
            llvm::PHINode *pn = llvm::dyn_cast<llvm::PHINode>(&bbi);
            if (!pn) {
                // Exit when we passed all PHI nodes
                break;
            }

            // phi node in successor of latch
            llvm::PHINode *newPN =
                llvm::PHINode::Create(pn->getType(), 2, pn->getName() + ".unr",
                                      prologExit->getFirstNonPHI());
            if (loopInstructions.count(pn) > 0) {
                // TODO Do I really need this?
                // newPN->addIncoming(pn->getIncomingValueForBlock(newPreHeader),
                //                    preHeader);
            } else {
                newPN->addIncoming(llvm::UndefValue::get(pn->getType()),
                                   preHeader);
            }

            llvm::Value *v = pn->getIncomingValueForBlock(latch);
            if (llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(v)) {
                // If it was not a constant find the mapping
                if (loopInstructions.count(I) > 0) {
                    v = vmap.lookup(I);
                }
            }

            newPN->addIncoming(v, prologLatch);

            if (loopInstructions.count(pn) > 0) {
                pn->setIncomingValue(
                    static_cast<uint32_t>(pn->getBasicBlockIndex(newPreHeader)),
                    newPN);
            } else {
                pn->addIncoming(newPN, prologExit);
            }
        }
    }

    std::map<BasicBlock *, BasicBlock *> exitEdges;
    set<BasicBlock *> loopExitSet;

    for (auto bb : loopBlocks) {
        if (!vmap[bb]) {
            continue;
        }
        vector<BasicBlock *> edgeTargets;
        for (auto succ : successors(bb)) {
            if (loopBlocks.count(succ) == 0) {
                loopExitSet.insert(llvm::cast<llvm::BasicBlock>(vmap[bb]));
                edgeTargets.push_back(succ);
            }
        }
        // Split all edges that go outside of the loop
        for (auto target : edgeTargets) {
            BasicBlock *newBB = llvm::cast<llvm::BasicBlock>(vmap[bb]);
            exitEdges.insert(std::make_pair(newBB, SplitEdge(newBB, target)));
        }
    }
    for (auto edge : exitEdges) {
        edge.second->replaceAllUsesWith(markedBlock);
    }
    vector<BasicBlock *> loopExits;
    loopExits.insert(loopExits.begin(), loopExitSet.begin(), loopExitSet.end());

    BasicBlock *split = SplitBlock(markedBlock, markedBlock->getTerminator());
    loopBlocks.insert(split);
    for (auto &instr : *split) {
        loopInstructions.insert(&instr);
    }

    // Create a phi node with the index of the loop exit
    llvm::PHINode *exitIndex =
        llvm::PHINode::Create(llvm::Type::getInt32Ty(markedBlock->getContext()),
                              static_cast<uint32_t>(exitEdges.size()),
                              "exitIndex", &markedBlock->front());
    for (size_t i = 0; i < exitEdges.size(); ++i) {
        exitIndex->addIncoming(
            llvm::ConstantInt::get(exitIndex->getType(), i + 1),
            loopExits.at(i));
        exitIndex->setName("exitIndex$1_0");
    }
    exitIndex->addIncoming(llvm::ConstantInt::get(exitIndex->getType(), 0),
                           newPreHeader);
    exitIndex->addIncoming(llvm::ConstantInt::get(exitIndex->getType(), 0),
                           backEdge);

    // Now switch based on the phi node to jump to the correct block
    llvm::SwitchInst *switchExit =
        llvm::SwitchInst::Create(exitIndex, split, 0);
    llvm::ReplaceInstWithInst(markedBlock->getTerminator(), switchExit);
    for (size_t i = 0; i < loopExits.size(); ++i) {
        llvm::ConstantInt *c = llvm::ConstantInt::get(
            llvm::Type::getInt32Ty(markedBlock->getContext()), i + 1);
        switchExit->addCase(c, exitEdges.at(loopExits.at(i)));
    }

    // Set phi values for loopexits
    for (auto &instr : *markedBlock) {
        llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(&instr);
        if (!phi) {
            break;
        }
        if (!vmap[phi]) {
            continue;
        }
        for (auto exitBlock : loopExits) {
            phi->addIncoming(vmap[phi], exitBlock);
        }
    }

    // We cloned instructions so we need to merge their uses
    for (auto bb : loopBlocks) {
        for (auto &instr : *bb) {
            llvm::SSAUpdater ssaUpdate;
            if (instr.getType()->isVoidTy() || !vmap[&instr])
                continue;
            llvm::Instruction *otherInstr =
                llvm::cast<llvm::Instruction>(vmap[&instr]);
            ssaUpdate.Initialize(instr.getType(), instr.getName());
            ssaUpdate.AddAvailableValue(instr.getParent(), &instr);
            if (exitEdges.count(otherInstr->getParent()) == 0) {
                ssaUpdate.AddAvailableValue(
                    llvm::cast<llvm::Instruction>(vmap[&instr])->getParent(),
                    vmap[&instr]);
            } else {
                ssaUpdate.AddAvailableValue(
                    llvm::cast<llvm::Instruction>(vmap[&instr])->getParent(),
                    vmap[&instr]);
            }
            vector<llvm::Use *> usesOutsideLoop;
            for (auto &use : instr.uses()) {
                llvm::Instruction *user =
                    llvm::dyn_cast<llvm::Instruction>(use.getUser());
                if (!user) {
                    continue;
                }
                if (loopInstructions.count(user) == 0) {
                    // Find uses outside the loop
                    usesOutsideLoop.push_back(&use);
                }
            }
            for (auto use : usesOutsideLoop) {
                ssaUpdate.RewriteUse(*use);
            }
        }
    }
    // f.viewCFG();
}

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

void UnrollPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.addRequired<llvm::LoopInfoWrapperPass>();
    AU.addRequired<llvm::DominatorTreeWrapperPass>();
    AU.addRequired<MarkAnalysis>();
    AU.setPreservesCFG(); // This is a horrible lie but it helps keeping the
                          // mark analysis up2date
}

bool UnrollPass::runOnFunction(llvm::Function &f) {
    llvm::LoopInfo &li = getAnalysis<llvm::LoopInfoWrapperPass>().getLoopInfo();
    llvm::DominatorTree &dt =
        getAnalysis<llvm::DominatorTreeWrapperPass>().getDomTree();
    auto map = getAnalysis<MarkAnalysis>().getBlockMarkMap();
    unrollFactor(f, 42, map, 4);
    // unrollAtMark(f, 42, map, li, dt);
    return true;
}

char UnrollPass::ID = 0;

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
