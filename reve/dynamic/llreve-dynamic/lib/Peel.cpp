#include "Peel.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/SSAUpdater.h"

#include "MonoPair.h"
#include "Transform.h"

using std::set;
using std::vector;

using llvm::ValueToValueMapTy;
using llvm::BasicBlock;
using llvm::BranchInst;

void peelAtMark(llvm::Function &f, Mark mark, const BidirBlockMarkMap &marks,
                std::string prefix) {
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
            RemapInstruction(&i, vmap, llvm::RF_NoModuleLevelChanges |
                                           llvm::RF_IgnoreMissingLocals);
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

    std::map<BasicBlock *, MonoPair<BasicBlock *>> exitEdges;

    for (auto bb : loopBlocks) {
        if (!vmap[bb]) {
            continue;
        }
        vector<BasicBlock *> edgeTargets;
        for (auto succ : successors(bb)) {
            if (loopBlocks.count(succ) == 0) {
                edgeTargets.push_back(succ);
            }
        }
        // Split all edges that go outside of the loop
        for (auto target : edgeTargets) {
            BasicBlock *newBB = llvm::cast<llvm::BasicBlock>(vmap[bb]);
            // SplitEdge segfaults if the phi nodes in target are not valid
            // To make them valid at this point we need to add incoming values
            // for each early exit in the prolog
            for (auto &instr : *target) {
                llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(&instr);
                if (!phi) {
                    break;
                }
                // Find all incoming values for the target that come from inside
                // of the loop
                vector<BasicBlock *> toAdd;
                for (auto bbIt = phi->block_begin(); bbIt != phi->block_end();
                     ++bbIt) {
                    if (loopBlocks.count(*bbIt) == 1) {
                        toAdd.push_back(*bbIt);
                    }
                }
                // For each of these values add a new incoming value for the
                // original instructions in the prolog, at this point the
                // original instruction is not accessible but we redirect the
                // control flow via markedBlock so it is guaranteed to be
                // accessible when we are done
                for (auto bb : toAdd) {
                    llvm::Value *val = phi->getIncomingValueForBlock(bb);
                    if (vmap[val]) {
                        phi->addIncoming(val, newBB);
                    }
                }
            }
            // edgeBlock will later be changed to point to markedBlock
            BasicBlock *edgeBlock = SplitEdge(newBB, target);
            // markedBlock then jumps to split if it came from edgeBlock
            BasicBlock *split =
                SplitBlock(edgeBlock, edgeBlock->getTerminator());
            edgeBlock->getTerminator()->setSuccessor(0, markedBlock);
            exitEdges.insert(
                std::make_pair(newBB, makeMonoPair(edgeBlock, split)));
        }
    }

    // Split the original markedBlock since we want to use a switch here
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
    exitIndex->setName("exitIndex$" + prefix + "_" + mark.toString());
    {
        // For loop exit i (the numbering is arbitrary) we set exitIndex to i
        size_t i = 1;
        for (auto edge : exitEdges) {

            exitIndex->addIncoming(
                llvm::ConstantInt::get(exitIndex->getType(), i),
                edge.second.first);
            ++i;
        }
    }
    exitIndex->addIncoming(llvm::ConstantInt::get(exitIndex->getType(), 0),
                           newPreHeader);
    exitIndex->addIncoming(llvm::ConstantInt::get(exitIndex->getType(), 0),
                           backEdge);

    // Switch based on the value of exitIndex to jump to the correct block
    llvm::SwitchInst *switchExit =
        llvm::SwitchInst::Create(exitIndex, split, 0);
    llvm::ReplaceInstWithInst(markedBlock->getTerminator(), switchExit);
    {
        size_t i = 1;
        for (auto edge : exitEdges) {
            llvm::ConstantInt *c = llvm::ConstantInt::get(
                llvm::Type::getInt32Ty(markedBlock->getContext()), i);
            switchExit->addCase(c, edge.second.second);
            ++i;
        }
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
        for (auto edge : exitEdges) {
            phi->addIncoming(vmap[phi], edge.second.first);
        }
    }

    // We cloned instructions so we need to merge their uses outside of the loop
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
}
