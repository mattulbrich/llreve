/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Unroll.h"

#include <iostream>
#include <queue>
#include <set>

#include "MonoPair.h"
#include "llreve/dynamic/Transform.h"

#include "llvm/Analysis/LoopIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"
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

void unrollAtMark(llvm::Function &f, Mark mark, const BidirBlockMarkMap &marks,
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
