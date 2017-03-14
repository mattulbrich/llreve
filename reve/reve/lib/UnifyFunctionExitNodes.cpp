#include "UnifyFunctionExitNodes.h"

#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

llvm::PreservedAnalyses
UnifyFunctionExitNodes::run(llvm::Function &F,
                            llvm::FunctionAnalysisManager &fam) {
    BasicBlock *UnreachableBlock;
    BasicBlock *ReturnBlock;
    // Loop over all of the blocks in a function, tracking all of the blocks
    // that
    // return.
    //
    std::vector<BasicBlock *> ReturningBlocks;
    std::vector<BasicBlock *> UnreachableBlocks;
    for (BasicBlock &I : F)
        if (isa<ReturnInst>(I.getTerminator()))
            ReturningBlocks.push_back(&I);
        else if (isa<UnreachableInst>(I.getTerminator()))
            UnreachableBlocks.push_back(&I);

    // Then unreachable blocks.
    if (UnreachableBlocks.empty()) {
        UnreachableBlock = nullptr;
    } else if (UnreachableBlocks.size() == 1) {
        UnreachableBlock = UnreachableBlocks.front();
    } else {
        UnreachableBlock =
            BasicBlock::Create(F.getContext(), "UnifiedUnreachableBlock", &F);
        new UnreachableInst(F.getContext(), UnreachableBlock);

        for (BasicBlock *BB : UnreachableBlocks) {
            BB->getInstList().pop_back(); // Remove the unreachable inst.
            BranchInst::Create(UnreachableBlock, BB);
        }
    }

    // Now handle return blocks.
    if (ReturningBlocks.empty()) {
        ReturnBlock = nullptr;
        return llvm::PreservedAnalyses::none(); // No blocks return
    } else if (ReturningBlocks.size() == 1) {
        ReturnBlock =
            ReturningBlocks.front(); // Already has a single return block
        return llvm::PreservedAnalyses::none();
    }

    // Otherwise, we need to insert a new basic block into the function, add a
    // PHI
    // nodes (if the function returns values), and convert all of the return
    // instructions into unconditional branches.
    //
    BasicBlock *NewRetBlock =
        BasicBlock::Create(F.getContext(), "UnifiedReturnBlock", &F);

    PHINode *PN = nullptr;
    if (F.getReturnType()->isVoidTy()) {
        ReturnInst::Create(F.getContext(), nullptr, NewRetBlock);
    } else {
        // If the function doesn't return void... add a PHI node to the block...
        PN = PHINode::Create(F.getReturnType(), ReturningBlocks.size(),
                             "UnifiedRetVal");
        NewRetBlock->getInstList().push_back(PN);
        ReturnInst::Create(F.getContext(), PN, NewRetBlock);
    }

    // Loop over all of the blocks, replacing the return instruction with an
    // unconditional branch.
    //
    for (BasicBlock *BB : ReturningBlocks) {
        // Add an incoming element to the PHI node for every return instruction
        // that
        // is merging into this new block...
        if (PN)
            PN->addIncoming(BB->getTerminator()->getOperand(0), BB);

        BB->getInstList().pop_back(); // Remove the return insn
        BranchInst::Create(NewRetBlock, BB);
    }
    return llvm::PreservedAnalyses::none();
}

llvm::AnalysisKey FunctionExitNodeAnalysis::Key;

ExitNode FunctionExitNodeAnalysis::run(llvm::Function &fun,
                                       llvm::FunctionAnalysisManager &am) {
    for (auto &bb : fun) {
        for (auto &inst : bb) {
            if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(&inst)) {
                return {&bb};
            }
        }
    }
    return {nullptr};
}
