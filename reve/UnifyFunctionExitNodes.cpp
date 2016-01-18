#include "UnifyFunctionExitNodes.h"

#include "llvm/IR/Instructions.h"

char UnifyFunctionExitNodes::PassID;

using llvm::BasicBlock;
using llvm::Function;

BasicBlock *
UnifyFunctionExitNodes::run(llvm::Function &Fun,
                            llvm::FunctionAnalysisManager * /*unused*/) {
    // Loop over all of the blocks in a function, tracking all of the blocks
    // that
    // return.
    //
    BasicBlock *UnreachableBlock = nullptr;
    BasicBlock *ReturnBlock = nullptr;
    std::vector<BasicBlock *> ReturningBlocks;
    std::vector<BasicBlock *> UnreachableBlocks;
    for (Function::iterator I = Fun.begin(), E = Fun.end(); I != E; ++I) {
        if (llvm::isa<llvm::ReturnInst>(I->getTerminator())) {
            ReturningBlocks.push_back(I);
        } else if (llvm::isa<llvm::UnreachableInst>(I->getTerminator())) {
            UnreachableBlocks.push_back(I);
        }
    }

    // Then unreachable blocks.
    if (UnreachableBlocks.empty()) {
        UnreachableBlock = nullptr;
    } else if (UnreachableBlocks.size() == 1) {
        UnreachableBlock = UnreachableBlocks.front();
    } else {
        UnreachableBlock = BasicBlock::Create(Fun.getContext(),
                                              "UnifiedUnreachableBlock", &Fun);
        new llvm::UnreachableInst(Fun.getContext(), UnreachableBlock);

        for (auto BB : UnreachableBlocks) {
            BB->getInstList().pop_back(); // Remove the unreachable inst.
            llvm::BranchInst::Create(UnreachableBlock, BB);
        }
    }

    // Now handle return blocks.
    if (ReturningBlocks.empty()) {
        ReturnBlock = nullptr;
        return ReturnBlock; // No blocks return
    }
    if (ReturningBlocks.size() == 1) {
        ReturnBlock =
            ReturningBlocks.front(); // Already has a single return block
        return ReturnBlock;
    }

    // Otherwise, we need to insert a new basic block into the function, add a
    // PHI
    // nodes (if the function returns values), and convert all of the return
    // instructions into unconditional branches.
    //
    BasicBlock *NewRetBlock =
        BasicBlock::Create(Fun.getContext(), "UnifiedReturnBlock", &Fun);

    llvm::PHINode *PN = nullptr;
    if (Fun.getReturnType()->isVoidTy()) {
        llvm::ReturnInst::Create(Fun.getContext(), nullptr, NewRetBlock);
    } else {
        // If the function doesn't return void... add a PHI node to the block...
        PN = llvm::PHINode::Create(
            Fun.getReturnType(),
            static_cast<unsigned int>(ReturningBlocks.size()), "UnifiedRetVal");
        NewRetBlock->getInstList().push_back(PN);
        llvm::ReturnInst::Create(Fun.getContext(), PN, NewRetBlock);
    }

    // Loop over all of the blocks, replacing the return instruction with an
    // unconditional branch.
    //
    for (auto BB : ReturningBlocks) {
        // Add an incoming element to the PHI node for every return instruction
        // that
        // is merging into this new block...
        if (PN != nullptr) {
            PN->addIncoming(BB->getTerminator()->getOperand(0), BB);
        }

        BB->getInstList().pop_back(); // Remove the return insn
        llvm::BranchInst::Create(NewRetBlock, BB);
    }
    ReturnBlock = NewRetBlock;
    return ReturnBlock;
}
