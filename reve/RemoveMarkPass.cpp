#include "RemoveMarkPass.h"

llvm::PreservedAnalyses RemoveMarkPass::run(llvm::Function &Fun,
                                            llvm::FunctionAnalysisManager *AM) {
    std::map<llvm::BasicBlock *, int> MarkedBlocks =
        AM->getResult<MarkAnalysis>(Fun);
    std::vector<llvm::Instruction *> ToDelete;
    for (auto BBTuple : MarkedBlocks) {
        if (BBTuple.second >= 0) {
            auto BB = BBTuple.first;
            for (auto &Inst : *BB) {
                if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                    ToDelete.push_back(CallInst);
                }
            }
        }
    }
    for (auto Instr : ToDelete) {
        for (auto &Use : Instr->uses()) {
            if (auto Used = llvm::dyn_cast<llvm::Instruction>(Use.getUser())) {
                // handle and
                if (auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(Used)) {
                    if (BinOp->getOpcode() == llvm::Instruction::And) {
                        removeAnd(Instr, BinOp);
                    }
                }
            }
        }
        // kill the call instruction
        Instr->eraseFromParent();
    }
    return llvm::PreservedAnalyses::all();
}

void removeAnd(llvm::Instruction *Instr, llvm::BinaryOperator *BinOp) {
    llvm::Value *ReplaceVal = nullptr;
    // find non dummy operand
    if (Instr == BinOp->getOperand(0)) {
        ReplaceVal = BinOp->getOperand(1);
    } else if (Instr == BinOp->getOperand(1)) {
        ReplaceVal = BinOp->getOperand(0);
    }

    assert(ReplaceVal);

    // replace all uses of and with the operand
    auto Replace = llvm::dyn_cast<llvm::User>(ReplaceVal);
    if (!Replace) {
        return;
    }
    for (auto &Use_ : BinOp->uses()) {
        if (auto Used_ = llvm::dyn_cast<llvm::User>(Use_.getUser())) {
            Used_->replaceUsesOfWith(BinOp, Replace);
        }
    }
    BinOp->eraseFromParent();

    // try to remove the zext and all uses of it
    auto ZExt = llvm::dyn_cast<llvm::ZExtInst>(Replace);
    if (!ZExt) {
        return;
    }
    for (auto &Use_ : ZExt->uses()) {
        if (auto Used_ = llvm::dyn_cast<llvm::Instruction>(Use_.getUser())) {
            for (auto &Use__ : Used_->uses()) {
                if (auto Used__ = llvm::dyn_cast<llvm::User>(Use__.getUser())) {
                    Used__->replaceUsesOfWith(Used_, ZExt->getOperand(0));
                }
            }
            Used_->eraseFromParent();
        }
    }
    ZExt->eraseFromParent();
}
