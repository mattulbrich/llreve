#include "RemoveMarkPass.h"

llvm::PreservedAnalyses RemoveMarkPass::run(llvm::Function &Fun,
                                            llvm::FunctionAnalysisManager *AM) {
    auto MarkedBlocks =
        AM->getResult<MarkAnalysis>(Fun);
    std::vector<llvm::Instruction *> ToDelete;
    for (auto BBTuple : MarkedBlocks) {
        if (BBTuple.first >= 0) {
            auto BB = BBTuple.second;
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
    if (Replace == nullptr) {
        return;
    }
    for (auto &Use : BinOp->uses()) {
        if (auto Used = llvm::dyn_cast<llvm::User>(Use.getUser())) {
            Used->replaceUsesOfWith(BinOp, Replace);
        }
    }
    BinOp->eraseFromParent();

    // try to remove the zext and all uses of it
    auto ZExt = llvm::dyn_cast<llvm::ZExtInst>(Replace);
    if (ZExt == nullptr) {
        return;
    }
    for (auto User : ZExt->users()) {
        if (auto UserInstr = llvm::dyn_cast<llvm::Instruction>(User)) {
            for (auto &Use__ : User->uses()) {
                if (auto Used__ = llvm::dyn_cast<llvm::User>(Use__.getUser())) {
                    Used__->replaceUsesOfWith(User, ZExt->getOperand(0));
                }
            }
            UserInstr->eraseFromParent();
        }
    }
    ZExt->eraseFromParent();
}
