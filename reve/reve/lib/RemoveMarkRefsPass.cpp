/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "RemoveMarkRefsPass.h"

#include "Helper.h"
#include "PathAnalysis.h"
#include "llvm/IR/Constants.h"

bool RemoveMarkRefsPass::runOnFunction(llvm::Function & /*unused*/) {
    auto BidirMarkBlockMap = getAnalysis<MarkAnalysis>().getBlockMarkMap();
    std::set<llvm::Instruction *> ToDelete;
    for (auto BBTuple : BidirMarkBlockMap.MarkToBlocksMap) {
        // no need to remove anything in exit and entry nodes
        if (BBTuple.first >= Mark(0)) {
            for (auto BB : BBTuple.second) {
                for (auto &Inst : *BB) {
                    if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                        if ((CallInst->getCalledFunction() != nullptr) &&
                            (CallInst->getCalledFunction()->getName() ==
                                 "__mark" ||
                             CallInst->getCalledFunction()->getName() ==
                                 "__splitmark")) {
                            ToDelete.insert(CallInst);
                        }
                    }
                }
            }
        }
    }
    for (auto Instr : ToDelete) {
        // Store the users to prevent modifications during the loop causing a
        // segfault
        std::vector<llvm::User *> Users;
        Users.insert(Users.end(), Instr->users().begin(), Instr->users().end());
        for (auto User : Users) {
            if (auto UserInstr = llvm::dyn_cast<llvm::Instruction>(User)) {
                // handle and
                if (auto BinOp =
                        llvm::dyn_cast<llvm::BinaryOperator>(UserInstr)) {
                    if (BinOp->getOpcode() == llvm::Instruction::And) {
                        removeAnd(Instr, BinOp);
                    }
                } else {
                    llvm::Instruction *ExtInst;
                    if ((ExtInst = llvm::dyn_cast<llvm::ZExtInst>(UserInstr)) ||
                        (ExtInst = llvm::dyn_cast<llvm::SExtInst>(UserInstr))) {
                        std::vector<llvm::User *> ExtUsers;
                        ExtUsers.insert(ExtUsers.end(),
                                        ExtInst->users().begin(),
                                        ExtInst->users().end());
                        for (auto User : ExtUsers) {
                            if (User != ExtInst) {
                                if (auto BinOp =
                                        llvm::dyn_cast<llvm::BinaryOperator>(
                                            User)) {
                                    if (BinOp->getOpcode() ==
                                        llvm::Instruction::And) {
                                        removeAnd(ExtInst, BinOp);
                                    }
                                } else {
                                    logErrorData("Unexpected use of extended "
                                                 "mark instruction\n",
                                                 *User);
                                }
                            }
                        }
                        ExtInst->eraseFromParent();
                        continue;
                    } else if (auto Cmp =
                                   llvm::dyn_cast<llvm::ICmpInst>(User)) {
                        if (Cmp->getPredicate() ==
                            llvm::CmpInst::Predicate::ICMP_NE) {
                            if (auto Const = llvm::dyn_cast<llvm::ConstantInt>(
                                    Cmp->getOperand(1))) {
                                if (Const->getValue().getSExtValue() == 0) {
                                    Cmp->setOperand(0,
                                                    llvm::ConstantInt::get(
                                                        Const->getType(), 1));
                                    continue;
                                }
                            }
                        }
                    }
                    logErrorData("Unexpected use of mark instruction\n",
                                 *UserInstr);
                }
            }
        }
        // kill the call instruction
        // Instr->eraseFromParent();
    }
    return true;
    // return llvm::PreservedAnalyses::all();
}

void removeAnd(const llvm::Instruction *Instr, llvm::BinaryOperator *BinOp) {
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

    for (auto Used : BinOp->users()) {
        Used->replaceUsesOfWith(BinOp, Replace);
    }
    BinOp->eraseFromParent();
}

char RemoveMarkRefsPass::ID = 0;

void RemoveMarkRefsPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.addPreserved<MarkAnalysis>();
    AU.addPreserved<PathAnalysis>();
    AU.addRequired<MarkAnalysis>();
    AU.setPreservesCFG();
}

static llvm::RegisterPass<RemoveMarkRefsPass>
    RegisterMarkAnalysis("remove-mark-refs", "Remove mark references", false,
                         false);
