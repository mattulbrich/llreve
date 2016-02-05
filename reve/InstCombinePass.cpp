#include "InstCombine.h"
#include "Helper.h"
#include "llvm/IR/Constants.h"

llvm::PreservedAnalyses
InstCombinePass::run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM) {
    for (auto &BB : Fun) {
        for (auto &Instr : BB) {
            // Casting a i1 to an i32 and then comparing to 0 is a noop
            if (auto ICmpInst = llvm::dyn_cast<llvm::ICmpInst>(&Instr)) {
                if (ICmpInst->getPredicate() ==
                    llvm::CmpInst::Predicate::ICMP_NE) {
                    // Swap constant to the right
                    if (auto Const = llvm::dyn_cast<llvm::ConstantInt>(
                            ICmpInst->getOperand(0))) {
                        if (Const->isZero()) {
                            ICmpInst->swapOperands();
                        }
                    }
                    if (auto ZExt = llvm::dyn_cast<llvm::ZExtInst>(
                            ICmpInst->getOperand(0))) {
                        if (ZExt->getOperand(0)->getType()->isIntegerTy(1)) {
                            auto Op = ZExt->getOperand(0);
                            for (auto User : ICmpInst->users()) {
                                User->replaceUsesOfWith(ICmpInst, Op);
                            }
                        }
                    }
                }
            }
        }
    }
    return llvm::PreservedAnalyses::all();
}
