#include "InlinePass.h"
#include "Helper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/Constants.h"
#include "llvm/CodeGen/IntrinsicLowering.h"

llvm::PreservedAnalyses
InlinePass::run(llvm::Function &fun,
                llvm::FunctionAnalysisManager * /*unused*/) {
    std::vector<llvm::Instruction *> toDelete;
    std::vector<llvm::CallInst *> toBeInlined;
    for (auto &bb : fun) {
        for (auto &instr : bb) {
            if (auto inlineCall = llvm::dyn_cast<llvm::CallInst>(&instr)) {
                auto fun = inlineCall->getCalledFunction();
                if (fun->getName() == "__inlineCall" ||
                    fun->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
                    if (auto callInst = llvm::dyn_cast<llvm::CallInst>(
                            inlineCall->getOperand(0))) {
                        for (auto user : inlineCall->users()) {
                            user->replaceUsesOfWith(inlineCall, callInst);
                        }
                        toDelete.push_back(inlineCall);
                        toBeInlined.push_back(callInst);
                    }
                }
            }
        }
    }

    for (auto instr : toDelete) {
        instr->eraseFromParent();
    }
    for (auto instr : toBeInlined) {
        llvm::InlineFunctionInfo InlineInfo;
        llvm::InlineFunction(instr, InlineInfo);
    }
    return llvm::PreservedAnalyses::none();
}
