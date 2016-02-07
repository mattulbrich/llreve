#include "InlinePass.h"
#include "Helper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/CodeGen/IntrinsicLowering.h"

llvm::PreservedAnalyses InlinePass::run(llvm::Function &Fun,
                                        llvm::FunctionAnalysisManager */*unused*/) {
    std::vector<llvm::Instruction*> ToDelete;
    std::vector<llvm::CallInst*> Inline;
    for (auto &BB : Fun) {
        for (auto &Instr : BB) {
            if (auto Annotation = llvm::dyn_cast<llvm::CallInst>(&Instr)) {
                auto Fun = Annotation->getCalledFunction();
                if (Fun && Fun->isIntrinsic()) {
                    if (Fun->getIntrinsicID() == llvm::Intrinsic::annotation) {
                        if (auto PtrToInt = llvm::dyn_cast<llvm::PtrToIntInst>(
                                Annotation->getOperand(0))) {
                            if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(
                                    PtrToInt->getOperand(0))) {
                                for (auto User : Annotation->users()) {
                                    User->replaceUsesOfWith(Annotation,
                                                            PtrToInt);
                                }
                                Inline.push_back(CallInst);
                                ToDelete.push_back(Annotation);
                            }
                        }
                    }
                }
            }
        }
    }
    for (auto Instr : ToDelete) {
        Instr->eraseFromParent();
    }
    for (auto Instr : Inline) {
        llvm::InlineFunctionInfo InlineInfo;
        llvm::InlineFunction(Instr,InlineInfo);
    }
    return llvm::PreservedAnalyses::none();
}
