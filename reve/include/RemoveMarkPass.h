#ifndef REMOVEMARKPASS_H
#define REMOVEMARKPASS_H

#include "MarkAnalysis.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class RemoveMarkPass {
 public:
    static llvm::StringRef name() {
        return "RemoveMarkPass";
    }
    llvm::PreservedAnalyses run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
};

void removeAnd(llvm::Instruction *Instr, llvm::BinaryOperator *BinOp);

#endif // REMOVEMARKPASS_H
