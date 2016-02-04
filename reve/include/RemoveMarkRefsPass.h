#pragma once

#include "MarkAnalysis.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class RemoveMarkRefsPass {
 public:
    static llvm::StringRef name() {
        return "RemoveMarkRefsPass";
    }
    llvm::PreservedAnalyses run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
};

void removeAnd(const llvm::Instruction *Instr, llvm::BinaryOperator *BinOp);
