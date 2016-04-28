#pragma once

#include "MarkAnalysis.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"

class RemoveMarkRefsPass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "RemoveMarkRefsPass"; }
    bool runOnFunction(llvm::Function &Fun) override;
    RemoveMarkRefsPass() : llvm::FunctionPass(ID) {}
    static char ID;
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
};

void removeAnd(const llvm::Instruction *Instr, llvm::BinaryOperator *BinOp);
