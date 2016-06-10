#pragma once

#include "DependencyGraphPasses.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include "core/Criterion.h"

class SyntacticSlicePass : public llvm::FunctionPass {

	public:

	static char ID;

	SyntacticSlicePass(CriterionPtr criterionPtr = Criterion::getReturnValueCriterion()) : llvm::FunctionPass(ID), criterion(criterionPtr) {}

	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;

	virtual bool runOnFunction(llvm::Function &func) override;

private:
	CriterionPtr criterion;
};
