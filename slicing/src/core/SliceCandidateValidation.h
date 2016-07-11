#pragma once

#include "llvm/IR/Module.h"
#include "core/Criterion.h"
#include "smtSolver/SmtSolver.h"

enum class ValidationResult {valid, invalid, unknown};

extern bool CriterionPresent;

class SliceCandidateValidation {
public:
	static ValidationResult validate(llvm::Module* program, llvm::Module* candidate,
		CriterionPtr criterion = Criterion::getReturnValueCriterion(),
		CEXType* pCEX = nullptr);
};
