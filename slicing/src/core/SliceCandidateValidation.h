#pragma once

#include "llvm/IR/Module.h"
#include "core/Criterion.h"

enum class ValidationResult {valid, invalid, unknown};

class CounterExample;

extern bool CriterionPresent;

class SliceCandidateValidation {
public:
	static ValidationResult validate(llvm::Module* program, llvm::Module* candidate,
		CriterionPtr criterion = Criterion::getReturnValueCriterion(),
		CounterExample* counterExample = nullptr);
};
