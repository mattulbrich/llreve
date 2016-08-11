/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

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
