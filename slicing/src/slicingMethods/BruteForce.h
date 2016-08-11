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

#include "SlicingMethod.h"
#include "llvm/Support/raw_ostream.h"
#include "core/Criterion.h"

#include <vector>


class BruteForce: public SlicingMethod {
public:
	/**
	 * @param program to slice
	 * @param ostream target for progress output. Use nullptr to supress progress printing.
	 */
	BruteForce(ModulePtr program, llvm::raw_ostream* ostream = &llvm::outs());
	virtual ModulePtr computeSlice(CriterionPtr c) override;
	unsigned getNumberOfReveCalls();
	unsigned getNumberOfTries();
	unsigned getNumberOfPossibleTries();

private:
	llvm::raw_ostream* ostream_;
	unsigned callsToReve_;
	unsigned numberOfTries_;
	unsigned numberOfPossibleTries_;

	void for_each_relevant_instruction(llvm::Module& program, Criterion& criterion,
		std::function<void (llvm::Instruction& instruction)> lambda);
	void for_each_pattern(unsigned numInstructions, std::function<void (std::vector<bool>& pattern, bool* done)> lambda);
};
