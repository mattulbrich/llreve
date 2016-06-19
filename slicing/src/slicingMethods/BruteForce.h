#pragma once

#include "SlicingMethod.h"
#include "llvm/Support/raw_ostream.h"


class BruteForce: public SlicingMethod {
public:
	/**
	 * @param program to slice
	 * @param ostream target for progress output. Use nullptr to supress progress printing.
	 */
	BruteForce(ModulePtr program, llvm::raw_ostream* ostream = &llvm::outs());
	virtual ModulePtr computeSlice(CriterionPtr c) override;
	unsigned getNumberOfReveCalls();

private:
	llvm::raw_ostream* ostream_;
	unsigned callsToReve_;
};
