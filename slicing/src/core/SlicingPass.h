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

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/DebugInfoMetadata.h"

/**
* The prupose of this class is to remove statements previously marked for removal.
* To mark a statement for removal use SlcingPass::toBeSliced
*/
class SlicingPass : public llvm::FunctionPass {
public:
	static char ID;
	static const std::string SLICE;
	static const std::string TO_BE_SLICED;
	static const std::string NOT_SLICED;

	static void toBeSliced(llvm::Instruction& instruction);
	static void markNotSliced(llvm::Instruction& instruction);
	static bool isToBeSliced(llvm::Instruction& instruction);
	static bool isNotSliced(llvm::Instruction& instruction);

	SlicingPass();
	virtual bool runOnFunction(llvm::Function &Fun) override;
	virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

	bool hasUnSlicedInstructions();

private:
	llvm::DominatorTree* domTree;
	bool hasUnSlicedInstructions_;

};

