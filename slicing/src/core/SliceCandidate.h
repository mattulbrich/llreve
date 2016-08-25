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

#include "core/Criterion.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include "MarkAnalysis.h"

class SliceCandidate;
typedef std::shared_ptr<llvm::Module> ModulePtr;
typedef std::shared_ptr<SliceCandidate> SliceCandidatePtr;

class SliceCandidate {
public:
	SliceCandidate(ModulePtr program, CriterionPtr criterion);

	/**
	 * return the program
	 */
	ModulePtr getProgram();

	/**
	 * return the slice candidate, feel free to modify it
	 */	
	ModulePtr getCandidate();

	/**
	 * return the criterion
	 */
	CriterionPtr getCriterion();

	/**
	 * returns if the candidate is valid
	 */
	bool validate();

	/**
	 * return a deep copy of this slice candidate
	 */ 
	SliceCandidatePtr copy();

	void computeMarks();
	/**
	 * returns a bidirectional map determining which blocks are marks, 
	 * i.e. synchronization points, in the original program.
	 */
	BidirBlockMarkMap* getMarkedBlocksProgram();

	/**
	 * Set the marked blocks map for program and take ownership.
	 */
	void setMarkedBlocksProgram(std::unique_ptr<BidirBlockMarkMap> markMap);

	BidirBlockMarkMap* getMarkedBlocksCandidate();

private:
	//SliceCandidate(ModulePtr program, ModulePtr candidate, CriterionPtr criterion, llvm::ValueToValueMapTy valueMap);
	SliceCandidate();

	ModulePtr program;
	ModulePtr candidate;
	CriterionPtr criterion;

	std::unique_ptr<BidirBlockMarkMap> markedBlocksProgram;
	std::unique_ptr<BidirBlockMarkMap> markedBlocksCandidate;

	/**
	 * Map values from original program to slice candidate.
	 */ 
	llvm::ValueToValueMapTy valueMap;
};
