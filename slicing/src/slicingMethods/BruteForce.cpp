/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "BruteForce.h"

#include "util/LambdaFunctionPass.h"
#include "core/Util.h"
#include "core/SlicingPass.h"
#include "util/misc.h"
#include <iostream>
#include <bitset>

#include "core/SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"


using namespace std;
using namespace llvm;

BruteForce::BruteForce(ModulePtr program, llvm::raw_ostream* ostream):SlicingMethod(program),ostream_(ostream){
	callsToReve_ = 0;
	numberOfTries_ = 0;
}

shared_ptr<Module> BruteForce::computeSlice(CriterionPtr c) {
	ModulePtr program = getProgram();

	unsigned numInstructions = 0;
	for_each_relevant_instruction(*program, *c, [&numInstructions](Instruction& instruction){
		numInstructions++;
	});

	ModulePtr bestCandidate = shared_ptr<Module>(nullptr);
	int maxSliced = -1;

	if (ostream_) {
		*ostream_ << "|--------------------|\n";
		*ostream_ << "|";
		ostream_->flush();
	}

	int progress = 0;

	unsigned maxIterations = 1 << numInstructions;
	float step = maxIterations / 20.f;

	numberOfPossibleTries_ = maxIterations;
	numberOfTries_ = 0;
	callsToReve_ = 0;

	int iterations = 0;
	for_each_pattern(numInstructions, [&](const vector<bool>& pattern, bool* done){
		if ((progress * step) < iterations) {
			progress++;
			if (ostream_) {
				*ostream_ << "=";
				ostream_->flush();
			}
		}

		ModulePtr sliceCandidate = CloneModule(&*program);
		int sliced = 0;
		unsigned instructionCounter = 0;

		for_each_relevant_instruction(*sliceCandidate, *c, [&](Instruction& instruction){
			if (pattern[instructionCounter]) {
				SlicingPass::toBeSliced(instruction);
				sliced++;
			}
			instructionCounter++;
		});

		//Will be deleted from pass manager!
		SlicingPass* slicingPass = new SlicingPass();
		llvm::legacy::PassManager PM;
		PM.add(slicingPass);
		PM.run(*sliceCandidate);

		if (!slicingPass->hasUnSlicedInstructions()) {
			assert(sliced >= maxSliced && "InternalError: The first valid slice should be the largest!");
			callsToReve_++;

			ValidationResult isValid = SliceCandidateValidation::validate(&*program, &*sliceCandidate, c);
			if (isValid == ValidationResult::valid) {
				maxSliced = sliced;
				bestCandidate = sliceCandidate;
				*done = true;
			}
		}

		numberOfTries_++;
		iterations++;
	});

	if (ostream_) {
		*ostream_ << "|\n";
		ostream_->flush();
	}

	return bestCandidate;
}

void BruteForce::for_each_pattern(unsigned numInstructions, std::function<void (vector<bool>& pattern, bool* done)> lambda) {
	vector<bool> pattern(numInstructions, true);
	bool done = false;

	for (unsigned numberOfZero = 0; numberOfZero <= numInstructions; numberOfZero++) {
		std::sort(pattern.begin(), pattern.end());
		if (numberOfZero > 0) {
			pattern[numberOfZero - 1] = false;
		}

		do {
			lambda(pattern, &done);
			if (done)
				break;
		} while (std::next_permutation(pattern.begin(), pattern.end()));

		if (done)
			break;
	}
}

void BruteForce::for_each_relevant_instruction(Module& program,
	Criterion& criterion, std::function<void (llvm::Instruction& instruction)> lambda) {
	set<Instruction*> criterionInstructions = criterion.getInstructions(program);


	for (Function& function: program) {
		if (!Util::isSpecialFunction(function)) {
			for(Instruction& instruction : Util::getInstructions(function)) {
				const bool isCriterion = criterionInstructions.find(&instruction) != criterionInstructions.end();
				if (!isCriterion) {
					lambda(instruction);
				}
			}
		}
	}
}

unsigned BruteForce::getNumberOfReveCalls(){
	return callsToReve_;
}

unsigned BruteForce::getNumberOfTries(){
	return numberOfTries_;
}

unsigned BruteForce::getNumberOfPossibleTries(){
	return numberOfPossibleTries_;
}
