// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "BruteForce.h"

#include "util/LambdaFunctionPass.h"
#include "core/Util.h"
#include "core/SlicingPass.h"
#include <iostream>
#include <bitset>

#include "core/SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"


using namespace std;
using namespace llvm;

BruteForce::BruteForce(ModulePtr program, llvm::raw_ostream* ostream):SlicingMethod(program),ostream_(ostream){
	callsToReve_ = 0;
}

shared_ptr<Module> BruteForce::computeSlice(CriterionPtr c) {
	ModulePtr program = getProgram();
	callsToReve_ = 0;
	int numFunctions = 0;
	int numInstructions = 0;
	for (Function& function: *program) {
		numFunctions++;
		for(Instruction& i : Util::getInstructions(function)) {
			numInstructions++;
		}
	}

	// We do not want to slice the criterion itself
	numInstructions -= c->getInstructions(*program).size();

	ModulePtr bestCandidate = shared_ptr<Module>(nullptr);
	int maxSliced = -1;

	if (ostream_) {
		*ostream_ << "|--------------------|\n";
		*ostream_ << "|";
		ostream_->flush();
	}

	int progress = 0;

	int iterations = 1 << numInstructions;
	float step = iterations / 20.f;

	for (int pattern = 0; pattern < iterations; pattern++){
		if ((progress * step) < pattern) {
			progress++;
			if (ostream_) {
				*ostream_ << "=";
				ostream_->flush();
			}
		}

		ModulePtr sliceCandidate = CloneModule(&*program);
		set<Instruction*> criterionInstructions = c->getInstructions(*sliceCandidate);
		int sliced = 0;
		int instructionCounter = 0;

		for (Function& function: *sliceCandidate) {
			for(Instruction& instruction : Util::getInstructions(function)) {
				const bool isCriterion = criterionInstructions.find(&instruction) != criterionInstructions.end();
				if (!isCriterion) {
					if (pattern & (1 << instructionCounter)) {
						SlicingPass::toBeSliced(instruction);
						sliced++;
					}
					instructionCounter++;
				}
			}
		}

		//Will be deleted from pass manager!
		SlicingPass* slicingPass = new SlicingPass();
		llvm::legacy::PassManager PM;
		PM.add(slicingPass);
		PM.run(*sliceCandidate);

		if (!slicingPass->hasUnSlicedInstructions() && sliced >= maxSliced) {
			++callsToReve_;
			ValidationResult isValid = SliceCandidateValidation::validate(&*program, &*sliceCandidate, c);
			if (isValid == ValidationResult::valid) {
				maxSliced = sliced;
				bestCandidate = sliceCandidate;
			}
		}
	}
	if (ostream_) {
		*ostream_ << "|\n";
		ostream_->flush();
	}

	return bestCandidate;
}


unsigned BruteForce::getNumberOfReveCalls(){
	return callsToReve_;
}