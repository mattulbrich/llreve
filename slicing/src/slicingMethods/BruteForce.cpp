#include "BruteForce.h"

#include "util/LambdaFunctionPass.h"
#include "core/Util.h"
#include "core/SlicingPass.h"
#include <iostream>

#include "core/SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"


using namespace std;
using namespace llvm;


shared_ptr<Module> BruteForce::computeSlice(CriterionPtr c) {
	ModulePtr program = getProgram();
	int numFunctions = 0;
	int numInstructions = 0;
	for (Function& function: *program) {
		numFunctions++;
		for(Instruction& i : Util::getInstructions(function)) {
			numInstructions++;
		}
	}
	//We will not be able to slice the return instruction:
	numInstructions--;

	ModulePtr bestCandidate = shared_ptr<Module>(nullptr);
	int maxSliced = 0;

	cout << "|--------------------|" << endl;
	cout << "|";
	int progress = 0;

	int iterations = 1 << numInstructions;
	float step = iterations / 20.f;

	for (int pattern = 0; pattern < iterations; pattern++){
		if ((progress * step) < pattern) {
			progress++;
			cout << "=";
			cout.flush();
		}

		ModulePtr sliceCandidate = CloneModule(&*program);
		int sliced = 0;

		for (Function& function: *sliceCandidate) {
			int instructionCounter = 0;
			for(Instruction& instruction : Util::getInstructions(function)) {
				if (pattern & (1 << instructionCounter)) {
					SlicingPass::toBeSliced(instruction);
					sliced++;
				}
				instructionCounter++;
			}
		}

		llvm::legacy::PassManager PM;
		PM.add(new SlicingPass());
		PM.run(*sliceCandidate);

		if (sliced > maxSliced) {
			ValidationResult isValid = SliceCandidateValidation::validate(&*program, &*sliceCandidate, c);
			if (isValid == ValidationResult::valid) {
				maxSliced = sliced;
				bestCandidate = sliceCandidate;
			}
		}
	}
	cout << "|" << endl;

	return bestCandidate;
}
