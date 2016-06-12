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

	// We do not want to slice the criterion itself
	numInstructions -= c->getInstructions(*program).size();

	ModulePtr bestCandidate = shared_ptr<Module>(nullptr);
	int maxSliced = -1;

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
