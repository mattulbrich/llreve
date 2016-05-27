#include "SyntacticSlicing.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include "core/PDGPass.h"
#include "core/SlicingPass.h"
#include "core/SyntacticSlicePass.h"
#include "core/Util.h"
#include "core/SliceCandidateValidation.h"

using namespace std;
using namespace llvm;

shared_ptr<Module> SyntacticSlicing::computeSlice(Criterion c) {
	ModulePtr result = shared_ptr<Module>(nullptr);
	if (c.isReturnValue()) {
		ModulePtr program = getProgram();
		ModulePtr sliceCandidate = CloneModule(&*program);

		llvm::legacy::PassManager PM;
		PM.add(new llvm::PostDominatorTree());
		PM.add(new PDGPass());
		PM.add(new SyntacticSlicePass());
		PM.add(new SlicingPass());
		PM.run(*sliceCandidate);

		ValidationResult valid = SliceCandidateValidation::validate(&*program, &*sliceCandidate);
		if (valid == ValidationResult::valid) {
			result = sliceCandidate;
			outs() << "The produced syntactic slice was verified by reve. :) \n";

		} else if (valid == ValidationResult::valid){
			outs() << "Ups! The produced syntactic slice is not valid! :/ \n";
		} else {
			outs() << "Could not verify the vlidity! :( \n";
		}
	}

	return result;
}
