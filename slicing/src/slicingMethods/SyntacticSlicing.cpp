#include "SyntacticSlicing.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include "core/DependencyGraphPasses.h"
#include "core/SlicingPass.h"
#include "core/SyntacticSlicePass.h"
#include "core/Util.h"
#include "core/SliceCandidateValidation.h"

using namespace std;
using namespace llvm;

shared_ptr<Module> SyntacticSlicing::computeSlice(CriterionPtr criterion) {
	ModulePtr result = shared_ptr<Module>(nullptr);

	ModulePtr program = getProgram();
	ModulePtr sliceCandidate = CloneModule(&*program);

	llvm::legacy::PassManager PM;
	PM.add(new llvm::PostDominatorTree());
	PM.add(new CDGPass());
	PM.add(new DDGPass());
	PM.add(new PDGPass());
	PM.add(new SyntacticSlicePass(criterion));
	PM.add(new SlicingPass());
	PM.run(*sliceCandidate);

	ValidationResult valid = SliceCandidateValidation::validate(&*program, &*sliceCandidate, criterion);
	if (valid == ValidationResult::valid) {
		result = sliceCandidate;
		outs() << "The produced syntactic slice was verified by reve. :) \n";

	} else if (valid == ValidationResult::valid){
		outs() << "Ups! The produced syntactic slice is not valid! :/ \n";
	} else {
		outs() << "Could not verify the vlidity! :( \n";
	}

	return result;
}
