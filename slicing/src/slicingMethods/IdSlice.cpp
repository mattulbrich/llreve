#include "IdSlice.h"

#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "core/SliceCandidateValidation.h"
#include "core/SliceCandidate.h"

ModulePtr IdSlicing::computeSlice(CriterionPtr criterion) {
	ModulePtr result = std::shared_ptr<llvm::Module>(nullptr);

	ModulePtr program = getProgram();
	ModulePtr sliceCandidate = CloneModule(&*program);
	ValidationResult valid = SliceCandidateValidation::validate(&*program, &*sliceCandidate, criterion);
	if (valid == ValidationResult::valid) {
		result = sliceCandidate;
	}

	// SliceCandidate candidate(getProgram(), criterion);
	// if (candidate.validate()) {
	// 	result = candidate.getCandidate();
	// }

	return result;
}
