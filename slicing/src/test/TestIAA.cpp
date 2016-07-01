#include "catch.hpp"

#include "llvm/Transforms/Utils/Cloning.h"

#include "core/SliceCandidateValidation.h"
#include "util/FileOperations.h"

#include "llvm/IR/Function.h"

using namespace std;
using namespace llvm;

TEST_CASE("Test IAA", "[IAA]") {
	shared_ptr<llvm::Module> program = getModuleFromSource("../testdata/dummy/iaa.c");
	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);

	for (Function& function: *sliceCandidate){

	}

	ValidationResult result = SliceCandidateValidation::validate(&*program, &*sliceCandidate);
}
