#include "catch.hpp"
#include "util/FileOperations.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"

#include "core/PDGPass.h"
#include "core/SlicingPass.h"
#include "core/SyntacticSlicePass.h"
#include "core/SliceCandidateValidation.h"
#include "core/Util.h"

using namespace std;
using namespace llvm;

void testSyntacticSlicing(string fileName) {
	shared_ptr<llvm::Module> program = getModuleFromFile(fileName);
	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);

	string ir;
	llvm::raw_string_ostream stream(ir);

	llvm::legacy::PassManager PM;
	PM.add(new llvm::PostDominatorTree());
	PM.add(new PDGPass());
	PM.add(new SyntacticSlicePass());
	PM.add(new SlicingPass());
	PM.add(llvm::createPrintModulePass(stream));
	PM.run(*sliceCandidate);

	INFO( "=== Resulting IR: ===  \n" << stream.str());

	ValidationResult result = SliceCandidateValidation::validate(&*program, &*sliceCandidate);
	CHECK(result == ValidationResult::valid);
}

TEST_CASE("Syntactic slice is Valid ", "[SyntacticSlicing],[basic]") {
	testSyntacticSlicing("../testdata/syntacticslicetest.c");
}
