#include "catch.hpp"

#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/SlicingPass.h"
#include "preprocessing/AddVariableNamePass.h"
#include "util/LambdaFunctionPass.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/IPO.h"

#include "core/SliceCandidateValidation.h"

#include "util/FileOperations.h"


using namespace llvm;
using namespace std;

using clang::CodeGenAction;

void testSingleLineElemination(string fileName, int line, ValidationResult expectedResult);

void testSingleLineElemination(string fileName, int line, ValidationResult expectedResult) {
	shared_ptr<llvm::Module> program = getModuleFromSource(fileName);
	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);

	{
		string ir;
		llvm::raw_string_ostream stream(ir);

		llvm::legacy::PassManager PM;
		PM.add(new LambdaFunctionPass([&](Function& function)->bool{
			int i = 0;
			for(llvm::BasicBlock& block: function) {
				for(llvm::Instruction& instruction: block) {
					i++;
					if (i == line)
					{
						SlicingPass::toBeSliced(instruction);
					}
					stream << i << ": " << instruction << "\n";
				}
			}
			return true;
		}));
		PM.add(new SlicingPass());
		PM.run(*sliceCandidate);
	}

	ValidationResult result = SliceCandidateValidation::validate(&*program, &*sliceCandidate);
	CHECK(result == expectedResult);
}

TEST_CASE("Validation of valid Slicecandidate", "[SliceCandidateValidation],[basic]") {
	testSingleLineElemination("../testdata/simple_sliceable.c", 1, ValidationResult::valid);
}

TEST_CASE("Validation of invalid Slicecandidate", "[SliceCandidateValidation],[basic]") {
	testSingleLineElemination("../testdata/simple_unsliceable.c", 1, ValidationResult::invalid);
}
