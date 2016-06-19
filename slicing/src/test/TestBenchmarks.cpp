#include "catch.hpp"

#include <iostream>
#include <vector>
#include <util/FileOperations.h>
#include <slicingMethods/BruteForce.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include "core/Util.h"
#include "core/PromoteAssertSlicedPass.h"
#include "core/SliceCandidateValidation.h"


using namespace std;
using namespace llvm;

TEST_CASE("Test benchmarks", "[benchmark],[bruteforce]") {
	vector<string> benchmarkFiles;
	vector<string> include;

	benchmarkFiles.push_back("../testdata/benchmarks/dead_code_after_ssa.c");
	benchmarkFiles.push_back("../testdata/benchmarks/dead_code_unused_variable.c");
	benchmarkFiles.push_back("../testdata/benchmarks/identity_not_modifying.c");
	benchmarkFiles.push_back("../testdata/benchmarks/identity_plus_minus_50.c");
	benchmarkFiles.push_back("../testdata/benchmarks/informationflow_cyclic.c");
	//benchmarkFiles.push_back("../testdata/benchmarks/informationflow_dynamic_override.c");
	benchmarkFiles.push_back("../testdata/benchmarks/informationflow_end_of_loop_override.c");
	benchmarkFiles.push_back("../testdata/benchmarks/redundant_code_simple.c");
	benchmarkFiles.push_back("../testdata/benchmarks/requires_path_sensitivity.c");
	benchmarkFiles.push_back("../testdata/benchmarks/unreachable_code_nested.c");
	benchmarkFiles.push_back("../testdata/benchmarks/unreachable_code_simple.c");

	for( string fileName : benchmarkFiles ){
		cout << fileName << endl;
		ModulePtr program = getModuleFromFile(fileName, "", include);

		CriterionPtr criterion;
		CriterionPtr presentCriterion = shared_ptr<Criterion>(new PresentCriterion());
		if (presentCriterion->getInstructions(*program).size() == 0) {
			criterion = shared_ptr<Criterion>(new ReturnValueCriterion());
		} else {
			criterion = presentCriterion;
		}

		SlicingMethodPtr method = shared_ptr<SlicingMethod>(new BruteForce(program));
		ModulePtr slice = method->computeSlice(criterion);

		bool noAssertSlicedLeft = true;
		for (Function& fun:*slice) {
			for(Instruction& instruction : Util::getInstructions(fun)) {
				bool isAssertSliced = PromoteAssertSlicedPass::isAssertSliced(instruction);
				noAssertSlicedLeft &= !isAssertSliced;
			}
		}
		CHECK( noAssertSlicedLeft );

		ValidationResult result = SliceCandidateValidation::validate(&*program, &*slice);
		CHECK(result == ValidationResult::valid);
	}
}
