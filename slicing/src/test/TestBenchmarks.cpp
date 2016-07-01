#include "catch.hpp"

#include <iostream>
#include <vector>
#include <util/FileOperations.h>
#include <slicingMethods/BruteForce.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include "core/Util.h"
#include "preprocessing/PromoteAssertSlicedPass.h"
#include "core/SliceCandidateValidation.h"
#include "util/misc.h"

#include <ctime>
#include <chrono>


using namespace std;
using namespace llvm;

TEST_CASE("Test benchmarks", "[benchmark],[bruteforce]") {
	vector<string> benchmarkFiles;
	vector<string> include;
	string folder = "../testdata/benchmarks/";

	benchmarkFiles.push_back("dead_code_after_ssa.c");
	benchmarkFiles.push_back("dead_code_unused_variable.c");
	benchmarkFiles.push_back("identity_not_modifying.c");
	benchmarkFiles.push_back("identity_plus_minus_50.c");
	benchmarkFiles.push_back("informationflow_cyclic.c");
	benchmarkFiles.push_back("informationflow_dynamic_override.c");
	benchmarkFiles.push_back("informationflow_end_of_loop_override.c");
	benchmarkFiles.push_back("intermediate.c");
	benchmarkFiles.push_back("redundant_code_simple.c");
	benchmarkFiles.push_back("requires_path_sensitivity.c");
	benchmarkFiles.push_back("unreachable_code_nested.c");
	benchmarkFiles.push_back("unreachable_code_simple.c");
	benchmarkFiles.push_back("whole_loop_removable.c");

	cout << "file name \t possible slices \t tried slices \t reve calls \t instructions program \t instructions slice \t cpu time in s \t wall clock time in s " << endl;
	for( string fileName : benchmarkFiles ){
		cout << fileName << "\t";
		cout.flush();
		std::clock_t startCpuTime = std::clock();
		auto startWallClockTime = std::chrono::system_clock::now();

		ModulePtr program = getModuleFromSource(folder + fileName, "", include);
		writeModuleToFile("out/" + fileName + ".orig", *program);

		CriterionPtr criterion;
		CriterionPtr presentCriterion = shared_ptr<Criterion>(new PresentCriterion());
		if (presentCriterion->getInstructions(*program).size() == 0) {
			criterion = shared_ptr<Criterion>(new ReturnValueCriterion());
		} else {
			criterion = presentCriterion;
		}

		BruteForce* bf = new BruteForce(program, nullptr);
		SlicingMethodPtr method = shared_ptr<SlicingMethod>(bf);
		ModulePtr slice = method->computeSlice(criterion);
		writeModuleToFile("out/" + fileName + ".slice", *slice);

		unsigned instructionsInSlice = 0;
		bool noAssertSlicedLeft = true;
		for (Function& fun:*slice) {
			if (!Util::isSpecialFunction(fun)) {
				for(Instruction& instruction : Util::getInstructions(fun)) {
					bool isAssertSliced = PromoteAssertSlicedPass::isAssertSliced(instruction);
					noAssertSlicedLeft &= !isAssertSliced;
					instructionsInSlice++;
				}
			}
		}

		unsigned instructionsInProgram = 0;
		for (Function& fun:*program) {
			if (!Util::isSpecialFunction(fun)) {
				for(Instruction& instruction : Util::getInstructions(fun)) {
					instructionsInProgram++;
				}
			}
		}
		CHECK( noAssertSlicedLeft );

		ValidationResult result = SliceCandidateValidation::validate(&*program, &*slice, criterion);
		CHECK(result == ValidationResult::valid);

		double cpuDuration = (std::clock() - startCpuTime) / double(CLOCKS_PER_SEC);
		std::chrono::duration<double> wctDuration = (std::chrono::system_clock::now() - startWallClockTime);
		cout << bf->getNumberOfPossibleTries() << "\t"
			<< bf->getNumberOfTries() << "\t"
			<< bf->getNumberOfReveCalls() << "\t"
			<< instructionsInProgram << "\t"
			<< instructionsInSlice << "\t"
			<< cpuDuration << "\t"
			<< wctDuration.count() << endl;
	}
}
