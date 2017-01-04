#include "catch.hpp"

#include "llvm/Transforms/Utils/Cloning.h"

#include "core/SliceCandidateValidation.h"
#include "core/Util.h"
#include "util/FileOperations.h"

#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <iostream>

using namespace std;
using namespace llvm;

TEST_CASE("Test IAA", "[IAA]") {
	shared_ptr<llvm::Module> program = getModuleFromSource("../testdata/dummy/iaa.c");
	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);
	CriterionPtr presentCriterion = shared_ptr<Criterion>(new PresentCriterion());

	Function* everyValue;
	{
	vector<Type*> parameter;
	ArrayRef<Type*> parameterRef(parameter);
	llvm::FunctionType* functionType = FunctionType::get(IntegerType::get(sliceCandidate->getContext() ,32), parameterRef, false);
	everyValue = Function::Create(functionType,
			llvm::GlobalValue::LinkageTypes::ExternalLinkage,
			Twine("__everyValue"),
			&*sliceCandidate);
	}

	int i = 0;
	Instruction* instToReplace = nullptr;
	for (Function& function: *sliceCandidate){
		if (function.getName() == "foo") {
			for (Instruction& instruction:Util::getInstructions(function)) {
				if (i == 13) { //3 oder 13
					instToReplace = &instruction;
				}
				i++;
			}
		}
	}
	BasicBlock::iterator ii(instToReplace);

	vector<Value*> parameter;
	ArrayRef<Value*> parameterRef(parameter);

	ReplaceInstWithInst(instToReplace->getParent()->getInstList(), ii,
		CallInst::Create(everyValue, parameterRef));

	writeModuleToFile("program.llvm", *program);
	writeModuleToFile("slice.llvm", *sliceCandidate);

	ValidationResult result = SliceCandidateValidation::validate(&*program, &*sliceCandidate, presentCriterion);
	if (result == ValidationResult::valid) {
		cout << "Valid" << endl;
	} else {
		cout << "Invalid" << endl;
	}
}
