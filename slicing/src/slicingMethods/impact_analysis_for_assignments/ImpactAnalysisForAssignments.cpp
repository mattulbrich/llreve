#include "ImpactAnalysisForAssignments.h"

#include "core/SlicingPass.h"
#include "core/SliceCandidateValidation.h"

#include "core/Util.h"
#include "util/misc.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <iostream>

using namespace llvm;
using namespace std;

string ImpactAnalysisForAssignments::EVERY_VALUE_FUNCTION_NAME = "__everyValue";

ImpactAnalysisForAssignments::ImpactAnalysisForAssignments(ModulePtr program):SlicingMethod(program){

}


ModulePtr ImpactAnalysisForAssignments::computeSlice(CriterionPtr criterion){
	callsToReve_ = 0;
	ModulePtr program = getProgram();
	ModulePtr slice = CloneModule(&*program);
	set<Instruction*> criterionInstructions = criterion->getInstructions(*slice);

	for (Function& function:*slice) {
		if (!Util::isSpecialFunction(function)) {
			for(Instruction& instruction : Util::getInstructions(function)) {
				Type* type = instruction.getType();
				const bool isCriterion = criterionInstructions.find(&instruction) != criterionInstructions.end();
				if (!isCriterion && !isa<PHINode>(instruction) && type->isIntegerTy() && type->getIntegerBitWidth() > 1) {
					ValueToValueMapTy valueMap;
					ModulePtr impactAbstraction = CloneModule(&*slice, valueMap);

					Instruction* instToReplace = cast<Instruction>(&*valueMap[&instruction]);
					BasicBlock::iterator ii(instToReplace);

					vector<Value*> parameter;
					ArrayRef<Value*> parameterRef(parameter);

					ReplaceInstWithInst(instToReplace->getParent()->getInstList(), ii,
						CallInst::Create(createEveryValueFunction(impactAbstraction), parameterRef));

					callsToReve_++;
					ValidationResult result = SliceCandidateValidation::validate(&*slice, &*impactAbstraction, criterion);
					if (result == ValidationResult::valid) {
						SlicingPass::toBeSliced(instruction);
					}
				}
			}
		}
	}

	// for (Function& function:*slice) {
	// 	for (BasicBlock& block:function){
	// 		bool allToBeSliced = true;
	// 		for (Instruction& instruction:block) {
	// 			if (allToBeSliced && isa<TerminatorInst>(instruction)) {
	// 				SlicingPass::toBeSliced(instruction);
	// 			} else if (!SlicingPass::isToBeSliced(instruction)) {
	// 				allToBeSliced = false;
	// 				break;
	// 			}
	// 		}
	// 	}
	// }

	llvm::legacy::PassManager PM;
	PM.add(new SlicingPass());
	PM.run(*slice);

	std::cout << "Number of Reve calls: " << callsToReve_ << std::endl;

	ValidationResult result = SliceCandidateValidation::validate(&*program, &*slice, criterion);
	if (result != ValidationResult::valid) {
		std::cout << "Error: Produced Slice is not Valid." << std::endl;
	}
	//assert(result == ValidationResult::valid);

	return slice;
}

llvm::Function* ImpactAnalysisForAssignments::createEveryValueFunction(ModulePtr impactAbstraction, Type * type){
	if (!type) {
		type = IntegerType::get(impactAbstraction->getContext() ,32);
	}
	vector<Type*> parameter;
	ArrayRef<Type*> parameterRef(parameter);
	llvm::FunctionType* functionType = FunctionType::get(type, parameterRef, false);
	return Function::Create(functionType,
			llvm::GlobalValue::LinkageTypes::ExternalLinkage,
			Twine(EVERY_VALUE_FUNCTION_NAME),
			&*impactAbstraction);
}

unsigned ImpactAnalysisForAssignments::getNumberOfReveCalls(){
	return callsToReve_;
}
