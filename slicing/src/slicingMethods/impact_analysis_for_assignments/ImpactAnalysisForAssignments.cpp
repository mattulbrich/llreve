#include "ImpactAnalysisForAssignments.h"

#include "core/SlicingPass.h"
#include "core/SliceCandidateValidation.h"

#include "core/Util.h"
#include "util/misc.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "util/logging.h"

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

	bool changed = true;
	while (changed) {
		changed = false;

		vector<Instruction*> instructionsToCheck;
		for (Function& function:*slice) {
			if (!Util::isSpecialFunction(function)) {
				for(Instruction& instruction : Util::getInstructions(function)) {
					Type* type = instruction.getType();
					const bool isCriterion = criterionInstructions.find(&instruction) != criterionInstructions.end();
					if (!isCriterion && !isa<PHINode>(instruction) && type->isIntegerTy() && type->getIntegerBitWidth() > 1) {
						instructionsToCheck.push_back(&instruction);
					}
				}
			}
		}

		for (Instruction* instruction: instructionsToCheck) {
			ValueToValueMapTy valueMap;
			ModulePtr impactAbstraction = CloneModule(&*slice, valueMap);

			Instruction* instToReplace = cast<Instruction>(&*valueMap[instruction]);
			BasicBlock::iterator ii(instToReplace);

			vector<Value*> parameter;
			ArrayRef<Value*> parameterRef(parameter);

			ReplaceInstWithInst(instToReplace->getParent()->getInstList(), ii,
				CallInst::Create(createEveryValueFunction(impactAbstraction, instToReplace->getType()), parameterRef));

			callsToReve_++;
			std::cout << ".";
			std::flush(std::cout);
			ValidationResult result = SliceCandidateValidation::validate(&*slice, &*impactAbstraction, criterion);
			if (result == ValidationResult::valid) {
				SlicingPass::toBeSliced(*instruction);
				for (Function& function:*slice) {
					// Deleted by function pass manager
					SlicingPass* slicingPass = new SlicingPass();

					llvm::legacy::FunctionPassManager fpm(slice.get());
					fpm.add(slicingPass);
					fpm.run(function);

					changed |= slicingPass->hasSlicedInstructions();
				}
			}
		}
	}
	std::cout << std::endl;
	std::cout << "Number of Reve calls: " << callsToReve_ << std::endl;
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
