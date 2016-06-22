#include "Criterion.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"

#include "core/PromoteAssertSlicedPass.h"
#include "core/Util.h"
#include "util/misc.h"

using namespace std;
using namespace llvm;

const string Criterion::FUNCTION_NAME = "__criterion";

Criterion::Criterion(){}

bool Criterion::isReturnValue() const{
	return false;
}

CriterionPtr Criterion::getReturnValueCriterion() {
	static CriterionPtr returnValueCriterion(new ReturnValueCriterion());
	return returnValueCriterion;
}

ReturnValueCriterion::ReturnValueCriterion():Criterion(){}

bool ReturnValueCriterion::isReturnValue() const {
	return true;
}

std::set<llvm::Instruction*> ReturnValueCriterion::getInstructions(llvm::Module& module) const{
	bool multipleFunctions = false;
	set<Instruction*> instructions;
	for (Function& function:module) {
		if (!Util::isSpecialFunction(function)) {
			assert(!multipleFunctions && "Can't use slicing after return value for programs with more than one function!");
		multipleFunctions = true;

		for (Instruction& instruction: Util::getInstructions(function)) {
			if(isa<ReturnInst>(&instruction)) {
				instructions.insert(&instruction);
			}
		}
	}
}

return instructions;
}

PresentCriterion::PresentCriterion():Criterion(){}

std::set<llvm::Instruction*> PresentCriterion::getInstructions(llvm::Module& module) const{
	bool multipleCriterions = false;
	set<Instruction*> instructions;
	for (Function& function:module) {
		if (!Util::isSpecialFunction(function)) {

			for (Instruction& instruction: Util::getInstructions(function)) {
				if (CallInst* callInst = dyn_cast<CallInst>(&instruction)) {
					if ((callInst->getCalledFunction() != nullptr) &&
						(callInst->getCalledFunction()->getName() == Criterion::FUNCTION_NAME)){

						assert(!multipleCriterions && "Can't use slicing for multiple criterions!");
						multipleCriterions = true;

						instructions.insert(callInst);
				}
			}

		}
	}
}

return instructions;
}
