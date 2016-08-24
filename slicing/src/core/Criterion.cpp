/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Criterion.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"

#include "preprocessing/PromoteAssertSlicedPass.h"
#include "core/Util.h"
#include "util/misc.h"

#include "Helper.h"

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
	set<Instruction*> instructions;
	Function* criterionFunction = nullptr;
	bool foundMain = false;
	bool singleFunction = true;
	bool firstFunction = true;
	for (Function& function:module) {
		if (!Util::isSpecialFunction(function)) {
			if (function.getName() == "main") {
				foundMain = true;
				criterionFunction = &function;
			}
			if (firstFunction) {
				firstFunction = false;
				criterionFunction = &function;
			} else {
				singleFunction = false;
			}
		}
	}

	if (!singleFunction && !foundMain) {
		logError("There are multiple functions, can't use slicing after return value.\n");
		logWarning("Found the following methods:\n");
		for (Function& function:module) {
			if (!Util::isSpecialFunction(function)) {
				logWarning(function.getName().str() + "\n");
			}
		}
		logError("There are multiple functions, can't use slicing after return value.\n");
		logError("Use __criterion to mark the slicing criterion, or define a main function.\n");
		std::exit(1);
	}
	assert((singleFunction || foundMain) && "Can't use slicing after return value for programs with more than one function!");

	if (criterionFunction) {
		for (Instruction& instruction: Util::getInstructions(*criterionFunction)) {
			if(isa<ReturnInst>(&instruction)) {
				instructions.insert(&instruction);
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
