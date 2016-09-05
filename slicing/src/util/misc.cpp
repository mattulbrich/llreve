/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "misc.h"

#include "core/Util.h"

#include "preprocessing/PromoteAssertSlicedPass.h"
#include "preprocessing/ExplicitAssignPass.h"
#include "preprocessing/MarkAnalysisPass.h"
#include "core/Criterion.h"
#include "slicingMethods/impact_analysis_for_assignments/ImpactAnalysisForAssignments.h"

using namespace llvm;

bool Util::isSpecialFunction(Function& function){
	return function.getName() == Criterion::FUNCTION_NAME
			|| MarkAnalysisPass::isMark(function)
			|| function.getName() == ImpactAnalysisForAssignments::EVERY_VALUE_FUNCTION_NAME
			|| function.getName() == PromoteAssertSlicedPass::FUNCTION_NAME
			|| ExplicitAssignPass::isExplicitAssignFunction(function);
}

int Util::countInstructions(Module& module) {
	int count = 0;

	for (Function& function:module) {
		if (!Util::isSpecialFunction(function)) {
			for (BasicBlock& block: function) {
				for (Instruction& instruction:block) {
					UTIL_UNUSED(instruction);
					++count;
				}
			}
		}
	}

	return count;
}
