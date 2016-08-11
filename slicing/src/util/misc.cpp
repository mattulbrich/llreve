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

#include "preprocessing/PromoteAssertSlicedPass.h"
#include "preprocessing/ExplicitAssignPass.h"
#include "core/Criterion.h"

using namespace llvm;

bool Util::isSpecialFunction(Function& function){
	return function.getName() == Criterion::FUNCTION_NAME
			|| function.getName() == "__mark"
			|| function.getName() == PromoteAssertSlicedPass::FUNCTION_NAME
			|| function.getName() == ExplicitAssignPass::FUNCTION_NAME;
}
