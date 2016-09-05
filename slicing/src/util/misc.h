/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "llvm/IR/Function.h"
 #include "llvm/IR/Module.h"

namespace Util {
	bool isSpecialFunction(llvm::Function& function);
	int countInstructions(llvm::Module& module);
}
