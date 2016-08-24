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

#include "SlicingMethod.h"

class SyntacticSlicing: public SlicingMethod {
public:
	SyntacticSlicing(ModulePtr program):SlicingMethod(program){}
	virtual ModulePtr computeSlice(CriterionPtr c) override;

};
