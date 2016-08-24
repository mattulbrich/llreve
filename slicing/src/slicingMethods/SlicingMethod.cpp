/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SlicingMethod.h"

using namespace std;
using namespace llvm;

SlicingMethod::~SlicingMethod() = default;


shared_ptr<Module> SlicingMethod::getProgram(){
	return this->program;
}
