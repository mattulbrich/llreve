/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SmtSolver.h"
#include "Eldarica.h"

SmtSolver& SmtSolver::getInstance() {
	static Eldarica instance("eld");
	return instance;
}

SmtSolver::~SmtSolver() = default;
