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
#include "Z3.h"

std::unique_ptr<SmtSolver> SmtSolver::solver = nullptr;

void SmtSolver::setSolverEld() {
	solver = std::make_unique<Eldarica>("eld");
}
void SmtSolver::setSolverEldClient() {
	solver = std::make_unique<Eldarica>("eld-client");
}
void SmtSolver::setSolverZ3() {
	solver = std::make_unique<Z3>("z3", "eld-client");
}

SmtSolver& SmtSolver::getInstance() {
	return *solver;
}

SmtSolver::~SmtSolver() = default;
