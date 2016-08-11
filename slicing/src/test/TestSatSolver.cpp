/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "catch.hpp"
#include "smtSolver/SmtSolver.h"


TEST_CASE("Test satisfiable", "[SMT]") {
	SatResult result;
	result = SmtSolver::getInstance().checkSat("../testdata/smt/simple-sat.smt");
	CHECK( result == SatResult::sat );

	result = SmtSolver::getInstance().checkSat("../testdata/smt/simple-unsat.smt");
	CHECK( result == SatResult::unsat );
}
