#include "catch.hpp"
#include "smtSolver/SmtSolver.h"


TEST_CASE("Test satisfiable", "[SMT]") {
	SatResult result;
	result = SmtSolver::getInstance().checkSat("../testdata/smt/simple-sat.smt");
	CHECK( result == SatResult::sat );

	result = SmtSolver::getInstance().checkSat("../testdata/smt/simple-unsat.smt");
	CHECK( result == SatResult::unsat );
}
