#include "SmtSolver.h"
#include "Eldarica.h"

SmtSolver& SmtSolver::getInstance() {
	static Eldarica instance("eld");
	return instance;
}

SmtSolver::~SmtSolver() = default;
