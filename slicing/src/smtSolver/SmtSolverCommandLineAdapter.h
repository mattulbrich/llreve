#pragma once
#include "SmtSolver.h"
#include <string>

class SmtCommand {
public:
	virtual std::string getCommandStr(std::string smtFilePath, std::string resultFilePath) = 0;
	virtual ~SmtCommand();
};

class SmtSolverCommandLineAdapter: public SmtSolver {
public:
	SmtSolverCommandLineAdapter():SmtSolver() {}
	virtual SatResult checkSat(std::string smtFilePath) override;
	virtual SatResult parseResult(std::string resultFile) = 0;
	virtual SmtCommand& getCommand() = 0;
	virtual ~SmtSolverCommandLineAdapter();
};
