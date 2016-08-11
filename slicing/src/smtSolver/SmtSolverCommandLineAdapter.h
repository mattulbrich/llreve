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
