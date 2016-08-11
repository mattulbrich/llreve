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
#include <string>

enum class SatResult {sat, unsat, unknown, timeout};

class SmtSolverOption {
	SmtSolverOption(std::string eldaricaPath, std::string z3Path):
		eldaricaPath(eldaricaPath), z3Path(z3Path){}

private:
	std::string eldaricaPath;
	std::string z3Path;
};

class SmtSolver {
public:
	static SmtSolver& getInstance();
	static void setOptions(std::shared_ptr<SmtSolverOption> option);

	//virtual bool isAvailable() = 0;
	//virtual void setTimeout(int miliSeconds) = 0;
	virtual SatResult checkSat(std::string smtFilePath) = 0;
	virtual ~SmtSolver();
private:
	static std::shared_ptr<SmtSolverOption> option;
};

