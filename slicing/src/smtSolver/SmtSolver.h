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
#include "dynamic/Interpreter.h"
#include <string>

enum class SatResult {sat, unsat, unknown, timeout};
std::ostream & operator<<(std::ostream & stream, const SatResult &satResult);

typedef Interpreter::InputType CEXType;

class SmtSolver {
public:
	static void setSolverEld();
	static void setSolverEldClient();
	static void setSolverZ3();
	static void setSolverCex1();
	static SmtSolver& getInstance();

	//virtual bool isAvailable() = 0;
	//virtual void setTimeout(int miliSeconds) = 0;
	virtual SatResult checkSat(std::string smtFilePath, CEXType* pCEX = nullptr) = 0;
	virtual ~SmtSolver();
private:
	static std::unique_ptr<SmtSolver> solver;
};

