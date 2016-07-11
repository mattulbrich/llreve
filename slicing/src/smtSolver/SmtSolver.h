#pragma once
#include "dynamic/Interpreter.h"
#include <string>

enum class SatResult {sat, unsat, unknown, timeout};

typedef Interpreter::InputType CEXType;

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
	virtual SatResult checkSat(std::string smtFilePath, CEXType* pCEX = nullptr) = 0;
	virtual ~SmtSolver();
private:
	static std::shared_ptr<SmtSolverOption> option;
};

