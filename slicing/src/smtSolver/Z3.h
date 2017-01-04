/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */
#include <string>
#include <regex>
#include "SmtSolverCommandLineAdapter.h"

class Z3Command : public SmtCommand {
public:
	Z3Command(std::string pathToEldarica, std::string pathToZ3): SmtCommand(), pathToEldarica(pathToEldarica), pathToZ3(pathToZ3){}
	virtual std::string getCommandStr(std::string smtFilePath, std::string resultFilePath) override;
private:
	std::string pathToEldarica;
	std::string pathToZ3;

};

class Z3 : public SmtSolverCommandLineAdapter {
public:
	Z3(std::string pathToZ3, std::string pathToEldarica):SmtSolverCommandLineAdapter(), command(pathToEldarica, pathToZ3) {}
	virtual SatResult parseResult(std::string resultFile, CEXType* pCEX) override;
	virtual SmtCommand& getCommand() override;
private:
	Z3Command command;
	static std::regex const patternSat;
	static std::regex const patternUnsat;
	static std::regex const patternUnknown;	
};
