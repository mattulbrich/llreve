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
#include <regex>
#include "SmtSolverCommandLineAdapter.h"

class EldaricaCommand : public SmtCommand {
public:
	EldaricaCommand(std::string pathToEldarica): SmtCommand(), pathToEldarica(pathToEldarica){}
	virtual std::string getCommandStr(std::string smtFilePath, std::string resultFilePath) override;
private:
	std::string pathToEldarica;

};

class Eldarica : public SmtSolverCommandLineAdapter {
public:
	Eldarica(std::string pathToEldarica):SmtSolverCommandLineAdapter(), command(pathToEldarica) {}
	virtual SatResult parseResult(std::string resultFile, CEXType* pCEX) override;
	virtual SmtCommand& getCommand() override;
private:
	static std::regex const patternSat;
	static std::regex const patternUnsat;
	static std::regex const patternUnknown;
	static std::regex const patternInitPred;
	static std::regex const patternInitPredTokenizer;
	EldaricaCommand command;
};
