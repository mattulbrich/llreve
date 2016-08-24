/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Eldarica.h"
#include <fstream>
#include <sstream>
#include <cassert>
#include <iostream>

std::regex const Eldarica::patternSat("sat");
std::regex const Eldarica::patternUnsat("unsat");
std::regex const Eldarica::patternUnknown("unknown");
std::regex const Eldarica::patternInitPred("INIT\\((?:-?[[:digit:]]+(?:, )?)*\\)");
std::regex const Eldarica::patternInitPredTokenizer("INIT\\(|, |\\)");

std::string EldaricaCommand::getCommandStr(std::string smtFilePath, std::string resultFilePath) {
	std::stringstream ss;
	ss << this->pathToEldarica;
	ss << " -hsmt -cex ";
	ss << smtFilePath;
	ss << " > ";
	ss << resultFilePath;
	return ss.str();
}

SatResult Eldarica::parseResult(std::string resultFile, CEXType* pCEX) {

	std::ifstream inputStream(resultFile);
	std::string   input(
		(std::istreambuf_iterator<char>(inputStream)),
		 std::istreambuf_iterator<char>());

	if(regex_search(input, patternUnsat)) {

		if(pCEX) {

			std::smatch result;
			regex_search(input, result, patternInitPred);

			std::string                initPred = result[0];
			std::sregex_token_iterator itCex(
				initPred.begin(), initPred.end(), patternInitPredTokenizer, -1);

			// Ignore the first token (empty string)
			for(unsigned int i = 0; i < pCEX->size(); i++) {
				++itCex;
				(*pCEX)[i] = stoll(itCex->str());
			}
		}

		return SatResult::unsat;

	} else if(regex_search(input, patternSat)) {

		return SatResult::sat;

	} else if(regex_search(input, patternUnknown)) {
		
		return SatResult::unknown;
		
	} else {
		std::cout << "unknown result: " << input;
		assert(
			false && "Did not find result information, please report a bug!");
		
		return SatResult::unknown;
	}
}

SmtCommand& Eldarica::getCommand(){
	return this->command;
}
