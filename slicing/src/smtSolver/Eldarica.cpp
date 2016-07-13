#include "Eldarica.h"
#include <fstream>
#include <sstream>
#include <cassert>
#include <iostream>

std::regex const Eldarica::patternSat("sat");
std::regex const Eldarica::patternUnsat("unsat");
std::regex const Eldarica::patternInitPred("INIT\\((?:(-?[[:digit:]]+)(, )?)*\\)");

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
		
		std::smatch result;
		regex_search(input, result, patternInitPred);
		
		assert(result.size() - 1 > pCEX->size());
		
		// Ignore the first capture group as this is the regex itself
		for(unsigned int i = 0; i < pCEX->size(); i++) {
			(*pCEX)[i] = stoll(result[i + 1]);
		}
		
		return SatResult::unsat;
		
	} else if(regex_search(input, patternSat)) {
		
		return SatResult::sat;
		
	} else {
		
		assert(false && "Did not find result information, please report a bug!");
		return SatResult::unknown;
	}
}

SmtCommand& Eldarica::getCommand(){
	return this->command;
}
