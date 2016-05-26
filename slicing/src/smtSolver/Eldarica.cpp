#include "Eldarica.h"
#include <fstream>
#include <sstream>
#include <cassert>

std::string EldaricaCommand::getCommandStr(std::string smtFilePath, std::string resultFilePath) {
	std::stringstream ss;
	ss << this->pathToEldarica;
	ss << " -hsmt ";
	ss << smtFilePath;
	ss << " > ";
	ss << resultFilePath;
	return ss.str();
}


SatResult Eldarica::parseResult(std::string resultFile) {
	std::ifstream input(resultFile);
	std::string line;
	SatResult result = unknown;
	bool foundResult = false;
	while (getline(input, line)) {
		if (line == "sat") {
			result = sat;
			foundResult = true;
			break;
		}
		if (line == "unsat") {
			result = unsat;
			foundResult = true;
			break;
		}
	}
	assert(foundResult && "Did not find result information, please report a bug!");

	return result;
}

SmtCommand& Eldarica::getCommand(){
	return this->command;
}
