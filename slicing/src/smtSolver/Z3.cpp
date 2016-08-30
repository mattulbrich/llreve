#include "Z3.h"

#include "core/Util.h"

#include <fstream>
#include <sstream>
#include <cassert>
#include <iostream>

std::regex const Z3::patternSat("sat");
std::regex const Z3::patternUnsat("unsat");
std::regex const Z3::patternUnknown("unknown");

std::string Z3Command::getCommandStr(std::string smtFilePath, std::string resultFilePath) {
	// i.e.: eld -sp smt.smt2 > z3.smt.smt2 ; z3 z3.smt.smt2 > resultFile
	std::stringstream ss;
	ss << this->pathToEldarica;
	ss << " -sp " << smtFilePath;
	ss << " > z3." << smtFilePath;
	ss << " ; ";
	ss << this->pathToZ3;
	ss << " z3." << smtFilePath << " > " << resultFilePath;
	return ss.str();
}

SatResult Z3::parseResult(std::string resultFile, CEXType* pCEX) {
	
	UTIL_UNUSED(pCEX)
	
	std::ifstream inputStream(resultFile);
	std::string   input(
		(std::istreambuf_iterator<char>(inputStream)),
		 std::istreambuf_iterator<char>());

	if(regex_search(input, patternUnsat)) {

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

SmtCommand& Z3::getCommand(){
	return this->command;
}
