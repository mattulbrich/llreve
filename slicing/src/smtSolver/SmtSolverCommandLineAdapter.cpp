#include "SmtSolverCommandLineAdapter.h"

#include <stdlib.h>
#include <iostream>
#include <csignal>

SmtCommand::~SmtCommand() = default;

SmtSolverCommandLineAdapter::~SmtSolverCommandLineAdapter() = default;

SatResult SmtSolverCommandLineAdapter::checkSat(std::string smtFilePath){
	std::string resultFilePath = "solverResult.txt";
	std::string command = this->getCommand().getCommandStr(smtFilePath, resultFilePath);

	// Note, that we assume a POSIX system. Will propably not work corectly on Windows!
	int ret = system(command.c_str());
	// During the system call sigint or sigquit will not be passed to us, as we will
	// execute this within a loop we need to handle the signals. Other wise it will not
	// be possible to terminate the program.
	if (WIFSIGNALED(ret) &&
		(WTERMSIG(ret) == SIGINT || WTERMSIG(ret) == SIGQUIT)) {
		std::cerr << "Got SIGINT or SIGQUIT during execution of SMT solver going to terminate!" << std::endl;
		exit(WTERMSIG(ret));
	}

	if (WEXITSTATUS(ret) != 0) {
		std::cerr << "The execution of smt command went wrong (Exitcode: " << WEXITSTATUS(ret) << "). The following command was tried to be executed:" << std::endl;
		std::cerr << "\"" << command << "\"" << std::endl;
		exit(1);
	}

	return this->parseResult(resultFilePath);
}
