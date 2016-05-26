#pragma once
#include <string>
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
	virtual SatResult parseResult(std::string resultFile) override;
	virtual SmtCommand& getCommand() override;
private:
	EldaricaCommand command;
};
