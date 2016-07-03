#include "CGS.h"

#include "core/Util.h"
#include "dynamic/Interpreter.h"
#include "util/misc.h"

using namespace std;
using namespace llvm;

shared_ptr<Module> CGS::computeSlice(
		CriterionPtr c) {
	
	ModulePtr program = getProgram();
	Function& func    = getFirstNonSpecialFunction(*program);
	uint64_t const input[] = {1};
	
	Interpreter interpreter(func, input);
	
	while(interpreter.getNextInstruction()) {
		//_ostream << Util::toString(*interpreter.getNextInstruction()) << "\n";
		interpreter.executeNextInstruction();
	}
	
	
	_ostream << "Interpreting finished: " << interpreter.getReturnValue()->getLimitedValue() << "\n";
	
	return program;
}

Function& CGS::getFirstNonSpecialFunction(
		Module& module) {
	
	for(Function& i : module) {
		if(!Util::isSpecialFunction(i)) {
			return i;
		}
	}
}
