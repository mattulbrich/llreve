#include "SlicingMethod.h"

using namespace std;
using namespace llvm;

SlicingMethod::~SlicingMethod() = default;


Criterion::Criterion(){
	this->isReturnVal = true;
}

bool Criterion::isReturnValue(){
	return this->isReturnVal;
}

shared_ptr<Module> SlicingMethod::getProgram(){
	return this->program;
}
