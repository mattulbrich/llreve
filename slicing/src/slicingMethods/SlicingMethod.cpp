#include "SlicingMethod.h"

using namespace std;
using namespace llvm;

SlicingMethod::~SlicingMethod() = default;


shared_ptr<Module> SlicingMethod::getProgram(){
	return this->program;
}
