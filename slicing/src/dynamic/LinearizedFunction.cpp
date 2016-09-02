#include "LinearizedFunction.h"

#include "core/Util.h"

#include <iomanip>
#include <sstream>

using namespace std;
using namespace llvm;

LinearizedFunction::LinearizedFunction(
		Function const& func) : func(func), _printPaddingLength(0) {
	
	unsigned int index = 0;
	
	for(Instruction const& i : Util::getInstructions(func)) {
		_mapInstToInt[&i] = index++;
	}
	
	// 'index' is the number of instructions
	_printPaddingLength = Util::getIntegerLength(index - 1);
	_mapIntToInst       = new Instruction const*[index];
	
	for(Instruction const& i : Util::getInstructions(func)) {
		// use the previous generated mapping as the iteration may vary
		// between different iterations
		_mapIntToInst[_mapInstToInt[&i]] = &i;
	}
}

LinearizedFunction::~LinearizedFunction(void) {
	
	delete [] _mapIntToInst;
}

unsigned int LinearizedFunction::getInstructionCount(void) const {
	
	return static_cast<unsigned int>(_mapInstToInt.size());
}

string LinearizedFunction::indexToString(
		unsigned int const index) const {
	
	stringstream stream;
	
	stream << setfill(' ') << setw(_printPaddingLength) << dec << index;
	
	return stream.str();
}

void LinearizedFunction::print(
		raw_ostream& out) const {
	
	unsigned int const instCount = getInstructionCount();
	
	for(unsigned int i = 0; i < instCount; i++) {
		out << indexToString(i) << " " << Util::toString((*this)[i]) << "\n";
	}
}

Instruction const& LinearizedFunction::operator[](
		unsigned int const index) const {
	
	return *_mapIntToInst[index];
}

unsigned int LinearizedFunction::operator[](
		Instruction const& inst)  const {
	
	return _mapInstToInt.at(&inst);
}
