#include "DRM.h"

#include "core/DependencyGraphPasses.h"
#include "core/Util.h"

#include "llvm/IR/LegacyPassManager.h"

using namespace std;
using namespace llvm;

LinearizedFunction::LinearizedFunction(
		Function const& func) : func(func) {
	
	unsigned int index = 0;
	
	for(Instruction const& i : Util::getInstructions(func)) {
		_mapInstToInt[&i] = index++;
	}
	
	// 'index' is the number of instructions
	_mapIntToInst = new Instruction const*[index];
	
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

void LinearizedFunction::print(
		raw_ostream& out) const {
	
	unsigned int const instCount = getInstructionCount();
	
	for(unsigned int i = 0; i < instCount; i++) {
		out << i << "\t" << Util::toString((*this)[i]) << "\n";
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

DRM::DRM(
		LinearizedFunction const& linFunc,
		uint64_t           const  cex[]) :
	linFunc   (linFunc),
	_instCount(linFunc.getInstructionCount()),
	_matrix   (new APInt*[_instCount]) {
	
	// Allocate the reachability matrix
	for(unsigned int i = 0; i < _instCount; i++) {
		_matrix[i] = new APInt(_instCount, 0);
		_matrix[i]->setBit(i); // The instruction itself is always reachable
	}
	
	//legacy::PassManager PM;
	//PM.add(new PostDominatorTree());
	//PM.add(new CDGPass());
	//PM.run(*sliceCandidate);
	
	// Initialize the interpreter with the counterexample
	Interpreter interpreter(linFunc.func, cex);
	
	while(interpreter.getNextInstruction()) {
		
		interpreter.executeNextInstruction();
		
		// Get the reachability row for the recent instruction
		APInt& reachability =
			*_matrix[linFunc[*interpreter.getRecentInstruction()]];
		
		// TODO: control dependency
		
		// Union the reachable instructions of all instructions used by the
		// recent one
		for(Instruction const* i : interpreter.recentDataDependencies) {
			reachability |= *_matrix[linFunc[*i]];
		}
	}
}

DRM::~DRM(void) {
	
	Util::deleteArrayDeep(_matrix, _instCount);
}

APInt const& DRM::computeSlice(
		APInt const& apriori) {
	
	assert(apriori.getBitWidth() == _instCount);
	
	_accumulator = 0;
	
	for(unsigned int i = 0; i < _instCount; i++) {
		if(apriori[i]) {
			_accumulator |= *_matrix[i];
		}
	}
	
	return _accumulator;
}

void DRM::print(
		raw_ostream& out) const {
	
	for(unsigned int i = 0; i < _instCount; i++) {
		out << i << "\t";
		for(unsigned int j = 0; j < _instCount; j++) {
			out << ((*_matrix[i])[j] ? "X" : " ") << " ";
		}
		out << "\n";
	}
}
