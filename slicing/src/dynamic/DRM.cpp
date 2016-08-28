#include "DRM.h"

#include "core/DependencyGraphPasses.h"
#include "core/Util.h"

#include "llvm/IR/Module.h"

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
		CEXType            const& cex) :
	linFunc     (linFunc),
	_instCount  (linFunc.getInstructionCount()),
	_matrix     (new APInt*[_instCount]),
	_accumulator(_instCount, 0) {
	
	legacy::PassManager pm;
	Heap                heap;
	
	// Array that holds the control dependency for each statement
	Instruction const** const ctrlDependencies =
		new Instruction const*[_instCount];
	
	// Create arrays for storing all nodes and the recently used nodes
	list<APInt const*>* const nodes       = new list<APInt const*>[_instCount];
	APInt const**       const recentNodes = new APInt const*      [_instCount];
	
	// Bit array where the current reachability is accumulated
	APInt reachability(_instCount, 0);
	
	// Compute the control dependencies and store them in 'ctrlDependencies'
	pm.add(new PostDominatorTree());
	pm.add(new CDGPass());
	pm.add(new CtrlDepExtractionPass(linFunc, ctrlDependencies));
	pm.run(*const_cast<Module*>(linFunc.func.getParent()));
	
	// Initialize the interpreter with the counterexample
	Interpreter interpreter(linFunc.func, cex, heap, true, &outs());
	
	while(interpreter.getNextInstruction()) {
		
		interpreter.executeNextInstruction();
		
		// Get the index for the recent instruction
		unsigned int const instIndex =
			linFunc[*interpreter.getRecentInstruction()];
		
		// Reset the reachability array
		reachability.clearAllBits();
		
		// Mark the recently executed instruction as reachable
		reachability.setBit(instIndex);
		
		// Consider the control dependency
		if(ctrlDependencies[instIndex]) {
			reachability |= *recentNodes[linFunc[*ctrlDependencies[instIndex]]];
		}
		
		// Union the reachable instructions of all instructions used by the
		// recent one
		for(Instruction const* i : interpreter.recentDataDependencies) {
			reachability |= *recentNodes[linFunc[*i]];
		}
		
		// Check whether a node with this reachablity configuration already
		// exists and create a new node if there exists none
		if(APInt const* const pExistingNode =
				findNode(nodes[instIndex], reachability)) {
			recentNodes[instIndex] = pExistingNode;
		} else {
			recentNodes[instIndex] = new APInt(reachability);
			nodes      [instIndex].push_back(recentNodes[instIndex]);
		}
	}
	
	// Create the reachability matrix
	for(unsigned int i = 0; i < _instCount; i++) {
		_matrix[i] = new APInt(_instCount, 0);
		_matrix[i]->setBit(i); // A node is always reachable from itself
		for(APInt const* j : nodes[i]) {
			*_matrix[i] |= *j;
		}
	}
	
	// Delete temporary nodes
	for(unsigned long i = 0; i < _instCount; i++) {
		for(APInt const* j : nodes[i]) {
			delete j;
		}
	}
	
	// Free resources
	delete [] ctrlDependencies;
	delete [] nodes;
	delete [] recentNodes;
}

DRM::~DRM(void) {
	
	Util::deleteArrayDeep(_matrix, _instCount);
}

APInt const& DRM::computeSlice(
		APInt const& apriori) const {
	
	assert(apriori.getBitWidth() == _instCount);
	
	_accumulator = 0;
	
	for(unsigned int i = 0; i < _instCount; i++) {
		if(apriori[i]) {
			_accumulator |= *_matrix[i];
		}
	}
	
	return _accumulator;
}

APInt const* DRM::findNode(
		list<APInt const*> const& elements,
		APInt              const& ref) {
	
	for(APInt const* i : elements) {
		if(i->eq(ref)) {
			return i;
		}
	}
	
	return nullptr;
}

void DRM::print(
		raw_ostream& out) const {
	
	for(unsigned int i = 0; i < _instCount; i++) {
		out << i << "\t";
		printReachability(*_matrix[i], out);
		out << "\n";
	}
}

void DRM::printReachability(
		APInt const& row,
		raw_ostream& out) const {
	
	for(unsigned int i = 0; i < _instCount; i++) {
		out << (row[i] ? "X" : " ") << " ";
	}
}

bool DRMCompare::operator()(
		DRM const& lhs,
		DRM const& rhs) const {
	
	assert(lhs._instCount == rhs._instCount);
	
	for(unsigned int i = 0; i < lhs._instCount; i++) {
		if(lhs._matrix[i]->ult(*rhs._matrix[i])) {
			return true;
		}
	}
	
	return false;
}

bool APIntCompare::operator()(
		APInt const& lhs,
		APInt const& rhs) const {
	
	return lhs.ult(rhs);
}

char CtrlDepExtractionPass::ID = 0;

void CtrlDepExtractionPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<CDGPass>();
}

bool CtrlDepExtractionPass::runOnFunction(
		Function& func) {
	
	// Check whether this is the correct function
	if(&func != &_linFunc.func) {
		return false;
	}
	
	CDGPass const& cdg = getAnalysis<CDGPass>();
	
	for(Instruction& i : Util::getInstructions(func)) {
	
		auto& predecessors = cdg[i].predecessors;
		
		if(predecessors.size() == 0) {
			_dependencies[_linFunc[i]] = nullptr;
		} else if(predecessors.size() == 1) {
			_dependencies[_linFunc[i]] = (*predecessors.begin())->innerNode;
		} else {
			assert(false);
		}
	}
	
	return false;
}
