#include "DRM.h"

#include "core/DependencyGraphPasses.h"
#include "core/Util.h"
#include "util/CtrlDepExtractionPass.h"

#include "llvm/IR/Module.h"

#include <iomanip>
#include <sstream>

using namespace std;
using namespace llvm;

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
	CtrlDepExtractionPass::ResultType ctrlDependencies(_instCount);
	
	// Create arrays for storing all nodes and the recently used nodes
	list<APInt const*>* const nodes       = new list<APInt const*>[_instCount];
	APInt const**       const recentNodes = new APInt const*      [_instCount];
	
	// The recent nodes must explicitely initialized with a null pointer to
	// avoid segmentation faults later on
	for(unsigned int i = 0; i < _instCount; i++) {
		recentNodes[i] = nullptr;
	}
	
	// Bit array where the current reachability is accumulated
	APInt reachability(_instCount, 0);
	
	// Compute the control dependencies and store them in 'ctrlDependencies'
	CtrlDepExtractionPass::getCtrlDependencies(linFunc, ctrlDependencies);
	
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
		
		// Consider the control dependencies
		for(Instruction const* i : ctrlDependencies[instIndex]) {
			if(APInt const* const recentNode = recentNodes[linFunc[*i]]) {
				reachability |= *recentNode;
			}
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
