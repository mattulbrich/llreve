#include "DDGPass.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/Use.h"
#include "llvm/Support/Casting.h"

#include <iostream>

using namespace std;
using namespace llvm;

static RegisterPass<DDGPass> tmp("ddg-creation", "DDG Creation", true, true);

char DDGPass::ID = 0;

DDGPass::~DDGPass() {
	
	clearNodes();
}

DDGPass::Iterator DDGPass::begin() {
	
	return Util::createValueIteratorP<MapType>(_nodes.begin());
}

//DDGPass::IteratorConst DDGPass::begin() const {
//	
//}

void DDGPass::clearNodes(void) {
	
	for(auto const& i : _nodes) {
		delete i.second;
	}
	
	_nodes.clear();
} 

void DDGPass::computeDependencies(
		Instruction const& inst) const {
	
	NodeTypeConst&     instNode = (*this)[inst];
	Instruction const* pRefInst;
	
	// Iterate over all operands and insert only those in the predecessor set,
	// that are actually instructions
	for(Use const& i : inst.operands()) {
		if((pRefInst = dyn_cast<Instruction const>(&i))) {
			instNode.predecessors.insert(&(*this)[*pRefInst]);
		}
	}
}

DDGPass::Iterator DDGPass::end() {
	
	return Util::createValueIteratorP<MapType>(_nodes.end());
}

//DDGPass::IteratorConst DDGPass::end() const {
//	
//}

void DDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
}

DDGPass::NodeType& DDGPass::operator[](
		Instruction& inst) const {
	
	return *_nodes.at(&inst);
}

DDGPass::NodeTypeConst& DDGPass::operator[](
		Instruction const& inst) const {
	
	return *reinterpret_cast<NodeTypeConst*>(_nodes.at(&inst));
}

bool DDGPass::runOnFunction(
		Function& func) {
	
	// Make sure, the previous state gets forgotten
	clearNodes();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		_nodes[&i] = new NodeType(&i);
	}
	
	// Compute the data dependencies for each instruction
	for(Instruction const& i : Util::getInstructions(func)) {
		computeDependencies(i);
	}
	
	// Complete the graph
	Util::addSuccessors(*this);
	
	return false;
}
