#pragma once

#include "Util.h"

#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include <unordered_map>

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class CDGPass : public llvm::FunctionPass {
	
	public:
	
	typedef GenericNode<llvm::Instruction*>                         NodeType;
	typedef GenericNode<llvm::Instruction const*>                   NodeTypeConst;
	typedef std::unordered_map<llvm::Instruction const*, NodeType*> MapType;
	typedef LambdaIterator<MapType::iterator, NodeType>             Iterator;
	typedef LambdaIterator<MapType::iterator, NodeType const>       IteratorConst;
	
	static char ID;
	
	CDGPass() : llvm::FunctionPass(ID) {}
	~CDGPass();
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	
	virtual bool runOnFunction(llvm::Function &func) override;
	
	Iterator      begin();
	//IteratorConst begin() const;
	Iterator      end();
	//IteratorConst end() const;
	
	NodeType& getRoot(void) const;
	
	NodeType&      operator[](llvm::Instruction&       inst) const;
	NodeTypeConst& operator[](llvm::Instruction const& inst) const;
	
	private:
	
	MapType _nodes;
	
	void clearNodes(void);
	
	void computeDependency(
		llvm::BasicBlock&              bb,
		llvm::PostDominatorTree const& pdt);
};

// GraphTraits specialization to apply standard graph algorithms to CDGs based
// on a node

template <> struct llvm::GraphTraits<CDGPass::NodeType*> :
	public GraphTraitsGenericNode<CDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<CDGPass::NodeType*>> :
	public GraphTraitsGenericNodeInverse<CDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<CDGPass::NodeTypeConst*> :
	public GraphTraitsGenericNode<CDGPass::NodeTypeConst::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<CDGPass::NodeTypeConst*>> :
	public GraphTraitsGenericNodeInverse<CDGPass::NodeTypeConst::InnerType> {};

// GraphTraits specialization to apply standard graph algorithms to CDGs based
// on the CDGPass

template <> struct llvm::GraphTraits<CDGPass*> :
	public llvm::GraphTraits<CDGPass::NodeType*> {

	typedef CDGPass::Iterator nodes_iterator;
	
	static NodeType* getEntryNode(CDGPass* pCDG) {
		return &pCDG->getRoot();
	}

	static nodes_iterator nodes_begin(CDGPass* pCDG) {
		return pCDG->begin();
	}

	static nodes_iterator nodes_end(CDGPass* pCDG) {
		return pCDG->end();
	}
};
