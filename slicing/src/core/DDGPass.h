#pragma once

#include "Util.h"

#include "llvm/ADT/GraphTraits.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include <unordered_map>

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class DDGPass : public llvm::FunctionPass {
	
	public:
	
	typedef GenericNode<llvm::Instruction*>                         NodeType;
	typedef GenericNode<llvm::Instruction const*>                   NodeTypeConst;
	typedef std::unordered_map<llvm::Instruction const*, NodeType*> MapType;
	typedef LambdaIterator<MapType::iterator, NodeType>             Iterator;
	typedef LambdaIterator<MapType::iterator, NodeType const>       IteratorConst;
	
	static char ID;
	
	DDGPass() : llvm::FunctionPass(ID) {}
	~DDGPass();
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	
	virtual bool runOnFunction(llvm::Function &func) override;
	
	Iterator      begin();
	//IteratorConst begin() const;
	Iterator      end();
	//IteratorConst end() const;
	
	NodeType&      operator[](llvm::Instruction&       inst) const;
	NodeTypeConst& operator[](llvm::Instruction const& inst) const;
	
	private:
	
	MapType _nodes;
	
	void clearNodes(void);
	void computeDependencies(llvm::Instruction const& inst) const;
};

// GraphTraits specialization to apply standard graph algorithms to DDGs based
// on a node

template <> struct llvm::GraphTraits<DDGPass::NodeType*> :
	public GraphTraitsGenericNode<DDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<DDGPass::NodeType*>> :
	public GraphTraitsGenericNodeInverse<DDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<DDGPass::NodeTypeConst*> :
	public GraphTraitsGenericNode<DDGPass::NodeTypeConst::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<DDGPass::NodeTypeConst*>> :
	public GraphTraitsGenericNodeInverse<DDGPass::NodeTypeConst::InnerType> {};

// GraphTraits specialization to apply standard graph algorithms to DDGs based
// on the DDGPass

template <> struct llvm::GraphTraits<DDGPass*> :
	public llvm::GraphTraits<DDGPass::NodeType*> {

	typedef DDGPass::Iterator nodes_iterator;
	
	// The entry node is a (pseudo) random node
	static NodeType* getEntryNode(DDGPass* pDDG) {
		return &(*pDDG->begin());
	}

	static nodes_iterator nodes_begin(DDGPass* pDDG) {
		return pDDG->begin();
	}

	static nodes_iterator nodes_end(DDGPass* pDDG) {
		return pDDG->end();
	}
};
