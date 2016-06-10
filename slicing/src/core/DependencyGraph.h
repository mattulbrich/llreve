#pragma once

#include "Util.h"

#include "llvm/ADT/DepthFirstIterator.h"

#include <unordered_map>

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
template <class ContentType> class DependencyGraph {
	
	public:
	
	typedef GenericNode<ContentType*>                                  NodeType;
	typedef GenericNode<ContentType const*>                            NodeTypeConst;
	typedef std::unordered_map<ContentType const*, NodeType*>          MapType;
	typedef LambdaIterator<typename MapType::iterator, NodeType>       Iterator;
	typedef LambdaIterator<typename MapType::iterator, NodeType const> IteratorConst;
	
	~DependencyGraph() {
		clearNodes();
	}
	
	Iterator begin() {
		return Util::createValueIteratorP<MapType>(_nodes.begin());
	}
	
	Iterator end() {
		return Util::createValueIteratorP<MapType>(_nodes.end());
	}
	
	// TODO: 
	//IteratorConst begin() const;
	//IteratorConst end() const;
	
	template <class InputSetType, class OutputSetType> void getInfluencedNodes(
			InputSetType&  initNodes,
			OutputSetType& result) const {
		
		NodeType pseudoRoot;
		
		for(ContentType* i : initNodes) {
			pseudoRoot.successors.insert(&(*this)[i]);
		}
		
		// The pseudo root will not be part of the result set
		for(auto i : llvm::depth_first_ext(&pseudoRoot, result)) {}
	}
	
	template <class InputSetType, class OutputSetType> void getInfluencingNodes(
			InputSetType&  initNodes,
			OutputSetType& result) const {
		
		NodeType pseudoRoot;
		
		for(ContentType* i : initNodes) {
			pseudoRoot.predecessors.insert(&(*this)[i]);
		}
		
		// The pseudo root will not be part of the result set
		for(auto i : llvm::inverse_depth_first_ext(&pseudoRoot, result)) {}
	}
	
	NodeType& operator[](ContentType& content) const {
		return *_nodes.at(&content);
	}
	
	NodeTypeConst& operator[](ContentType const& content) const {
		return *reinterpret_cast<NodeTypeConst*>(_nodes.at(&content));
	}
	
	protected:
	
	void clearNodes(void) {
		for(auto const& i : _nodes) {delete i.second;}
		_nodes.clear();
	}
	
	void createNode(ContentType* pContent) {
		_nodes[pContent] = new NodeType(pContent);
	}
	
	NodeType& operator[](ContentType* pContent) const {
		return *_nodes.at(pContent);
	}
	
	private:
	
	MapType _nodes;
};

// GraphTraits specialization to apply standard graph algorithms to DDGs based
// on the DDGPass

template <class ContentType> struct GraphTraitsDependencyGraph {

	typedef typename DependencyGraph<ContentType>::Iterator nodes_iterator;
	
	static nodes_iterator nodes_begin(DependencyGraph<ContentType>* pGraph) {
		return pGraph->begin();
	}

	static nodes_iterator nodes_end(DependencyGraph<ContentType>* pGraph) {
		return pGraph->end();
	}
};
