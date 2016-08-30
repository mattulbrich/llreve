// *** ADDED BY HEADER FIXUP ***
#include <istream>
#include <iterator>
#include <utility>
// *** END ***
#pragma once

#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Value.h"

#include <iomanip>
#include <iostream>
#include <sstream>
#include <type_traits>
#include <unordered_set>

#define UTIL_NULL_REF(t) *static_cast<t*>(nullptr);

#define UTIL_REMOVE_POINTER(t)   typename std::remove_pointer<t>::type
#define UTIL_REMOVE_REF(t)       typename std::remove_reference<t>::type
#define UTIL_IT_FROM_TYPE(t)     decltype(std::declval<t>().begin())
#define UTIL_REF_TYPE_FROM_IT(t) decltype(std::declval<t>().operator*())
#define UTIL_CHILD_IT_FROM_IT(t) UTIL_IT_FROM_TYPE(UTIL_REF_TYPE_FROM_IT(t))
#define UTIL_TYPE_FROM_IT(t)     UTIL_REMOVE_REF(UTIL_REF_TYPE_FROM_IT(t))

#define UTIL_UNUSED(x) (void)(x);

template <class TopLevelType>
class NestedInputIterator :
	public std::iterator<
		std::input_iterator_tag,
		UTIL_TYPE_FROM_IT(UTIL_CHILD_IT_FROM_IT(UTIL_IT_FROM_TYPE(TopLevelType)))> {
	
	typedef UTIL_IT_FROM_TYPE(TopLevelType)     Level1ItType;
	typedef UTIL_CHILD_IT_FROM_IT(Level1ItType) Level2ItType;
	typedef UTIL_TYPE_FROM_IT(Level2ItType)     ElementType;
	
	public:
	
	NestedInputIterator(void) : _endReached(true) {}
	
	NestedInputIterator(
			TopLevelType& topLevel) : _endReached(false) {
		
		_itL1    = topLevel.begin();
		_itL1End = topLevel.end();
		
		moveToNextElement();
	}
	
	NestedInputIterator(
			NestedInputIterator const& it) :
		_endReached(it._endReached),
		_itL1      (it._itL1),
		_itL1End   (it._itL1End),
		_itL2      (it._itL2),
		_itL2End   (it._itL2End) {}
	
	NestedInputIterator& operator++() {
		
		if(_endReached) return *this;
		
		++_itL2;
		
		if(_itL2 == _itL2End) {
			++_itL1;
			if(_itL1 == _itL1End) {
				_endReached = true;
			} else {
				moveToNextElement();
			}
		}
		
		return *this;
	}
	
	NestedInputIterator operator++(int) {
		
		NestedInputIterator tmp(*this);
		operator++();
		
		return tmp;
	}
	
	bool operator==(
			NestedInputIterator const& rhs) {
		
		return !_endReached && !rhs._endReached ?
			&(*_itL2) == &(*rhs._itL2) :
			_endReached && rhs._endReached;
	}
	
	bool operator!=(
			NestedInputIterator const& rhs) {
		
		return !operator==(rhs);
	}
	
	ElementType& operator*() {
		
		return *_itL2;
	}
	
	private:
	
	bool         _endReached;
	Level1ItType _itL1;
	Level1ItType _itL1End;
	Level2ItType _itL2;
	Level2ItType _itL2End;
	
	void moveToNextElement(void) {
		
		_itL2    = (*_itL1).begin();
		_itL2End = (*_itL1).end();
	}
};

template <class ValueType>
class SingleValueIterator :
	public std::iterator<std::forward_iterator_tag, ValueType> {
	
	public:
	
	SingleValueIterator(void) :
		_endReached(true),
		_pValue    (NULL) {}
	
	SingleValueIterator(
			ValueType& value) :
		_endReached(false),
		_pValue    (&value) {}
	
	SingleValueIterator(
			SingleValueIterator const& it) :
		_endReached(it._endReached),
		_pValue    (it._pValue) {}
	
	SingleValueIterator& operator++() {
		
		_endReached = true;
		
		return *this;
	}
	
	SingleValueIterator operator++(int) {
		
		SingleValueIterator tmp(*this);
		operator++();
		
		return tmp;
	}
	
	bool operator==(
			SingleValueIterator const& rhs) {
		
		return !_endReached && !rhs._endReached ?
			_pValue == rhs._pValue :
			_endReached && rhs._endReached;
	}
	
	bool operator!=(
			SingleValueIterator const& rhs) {
		
		return !operator==(rhs);
	}
	
	ValueType& operator*() {
		
		return *_pValue;
	}
	
	private:
	
	bool       _endReached;
	ValueType* _pValue;
};

template <class ItType, class ValueType>
class LambdaIterator :
	public std::iterator<std::forward_iterator_tag, ValueType> {
	
	public:
	
	typedef UTIL_REF_TYPE_FROM_IT(ItType)                  LambdaArgType;
	typedef ValueType&                                     LambdaReturnType;
	typedef std::function<LambdaReturnType(LambdaArgType)> LambdaType;
	
	LambdaIterator(void) : _refIt() {}
	
	LambdaIterator(
		ItType const& it,
		LambdaType    lambdaExpr) : _refIt(it), _lambdaExpr(lambdaExpr) {}
	
	LambdaIterator(
			LambdaIterator const& it) :
		_refIt     (it._refIt),
		_lambdaExpr(it._lambdaExpr) {}
	
	LambdaIterator& operator++() {
		
		++_refIt;
		
		return *this;
	}
	
	LambdaIterator operator++(int) {
		
		LambdaIterator tmp(*this);
		operator++();
		
		return tmp;
	}
	
	bool operator==(
			LambdaIterator const& rhs) {
		
		return _refIt == rhs._refIt;
	}
	
	bool operator!=(
			LambdaIterator const& rhs) {
		
		return _refIt != rhs._refIt;
	}
	
	ValueType& operator*() {
		
		return _lambdaExpr(*_refIt);
	}
	
	private:
	
	ItType     _refIt;
	LambdaType _lambdaExpr;
};

template <class NodeType> class GenericNode {
	
	public:
	
	typedef NodeType                                                      InnerType;
	typedef typename std::unordered_set<GenericNode<NodeType>*>::iterator Iterator;
	
	NodeType                                   innerNode;
	std::unordered_set<GenericNode<NodeType>*> predecessors;
	std::unordered_set<GenericNode<NodeType>*> successors;
	
	// Only available if the InnerType provides a default constructor
	GenericNode(void) : innerNode() {}
	
	GenericNode(
		NodeType innerNode) : innerNode(innerNode) {}
	
	NodeType& operator*() {
		
		return innerNode;
	}
};

template <class InnerType> struct GraphTraitsGenericNode {
	
	typedef GenericNode<InnerType>      NodeType;
	typedef typename NodeType::Iterator ChildIteratorType;

	static NodeType* getEntryNode(NodeType* pNode) {
		return pNode;
	}

	static ChildIteratorType child_begin(NodeType* pNode) {
		return pNode->successors.begin();
	}

	static ChildIteratorType child_end(NodeType* pNode) {
		return pNode->successors.end();
	}
};

template <class InnerType> struct GraphTraitsGenericNodeInverse {
	
	typedef GenericNode<InnerType>      NodeType;
	typedef typename NodeType::Iterator ChildIteratorType;

	static NodeType* getEntryNode(llvm::Inverse<NodeType*> pNode) {
		return pNode.Graph;
	}

	static ChildIteratorType child_begin(NodeType* pNode) {
		return pNode->predecessors.begin();
	}

	static ChildIteratorType child_end(NodeType* pNode) {
		return pNode->predecessors.end();
	}
};

namespace Util {

template <
	class MapType,
	class ValueType = typename MapType::key_type,
	class ItType    = typename MapType::iterator>
static LambdaIterator<ItType, ValueType> createKeyIterator(
		ItType it) {
	
	return LambdaIterator<ItType, ValueType>(
		it,
		[](UTIL_REF_TYPE_FROM_IT(ItType) i) -> ValueType& {
			return *i.first;
		});
}

template <
	class MapType,
	class ValueType = UTIL_REMOVE_POINTER(typename MapType::key_type),
	class ItType    = typename MapType::iterator>
static LambdaIterator<ItType, ValueType> createKeyIteratorP(
		ItType it) {
	
	return LambdaIterator<ItType, ValueType>(
		it,
		[](UTIL_REF_TYPE_FROM_IT(ItType) i) -> ValueType& {
			return *i.first;
		});
}

template <
	class MapType,
	class ValueType = typename MapType::mapped_type,
	class ItType    = typename MapType::iterator>
static LambdaIterator<ItType, ValueType> createValueIterator(
		ItType it) {
	
	return LambdaIterator<ItType, ValueType>(
		it,
		[](UTIL_REF_TYPE_FROM_IT(ItType) i) -> ValueType& {
			return *i.second;
		});
}

template <
	class MapType,
	class ValueType = UTIL_REMOVE_POINTER(typename MapType::mapped_type),
	class ItType    = typename MapType::iterator>
static LambdaIterator<ItType, ValueType> createValueIteratorP(
		ItType it) {
	
	return LambdaIterator<ItType, ValueType>(
		it,
		[](UTIL_REF_TYPE_FROM_IT(ItType) i) -> ValueType& {
			return *i.second;
		});
}

template <class FunctionType>
NestedInputIterator<FunctionType> getInstItBegin(
		FunctionType& func) {
	
	return NestedInputIterator<FunctionType>(func);
}

template <class FunctionType>
NestedInputIterator<FunctionType> getInstItEnd(void) {
	
	return NestedInputIterator<FunctionType>();
}

template <class FunctionType>
llvm::iterator_range<NestedInputIterator<FunctionType>> getInstructions(
		FunctionType& func) {
	
	return llvm::make_range(
		getInstItBegin(func), getInstItEnd<FunctionType>());
}

// Functions for graph completion

template <class GraphType, class GT = llvm::GraphTraits<GraphType*>>
llvm::iterator_range<typename GT::nodes_iterator> getNodes(
		GraphType& graph) {
	
	return llvm::make_range(GT::nodes_begin(&graph), GT::nodes_end(&graph));
}

template <class GraphType> void addPredecessors(
		GraphType& graph) {
	
	// 'i' will be a reference, 'j' a pointer to a 'GenericNode<>'
	for(auto& i : getNodes(graph)) {
		for(auto j : i.successors) {
			j->predecessors.insert(&i);
		}
	}
}

template <class GraphType> void addSuccessors(
		GraphType& graph) {
	
	// 'i' will be a reference, 'j' a pointer to a 'GenericNode<>'
	for(auto& i : getNodes(graph)) {
		for(auto j : i.predecessors) {
			j->successors.insert(&i);
		}
	}
}

template <class GraphType> void makeBidirectional(
		GraphType& graph) {
	
	addPredecessors(graph);
	addSuccessors(graph);
}

// Functions for easy LLVM value printing

std::string& toString(
	llvm::Value const& value,
	std::string&       str,
	bool const         isForDebug = false);

std::string toString(
	llvm::Value const& value,
	bool const         isForDebug = false);

template<class T> std::string toHexString(
		T   const decimalValue,
		int const digitCount = sizeof(T) * 2) {

	std::stringstream stream;
	
	stream << "0x" << std::setfill('0') << std::setw(digitCount) << std::hex <<
		decimalValue;
	
	return stream.str();
}

// Function for freeing the resources of an array including its elements

template <class ElementType> void deleteArrayDeep(
		ElementType** const array,
		unsigned long const length) {
	
	for(unsigned long i = 0; i < length; i++) {
		delete array[i];
	}
	
	delete [] array;
}

}
