#pragma once

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

#include <type_traits>
#include <iostream>

#define UTIL_REMOVE_REF(t)       typename std::remove_reference<t>::type
#define UTIL_IT_FROM_TYPE(t)     decltype(std::declval<t>().begin())
#define UTIL_REF_TYPE_FROM_IT(t) decltype(std::declval<t>().operator*())
#define UTIL_CHILD_IT_FROM_IT(t) UTIL_IT_FROM_TYPE(UTIL_REF_TYPE_FROM_IT(t))
#define UTIL_TYPE_FROM_IT(t)     UTIL_REMOVE_REF(UTIL_REF_TYPE_FROM_IT(t))

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

template <class ItType>
class IteratorPair {
	
	public:
	
	IteratorPair(
		ItType itBegin,
		ItType itEnd) : _itBegin(itBegin), _itEnd(itEnd) {}
	
	ItType begin(void) {return _itBegin;}
	ItType end  (void) {return _itEnd;}
	
	private:
	
	ItType _itBegin;
	ItType _itEnd;
};

namespace Util {
	
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
	IteratorPair<NestedInputIterator<FunctionType>> getInstructions(
			FunctionType& func) {
		
		return IteratorPair<NestedInputIterator<FunctionType>>(
			getInstItBegin(func), getInstItEnd<FunctionType>());
	}
}
