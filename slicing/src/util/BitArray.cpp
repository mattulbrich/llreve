#include "BitArray.h"

#include <stdexcept>

using namespace std;

BitArray::BitArray(
		unsigned int size) :
	size     (size),
	_intCount(size % _slotSize == 0 ? size / _slotSize : size / _slotSize + 1),
	_data    (new SlotType[_intCount]) {}

BitArray::~BitArray() {
	
	delete [] _data;
}

BitArray& BitArray::invert(void) {
	
	for(unsigned int i = 0; i < _intCount; i++) {
		_data[i] = ~_data[i];
	}
	
	return *this;
}

BitArray& BitArray::reset(void) {
	
	for(unsigned int i = 0; i < _intCount; i++) {
		_data[i] = 0;
	}
	
	return *this;
}

BitArray& BitArray::performBinaryOp(
		BitArray const&                               rhs,
		function<SlotType(SlotType, SlotType)> const& op) {
	
	if(size != rhs.size) {
		throw range_error("Bit arrays of different size");
	}
	
	for(unsigned int i = 0; i < _intCount; i++) {
		_data[i] = op(_data[i], rhs._data[i]);
	}
	
	return *this;
}

bool BitArray::operator==(
		BitArray const& rhs) const {
	
	if(size != rhs.size) {
		return false;
	}
	
	for(unsigned int i = 0; i < _intCount; i++) {
		if(_data[i] != rhs._data[i]) return false;
	}
	
	return true;
}

bool BitArray::operator!=(
		BitArray const& rhs) const {
	
	return !(*this == rhs);
}

BitArray& BitArray::operator&=(
		BitArray const& rhs) {
	
	return performBinaryOp(
		rhs, [](SlotType a, SlotType b) {return a & b;});
}

BitArray& BitArray::operator|=(
		BitArray const& rhs) {
	
	return performBinaryOp(
		rhs, [](SlotType a, SlotType b) {return a | b;});
}

BitArray& BitArray::operator^=(
		BitArray const& rhs) {
	
	return performBinaryOp(
		rhs, [](SlotType a, SlotType b) {return a ^ b;});
}

bool BitArray::operator[](
		unsigned int pos) const {
	
	if(pos >= size) {
		throw range_error("Position out of range");
	}
	
	return (_data[pos / _slotSize] & (pos % _slotSize << 1)) > 0;
}
