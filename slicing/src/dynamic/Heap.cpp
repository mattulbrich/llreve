#include "Heap.h"

#include <cassert>
#include <cstdint>

#include <iostream>

using namespace std;
using namespace llvm;

Heap::AddressType Heap::alloc(
		OwnerType   const owner, 
		AddressType const byteCount) {
	
	AddressType const address = _curFreeAddress;
	
	_curFreeAddress += byteCount;
	
	if(_reservedByOwner.find(owner) == _reservedByOwner.end()) {
		_reservedByOwner.emplace(owner, unordered_set<AddressType>());
	}
	
	_reservedByAddress[address] = byteCount;
	_reservedByOwner  [owner].insert(address);
	
	return address;
}

Heap::SizeType Heap::assertMemory(
		AddressType const address,
		SizeType    const bitCount) {
	
	assert(bitCount > 0 && bitCount % 8 == 0 && "Invalid integer size");
	
	SizeType const byteCount = bitCount / 8;
	
	for(AddressType i = address; i < address + byteCount; i++) {
		if(_memory.find(i) == _memory.end()) {
			_memory.insert({i, {0, nullptr}});
		}
	}
	
	return byteCount;
}

Heap::SizeType Heap::computeSegmentCount(
		SizeType const byteCount) {
	
	return byteCount % 8 ? byteCount / 8 + 1 : byteCount / 8;
}

Heap::OwnerType Heap::createOwner(void) {
	
	return _curFreeOwner++;
}

Heap::AddressType Heap::free(
		AddressType const address) {
	
	if(_reservedByAddress.find(address) != _reservedByAddress.end()) {
		
		AddressType const byteCount = _reservedByAddress[address];
		_reservedByAddress.erase(address);
		
		return byteCount;
		
	} else {
		
		return 0;
	}
}

Heap::AddressType Heap::freeAll(
		OwnerType const owner) {
	
	AddressType byteCount = 0;
	
	if(_reservedByOwner.find(owner) != _reservedByOwner.end()) {
		for(AddressType const i : _reservedByOwner[owner]) {
			byteCount += free(i);
		}
	}
	
	return byteCount;
}

bool Heap::isLittleEndian(void) const {
	
	return _littleEndian;
}

bool Heap::isBigEndian(void) const {
	
	return !_littleEndian;
}

void Heap::iterateSegments(
		AddressType const address,
		SizeType    const byteCount,
		bool        const startAtLowAddress,
		function<void(AddressType, SizeType, SizeType)> const& lambda) {
	
	SizeType const segCount  = computeSegmentCount(byteCount);
	SizeType       bytesLeft = byteCount;
	
	for(SizeType i = 0; i < segCount; i++) {
		
		SizeType const segSize = bytesLeft > 8 ? 8 : bytesLeft;
		
		lambda(
			address + (startAtLowAddress ? i * 8 : byteCount - segSize - i * 8),
			segSize,
			i);
		
		bytesLeft -= 8;
	}
}

void Heap::iterateSegmentSlots(
		AddressType const address,
		SizeType    const byteCount,
		bool        const startAtLowAddress,
		function<void(SlotType&)> const& lambda) {
	
	for(SizeType i = 0; i < byteCount; i++) {
		lambda(_memory[address + (startAtLowAddress ? i : byteCount - 1 - i)]);
	}
}

APInt Heap::readInt(
		AddressType const  address,
		SizeType    const  bitCount,
		DependencySetType* pDataDepSet) {
	
	SizeType const byteCount = assertMemory(address, bitCount);
	SizeType const segCount  = computeSegmentCount(byteCount);
	
	std::vector<SegmentType> segments(segCount);
	
	iterateSegments(
		address, byteCount, _littleEndian,
		[&](AddressType start, SizeType length, SizeType index) {
			segments[index] = readIntSegment(start, length);
		});
	
	if(pDataDepSet) {
		for(SizeType i = 0; i < byteCount; i++) {
			pDataDepSet->insert(_memory[address + i].second);
		}
	}
	
	// Create a new APInt based on the previously filled segment array
	return
		APInt(bitCount, static_cast<unsigned int>(segCount), segments.data());
}

Heap::SegmentType Heap::readIntSegment(
		AddressType const address,
		SizeType    const byteCount) {
	
	SegmentType result = 0;
	bool        first  = true;
	
	iterateSegmentSlots(
		address, byteCount, !_littleEndian,
		[&](SlotType& slot) {
			if(!first) {
				result <<= 8;
			}
			result += slot.first;
			first   = false;
		});
	
	return result;
}

void Heap::writeInt(
		AddressType const  address,
		APInt       const  value,
		Instruction const& modifyingInst) {
	
	SizeType    const  byteCount =
		assertMemory(address, static_cast<SizeType>(value.getBitWidth()));
	SegmentType const* segments  = value.getRawData();
	
	iterateSegments(
		address, byteCount, _littleEndian,
		[&](AddressType start, SizeType length, SizeType index) {
			writeIntSegment(start, segments[index], length, modifyingInst);
		});
}

void Heap::writeIntSegment(
		AddressType const  address,
		SegmentType        segment,
		SizeType    const  byteCount,
		Instruction const& modifyingInst) {
	
	iterateSegmentSlots(
		address, byteCount, _littleEndian,
		[&](SlotType& slot) {
			slot.first  = segment & UINT64_C(0xFF);
			slot.second = &modifyingInst;
			segment   >>= 8;
		});
}

Heap::ElementType Heap::operator[](
		AddressType const address) const {
	
	return
		_memory.find(address) != _memory.end() ? _memory.at(address).first : 0;
}
