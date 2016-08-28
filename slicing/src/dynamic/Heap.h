#pragma once

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Instruction.h"

#include <functional>
#include <unordered_map>
#include <unordered_set>

class Heap {
	
	public:
	
	typedef uint64_t                                     AddressType;
	typedef uint8_t                                      ElementType;
	typedef uint16_t                                     SizeType;
	typedef uint16_t                                     OwnerType;
	typedef std::unordered_set<llvm::Instruction const*> DependencySetType;
	
	Heap(bool const littleEndian = true) :
		_littleEndian(littleEndian), _curFreeAddress(1024), _curFreeOwner(0) {}
	
	OwnerType createOwner(void);
	
	AddressType alloc(OwnerType const owner, AddressType const byteCount);
	AddressType free(AddressType const address);
	AddressType freeAll(OwnerType const owner);
	
	llvm::APInt readInt(
		AddressType const  address,
		SizeType    const  bitCount,
		DependencySetType* pDataDepSet = nullptr);
	
	void writeInt(
		AddressType       const  address,
		llvm::APInt       const  value,
		llvm::Instruction const& modifyingInst);
	
	bool isLittleEndian(void) const;
	bool isBigEndian   (void) const;
	
	ElementType operator[](AddressType const address) const;
	
	private:
	
	typedef std::pair<ElementType, llvm::Instruction const*> SlotType;
	typedef uint64_t                                         SegmentType;
	
	bool const                                   _littleEndian;
	AddressType                                  _curFreeAddress;
	OwnerType                                    _curFreeOwner;
	std::unordered_map<AddressType, SlotType>    _memory;
	std::unordered_map<AddressType, AddressType> _reservedByAddress;
	std::unordered_map<OwnerType, std::unordered_set<AddressType>>
		_reservedByOwner;
	
	// Returns the byte count
	SizeType assertMemory(
		AddressType const address, SizeType const bitCount);
	
	SizeType computeSegmentCount(SizeType const byteCount);
	
	void iterateSegments(
		AddressType const  address,
		SizeType    const  byteCount,
		bool        const  startAtLowAddress,
		std::function<void(AddressType, SizeType, SizeType)> const& lambda);
	void iterateSegmentSlots(
		AddressType const address,
		SizeType    const byteCount,
		bool        const startAtLowAddress,
		std::function<void(SlotType&)> const& lambda);
	
	SegmentType readIntSegment(
		AddressType const address, SizeType const byteCount);
	
	void writeIntSegment(
		AddressType       const  address,
		SegmentType              segment,
		SizeType          const  byteCount,
		llvm::Instruction const& modifyingInst);
};
