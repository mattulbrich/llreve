/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include <cstdint>
#include <functional>

class BitArray {
	
	public:
	
	unsigned int const size;
	
	BitArray(unsigned int size);
	~BitArray();
	
	BitArray& invert(void);
	BitArray& reset (void);
	
	bool operator==(BitArray const& rhs) const;
	bool operator!=(BitArray const& rhs) const;
	
	BitArray& operator&=(BitArray const& rhs);
	BitArray& operator|=(BitArray const& rhs);
	BitArray& operator^=(BitArray const& rhs);
	
	bool operator[](unsigned int pos) const;
	
	private:
	
	typedef unsigned long long SlotType;
	
	static constexpr unsigned int _slotSize = sizeof(SlotType) * 8;
	
	unsigned int const _intCount;
	SlotType* const    _data;
	
	BitArray& performBinaryOp(
		BitArray const&                                    rhs,
		std::function<SlotType(SlotType, SlotType)> const& op);
};
