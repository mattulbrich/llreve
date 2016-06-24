#pragma once

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

#include <unordered_map>

class LinearizedFunction {
	
	public:
	
	LinearizedFunction(llvm::Function& func);
	~LinearizedFunction(void);
	
	llvm::Instruction& operator[](unsigned int const       index) const;
	unsigned int       operator[](llvm::Instruction const& inst)  const;
	
	private:
	
	std::unordered_map<llvm::Instruction const*, unsigned int> mapInstToInt;
	llvm::Instruction**                                        mapIntToInst;
};

class DRM {
	
	public:
	
	// TODO: DRM(LinearizedFunction, CounterExample);
	// Use the Algorithm for DRM creation
	
	BitArray const& computeSlice(BitArray const& apriori);
	
	private:
	
	LinearizedFunction const& func;
	BitArray const*           matrix;
	BitArray                  accumulator;
};