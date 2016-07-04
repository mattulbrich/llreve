#pragma once

#include "Interpreter.h"

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include <list>
#include <unordered_map>

class LinearizedFunction {
	
	public:
	
	llvm::Function const& func;
	
	LinearizedFunction(llvm::Function const& func);
	~LinearizedFunction(void);
	
	unsigned int getInstructionCount(void)          const;
	void         print(llvm::raw_ostream& _ostream) const;
	
	llvm::Instruction const& operator[](unsigned int const       index) const;
	unsigned int             operator[](llvm::Instruction const& inst)  const;
	
	private:
	
	std::unordered_map<llvm::Instruction const*, unsigned int> _mapInstToInt;
	llvm::Instruction const**                                  _mapIntToInst;
};

class DRM {
	
	public:
	
	LinearizedFunction const& linFunc;
	
	DRM(LinearizedFunction const& linFunc, uint64_t const cex[]);
	~DRM(void);
	
	llvm::APInt const& computeSlice(llvm::APInt const& apriori);
	void               print       (llvm::raw_ostream& _ostream) const;
	
	private:
	
	unsigned int  const _instCount;
	llvm::APInt** const _matrix;
	llvm::APInt         _accumulator;
};

class AddCtrlDepToDRMPass {
	
};
