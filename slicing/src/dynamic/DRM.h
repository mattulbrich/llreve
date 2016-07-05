#pragma once

#include "Interpreter.h"

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
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
	void               print       (llvm::raw_ostream& out) const;
	
	private:
	
	unsigned int  const _instCount;
	llvm::APInt** const _matrix;
	llvm::APInt         _accumulator;
	
	static llvm::APInt const* findNode(
		std::list<llvm::APInt const*> const& elements,
		llvm::APInt                   const& ref);
	
	void printReachability(
		llvm::APInt const& row,
		llvm::raw_ostream& out) const;
};

class CtrlDepExtractionPass : public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	CtrlDepExtractionPass(
			LinearizedFunction const& linFunc,
			llvm::Instruction  const* dependencies[]) :
		llvm::FunctionPass(ID),
		_linFunc          (linFunc),
		_dependencies     (dependencies) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction   (llvm::Function      &func)     override;
	
	private:
	
	LinearizedFunction        const& _linFunc;
	llvm::Instruction const** const  _dependencies;
};
