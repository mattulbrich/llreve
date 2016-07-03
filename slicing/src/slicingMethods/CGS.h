#pragma once

#include "core/Criterion.h"
#include "SlicingMethod.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

class CGS : public SlicingMethod {
	
	public:
	
	CGS(ModulePtr program, llvm::raw_ostream& ostream = llvm::outs()) :
		SlicingMethod(program), _ostream(ostream) {}
	
	virtual ModulePtr computeSlice(CriterionPtr c) override;
	
	private:
	
	llvm::raw_ostream& _ostream;
	
	llvm::Function& getFirstNonSpecialFunction(llvm::Module& module);
};
