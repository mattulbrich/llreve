#include "AddVariableNamePass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include <stack>

using namespace llvm;

char AddVariableNamePass::ID = 0;

bool AddVariableNamePass::runOnFunction(llvm::Function &function) {
	for (BasicBlock& block : function) {
		for (Instruction& instruction : block) {
			if (DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&instruction)) {
				if (Instruction* ssaVar = dyn_cast<Instruction>(DbgValue->getValue())) {
					DIVariable* srcVariable = DbgValue->getVariable();
					setSrcVariable(*ssaVar, srcVariable);

					std::stack<Instruction*> visit;
					visit.push(ssaVar);
					while(!visit.empty()) {
						Instruction* next = visit.top();
						visit.pop();
						for (User* user: ssaVar->users()) {
							if (isa<PHINode>(user)) {
								if (Instruction* phiVar = dyn_cast<Instruction>(user)) {
									//if (srcVariable = )
									setSrcVariable(*phiVar, srcVariable);
									//TODO: traverse all phi nodes and annotate with variable name
									//visit.push(phiVar);
								}
							}
						}
					}
				}
			}
		}
	}
	return true;
}

void AddVariableNamePass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {

}

DIVariable* AddVariableNamePass::getSrcVariable(llvm::Instruction& instruction) {
	return nullptr;
}


DIVariable* AddVariableNamePass::findSrcVariable(const llvm::Instruction& instruction){
	for(const llvm::Instruction& dbgInfo: *instruction.getParent()){
		if (const DbgValueInst* DbgValue = dyn_cast<DbgValueInst>(&dbgInfo)) {
			if (DbgValue->getValue() == &instruction) {
				return DbgValue->getVariable();;
			}
		}
	}
	return nullptr;
}

void AddVariableNamePass::setSrcVariable(Instruction& instruction, DIVariable* variable){
	LLVMContext& context = instruction.getContext();	
	instruction.setMetadata("srcVariable", variable);
}