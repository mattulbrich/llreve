#include "ExplicitAssignPass.h"

#include "core/Util.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Verifier.h"


#include "llvm/Support/raw_ostream.h"


using namespace llvm;
using namespace std;

char ExplicitAssignPass::ID = 0;
string ExplicitAssignPass::FUNCTION_NAME = "__identity";

bool ExplicitAssignPass::runOnModule(llvm::Module &module){
	idFunctionMap_.clear();

	for (Function& function: module) {
		for (BasicBlock& block: function) {
			for (auto it = block.begin(); it != block.end(); it++){
				Instruction& instruction = *it;
				if (StoreInst* store = dyn_cast<StoreInst>(&instruction)) {
					Value* value = store->getValueOperand();
					if (noDublicateAssignment(value)) {
						Type*  type  = value->getType();

						Function& idFunction = getID(*type, *function.getParent());
						vector<Value*> parameter;
						parameter.push_back(value);
						ArrayRef<Value*> parameterRef(parameter);
						CallInst* assignment = CallInst::Create(&idFunction, parameterRef, "", store);

						assert(store->getOperand(0) == value && "Internal error: The value operand is not operand 0 anymore.");
						store->setOperand(0, assignment);
					}
				}
			}
		}
	}

	bool hasError = llvm::verifyModule(module, &errs());
	assert(!hasError && "Internal Error: ExplicitAssignPass produced module, which ist not a valid llvm program.");
	return true;
}

bool ExplicitAssignPass::noDublicateAssignment(Value* value) {
	if ((isa<Instruction>(value) && !isa<LoadInst>(value)) || isa<Argument>(value)) {
		return false;
	} else {
		return true;
	}
}

llvm::Function& ExplicitAssignPass::getID(llvm::Type& type, llvm::Module& module){
	llvm::Function* function = nullptr;

	vector<Type*> parameter;
	parameter.push_back(&type);
	ArrayRef<Type*> parameterRef(parameter);
	llvm::FunctionType* functionType = FunctionType::get(&type, parameterRef, false);

	auto it = idFunctionMap_.find(functionType);

	if (it != idFunctionMap_.end()) {
		function = it->second;
	} else {
		function = Function::Create(functionType,
			llvm::GlobalValue::LinkageTypes::ExternalLinkage,
			Twine(ExplicitAssignPass::FUNCTION_NAME),
			&module);
		idFunctionMap_.insert(pair<FunctionType*, Function*>(functionType, function));
	}

	return *function;
}

