#include "FixNamesPass.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

#include "llvm/IR/DebugInfoMetadata.h"

#include "preprocessing/AddVariableNamePass.h"

#include <sstream>

using namespace llvm;
using namespace std;

char FixNamesPass::ID = 0;

bool FixNamesPass::runOnModule(llvm::Module &module){
	int b = 0;
	int i = 0;
	for (Function& function: module) {
		for (BasicBlock& block: function) {
			stringstream ss;
			ss << "block." << ++b;
			block.setName(Twine(ss.str()));
			for (Instruction& instruction:block) {
				if (!instruction.getType()->isVoidTy()) {
					stringstream ss;
					DIVariable* name = AddVariableNamePass::getSrcVariable(instruction);
					if (name) {
						ss << name->getName().str();
					} else {
						ss << "_";
					}
					ss << "." << ++i;
					instruction.setName(Twine(ss.str()));
				}
			}
		}
	}
	return true;
}
