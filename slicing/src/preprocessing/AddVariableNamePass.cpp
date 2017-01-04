/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "AddVariableNamePass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"

#include <stack>
#include <set>

using namespace llvm;

char AddVariableNamePass::ID = 0;
std::string AddVariableNamePass::srcVariableMetadataName = "srcVariable";


void AddVariableNamePass::propagateNoVariable(Instruction* instruction){
	std::stack<Instruction*> visit;
	visit.push(instruction);
	while(!visit.empty()) {
		Instruction* next = visit.top();
		visit.pop();

		auto insertRes = hasNoName->insert(next);
		bool didInsert = insertRes.second;
		if (didInsert) {
			setSrcVariable(*instruction, nullptr);
			for (User* user: next->users()) {
				if (auto phi = dyn_cast<PHINode>(user)) {
					visit.push(phi);
				}
			}
		}
	}
}

void AddVariableNamePass::setAndPropagate(DIVariable* srcVariable, Instruction* instruction){
	setSrcVariable(*instruction, srcVariable);

	std::stack<Instruction*> visit;
	visit.push(instruction);
	while(!visit.empty()) {
		Instruction* next = visit.top();
		visit.pop();
		for (User* user: next->users()) {
			if (auto phi = dyn_cast<PHINode>(user)) {
				DIVariable* presentSrcVariable = getSrcVariable(*phi);
				bool containedInHasNoName = (hasNoName->find(phi) != hasNoName->end());
				if (!containedInHasNoName) {
					if (presentSrcVariable == nullptr) {
						setSrcVariable(*phi, srcVariable);
						visit.push(phi);
					}
				}
			}
		}
	}
}

bool AddVariableNamePass::runOnFunction(llvm::Function &function) {
	std::set<Instruction*> hasNoName;
	this->hasNoName = &hasNoName;

	Instruction* previousInstruction = nullptr;
	//propagate variables
	for (BasicBlock& block : function) {
		for (Instruction& instruction : block) {
			if (DbgValueInst* dbgValueInst = dyn_cast<DbgValueInst>(&instruction)) {
				if (auto dbgValue = dbgValueInst->getValue()) {
					if (Instruction* ssaVar = dyn_cast<Instruction>(dbgValue)) {
						if (ssaVar == previousInstruction) { //correct debug information is imediatly after the instruction
							DIVariable* srcVariable = dbgValueInst->getVariable();
							setAndPropagate(srcVariable, ssaVar);
						}
					}
				}
			}
			previousInstruction = &instruction;
		}
	}

	//clean up: remove variables if phi uses different src variables
	for (BasicBlock& block : function) {
		for (Instruction& instruction : block) {
			if (auto phi = dyn_cast<PHINode>(&instruction)) {
				DIVariable* srcVariable = getSrcVariable(*phi);
				if (srcVariable != nullptr) {
					for (unsigned int i = 0; i < phi->getNumIncomingValues();i++) {
						if (Instruction* defInstruction = dyn_cast<Instruction>(phi->getIncomingValue(i))) {
							if (srcVariable != getSrcVariable(*defInstruction)) {
								propagateNoVariable(phi);
								break;
							}
						}
					}
				}
			}
		}
	}

	return true;
}

DIVariable* AddVariableNamePass::getSrcVariable(llvm::Instruction& instruction) {
	auto metadata = instruction.getMetadata(srcVariableMetadataName);
	if (metadata) {
		if (DIVariable* result = dyn_cast<DIVariable>(metadata)) {
			return result;
		}
	}

	return nullptr;

}


void AddVariableNamePass::setSrcVariable(Instruction& instruction, DIVariable* variable){
	instruction.setMetadata(srcVariableMetadataName, variable);
}
