/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "MarkAnalysisPass.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/Constants.h"

#include "util/misc.h"

#include "MarkAnalysis.h"

#include <iostream>

class Info {
public:
	int incomingPaths;
	int outgoingPaths;

	Info(){
		incomingPaths = 0;
		outgoingPaths = 0;
	}
};

std::string MarkAnalysisPass::FUNCTION_NAME = "__mark";
char MarkAnalysisPass::ID = 0;

bool MarkAnalysisPass::runOnModule(llvm::Module &module) {
	findMarks(module);

	for (llvm::Function& function: module) {
		if (!function.isDeclaration() && !Util::isSpecialFunction(function)) {
			llvm::BasicBlock* entry = &function.getEntryBlock();
			llvm::BasicBlock* exit = getAnalysis<llvm::UnifyFunctionExitNodes>(function).ReturnBlock;
			marks.insert(entry);
			marks.insert(exit);

			addLoopMarks(function);

			int diff;
			do {
				diff = optimizeMark(entry, exit, function);	
			} while (diff > 10);
		}
	}
		
	return true; // changes llvm
}

void MarkAnalysisPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
	AU.setPreservesAll();
	AU.addRequired<llvm::UnifyFunctionExitNodes>();
	AU.addRequired<llvm::LoopInfoWrapperPass>();
}

void MarkAnalysisPass::findMarks(llvm::Module &module) {
	llvm::Function& markFunction = getMarkFunction(module);
	for (auto user = markFunction.user_begin(); user != markFunction.user_end(); ++user) {
		if (llvm::CallInst* callInst = llvm::dyn_cast<llvm::CallInst>(*user)) {
			marks.insert(callInst->getParent());			
			int markNumber = 0;

			llvm::Value* parameter = callInst->getArgOperand(0);
			if (auto constInt = llvm::dyn_cast<llvm::ConstantInt>(parameter)) {
				markNumber = static_cast<int>(constInt->getValue().getSExtValue());
			}

			if (markNumber > markCounter) {
				markCounter = markNumber;
			}
		}
	}
}

void MarkAnalysisPass::addLoopMarks(llvm::Function &function) {
	llvm::LoopInfo &loopInfo =
	    getAnalysis<llvm::LoopInfoWrapperPass>(function).getLoopInfo();
	for (auto loop : loopInfo) {
		llvm::BasicBlock* loopHeader = loop->getHeader();
		addMark(loopHeader);
	}
}

/**
 * Places a new mark to reduce the number of paths.
 * Returns the difference in the number of paths before and after the mark was inserted.
 */
int MarkAnalysisPass::optimizeMark(llvm::BasicBlock* entry, llvm::BasicBlock* exit, llvm::Function &fun) {
	std::map<llvm::BasicBlock*, Info> infos;
	
	for (auto blockIt = llvm::po_begin(entry);blockIt != llvm::po_end(entry); ++blockIt) {
		llvm::BasicBlock& block = **blockIt;
		Info& info = infos[&block];
		if (hasMark(&block)) {
			info.outgoingPaths = 1;
		} else {
			for (auto succ = llvm::succ_begin(&block); succ != llvm::succ_end(&block); ++succ) {					
				Info& succInfo = infos[*succ];
				if (succInfo.outgoingPaths == 0) {
					assert(hasMark(*succ));
					succInfo.outgoingPaths = 1;
				}					
			
				info.outgoingPaths += succInfo.outgoingPaths;
			}
		}
	}
	

	for (auto blockIt = llvm::ipo_begin(exit);blockIt != llvm::ipo_end(exit); ++blockIt) {
		llvm::BasicBlock& block = **blockIt;
		Info& info = infos[&block];
		if (hasMark(&block)) {
			info.incomingPaths = 1;
		} else {
			info.incomingPaths = 0;
			for (auto pred = llvm::pred_begin(&block); pred != llvm::pred_end(&block); ++pred) {					
				Info& predInfo = infos[*pred];
				if (predInfo.incomingPaths == 0) {
					assert(hasMark(*pred));
					predInfo.incomingPaths = 1;
				}					
			
				info.incomingPaths += predInfo.incomingPaths;
			}
		}
	}

	
	int maxDiff = -1;
	llvm::BasicBlock* maxBlock = nullptr;
	for (llvm::BasicBlock& block:fun) {
		Info& info = infos[&block];
		int pathsNoMark = info.incomingPaths * info.outgoingPaths;
		int pathsMark = info.incomingPaths + info.outgoingPaths;
		int diff = pathsNoMark - pathsMark;
		if (maxDiff < diff) {
			maxDiff = diff;
			maxBlock = &block;
		}
	}

	if (maxDiff >= 0) {
		assert(maxBlock && !hasMark(maxBlock));
		addMark(maxBlock);
	}
	
	return maxDiff;
}

bool MarkAnalysisPass::hasMark(llvm::BasicBlock* block){
	return this->marks.find(block) != this->marks.end();
}

void MarkAnalysisPass::addMark(llvm::BasicBlock* block){	
	addMark(++markCounter, block);
}

void MarkAnalysisPass::addMark(int markNumber, llvm::BasicBlock* block){
	auto result = this->marks.insert(block);
	bool existed = !result.second;
	if (!existed) {
		llvm::Function& markFunction = getMarkFunction(*block->getModule());

		auto intType = llvm::IntegerType::get(block->getContext(), 32);
		auto markConstant = llvm::ConstantInt::getSigned(intType, markNumber);

		std::vector<llvm::Value*> parameter;
		parameter.push_back(markConstant);
		llvm::ArrayRef<llvm::Value*> parameterRef(parameter);

		llvm::CallInst::Create(&markFunction, parameterRef, "", block->getFirstNonPHI());
	}
}

llvm::Function& MarkAnalysisPass::getMarkFunction(llvm::Module& module){
	llvm::Function* function = module.getFunction(llvm::StringRef(MarkAnalysisPass::FUNCTION_NAME));
	if (!function) {
		std::vector<llvm::Type*> parameter;
		parameter.push_back(llvm::IntegerType::get(module.getContext(), 32));
		llvm::ArrayRef<llvm::Type*> parameterRef(parameter);
		llvm::Type* returnType = llvm::Type::getVoidTy(module.getContext());
		llvm::FunctionType* functionType = llvm::FunctionType::get(returnType, parameterRef, false);

		function = llvm::Function::Create(functionType,
			llvm::GlobalValue::LinkageTypes::ExternalLinkage,
			llvm::Twine(MarkAnalysisPass::FUNCTION_NAME),
			&module);
	}

	return *function;
}
