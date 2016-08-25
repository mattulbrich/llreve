/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SliceCandidate.h"

#include "core/SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/Interval.h"


#include <set>
#include <vector>

// class DfsInfo {
// public:
// 	int pathCount;
// 	bool visited;
// 	bool done;
// };


class Info {
public:
	int incomingPaths;
	int outgoingPaths;

	Info(){
		incomingPaths = 0;
		outgoingPaths = 0;
	}
};



class HelperPass: public llvm::FunctionPass {

public:
	static char ID;
	static int markCounter;
	HelperPass():llvm::FunctionPass(ID) {
		assert(false && "Internal Error: This pass can not be created with default constructor.");
	}

	HelperPass(SliceCandidate* candidate):llvm::FunctionPass(ID), candidate(candidate) {
		
	}

	virtual ~HelperPass(){

	}

	virtual bool runOnFunction(llvm::Function &fun) override {
		this->blockMarkMap = std::make_unique<BidirBlockMarkMap>();

		llvm::BasicBlock* entry = &fun.getEntryBlock();
		llvm::BasicBlock* exit = getAnalysis<llvm::UnifyFunctionExitNodes>().ReturnBlock;

		addMark(ENTRY_MARK, entry);
		addMark(EXIT_MARK, exit);

		llvm::LoopInfo &loopInfo =
		    getAnalysis<llvm::LoopInfoWrapperPass>().getLoopInfo();
		for (auto loop : loopInfo) {
			addMark(++markCounter,loop->getHeader());
		}

		int diff;
		do {
			diff = optimizeMark(entry, exit, fun);	
		} while (diff > 0);
			
		candidate->setMarkedBlocksProgram(std::move(blockMarkMap));
		return false; // Did not modify CFG
	}

	/**
	 * Places a new mark to reduce the number of paths.
	 * Returns the difference in the number of paths before and after the mark was inserted.
	 */
	virtual int optimizeMark(llvm::BasicBlock* entry, llvm::BasicBlock* exit, llvm::Function &fun) {
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
			std::cout << block.getName().str() << " noMark: " << pathsNoMark << " Mark: " << pathsMark << std::endl;
			int diff = pathsNoMark - pathsMark;
			if (maxDiff < diff) {
				maxDiff = diff;
				maxBlock = &block;
			}
		}

		if (maxDiff >= 0) {
			assert(maxBlock && !hasMark(maxBlock));
			addMark(++markCounter, maxBlock);
			std::cout << "Inserted mark " << markCounter << " with maxDiff: " << maxDiff << " at " << maxBlock->getName().str() << std::endl;
		}
		
		
		return maxDiff;
	}

	// virtual void inverseMarkToMarkDFS(llvm::BasicBlock* start, std::function<void (DfsInfo& info)> lambda){
	// 	markToMarkDFS(start, lambda, true);
	// }

	// virtual void markToMarkDFS(llvm::BasicBlock* start, std::function<void (DfsInfo& info)> lambda, bool inverse = false){
	// 	std::stack<llvm::BasicBlock*> worklist;
	// 	std::map<llvm::BasicBlock*, DfsInfo> infos;

	// 	worklist.push(start);
	// 	while (!worklist.empty()) {
	// 		llvm::BasicBlock* next = worklist.top();
	// 		//Do not pop, as we want to visit the element again, when all childes are visited

	// 		auto& info = infos[next];
	// 		if (info.done) {
	// 			worklist.pop();
	// 		} else {
	// 			if (!info.visited) {
	// 				info.visited = true;

	// 				if (hasMark(next)) {
	// 					info.done = true;
	// 					worklist.pop();
	// 					info.pathCount = 1;
	// 				} else {
	// 					auto succ =  next->getTerminator()->successors();
	// 					for (auto it = succ.begin(); it != succ.end(); it++){
	// 						worklist.push(*it);						
	// 					}
	// 				}
	// 			} else {
	// 				info.done = true;
	// 				worklist.pop();
	// 				info.pathCount = 0;

	// 				auto successors =  next->getTerminator()->successors();
	// 				for (auto it = successors.begin(); it != successors.end(); it++){
	// 					BasicBlock* successor = *it;
	// 					info.pathCount += infos[successor].pathCount;
	// 				}				
	// 			}
	// 		} 
	// 	}
	// }

	virtual bool hasMark(llvm::BasicBlock* block){
		return blockMarkMap->BlockToMarksMap.find(block) != blockMarkMap->BlockToMarksMap.end();
	}

	virtual void addMark(int mark, llvm::BasicBlock* block){
		assert(block);
		blockMarkMap->BlockToMarksMap[block].insert(mark);
		blockMarkMap->MarkToBlocksMap[mark].insert(block);
	}

	virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override{
		AU.setPreservesAll();
		AU.addRequired<llvm::UnifyFunctionExitNodes>();
		AU.addRequired<llvm::LoopInfoWrapperPass>();
	}

private:
	SliceCandidate* candidate;
	std::unique_ptr<BidirBlockMarkMap> blockMarkMap;
};

char HelperPass::ID = 0;
int HelperPass::markCounter = 0;
static llvm::RegisterPass<HelperPass>
    RegisterHelperPasskAnalysis("mark-analysis-helper-pass", "Mark Analysis Helper Pass", true, true);

SliceCandidate::SliceCandidate(ModulePtr program, CriterionPtr criterion):
		program(program), criterion(criterion) { 			
	this->candidate = llvm::CloneModule(program.get(), valueMap);
}

SliceCandidate::SliceCandidate() {

}

ModulePtr SliceCandidate::getProgram(){
	return this->program;
}

ModulePtr SliceCandidate::getCandidate(){
	return this->candidate;
}

CriterionPtr SliceCandidate::getCriterion(){
	return this->criterion;
}

bool SliceCandidate::validate(){
	return SliceCandidateValidation::validate(this) == ValidationResult::valid;
}

void SliceCandidate::computeMarks(){
	llvm::legacy::PassManager PM;
	PM.add(llvm::createLoopSimplifyPass());
	PM.add(llvm::createUnifyFunctionExitNodesPass());	
	PM.add(new HelperPass(this));

	//PM.run(*this->getCandidate());
	//this->markedBlocksCandidate = std::move(markedBlocksProgram);
	PM.run(*this->getProgram());

	// {
	// 	llvm::legacy::PassManager PM;
	// 	PM.add(llvm::createCFGSimplificationPass());	
	// 	PM.run(*this->getProgram());
	// }

	std::map<int, std::set<llvm::BasicBlock *>> marksToBlocks;
	auto& MarkToBlockMapProgram = this->markedBlocksProgram->MarkToBlocksMap;
	for (auto it = MarkToBlockMapProgram.begin(); it != MarkToBlockMapProgram.end(); it++) {
		int mark = it->first;
		std::set<llvm::BasicBlock*> candidateBlocks;
		for (llvm::BasicBlock* programBlock:it->second) {
			std::cout << "Mark " << mark << " at " << programBlock->getName().str() << std::endl;
			if (llvm::BasicBlock* candidateBlock = llvm::dyn_cast<llvm::BasicBlock>(valueMap[programBlock])) {
				candidateBlocks.insert(candidateBlock);
			} else {
				std::cout << "Warning: Unmatched Marks!" << std::endl;
			}
		}
		marksToBlocks[mark] = candidateBlocks;
	}

	std::map<llvm::BasicBlock *, std::set<int>> blocksToMarks;
	auto& blockToMarkProgram = this->markedBlocksProgram->BlockToMarksMap;
	for (auto it = blockToMarkProgram.begin(); it != blockToMarkProgram.end(); it++) {
		llvm::BasicBlock* programBlock = it->first;
		if (llvm::BasicBlock* candidateBlock = llvm::dyn_cast<llvm::BasicBlock>(valueMap[programBlock])) {
			blocksToMarks[candidateBlock] = it->second;
		} else {
			std::cout << "Warning: Unmatched Marks!" << std::endl;
		}
	}

	this->markedBlocksCandidate = std::make_unique<BidirBlockMarkMap>(blocksToMarks,marksToBlocks);
}

void SliceCandidate::setMarkedBlocksProgram(std::unique_ptr<BidirBlockMarkMap> markMap){
	this->markedBlocksProgram = std::move(markMap);
}


BidirBlockMarkMap* SliceCandidate::getMarkedBlocksProgram(){
	return markedBlocksProgram.get();
}

BidirBlockMarkMap* SliceCandidate::getMarkedBlocksCandidate(){
	return markedBlocksCandidate.get();
}


SliceCandidatePtr SliceCandidate::copy(){
	SliceCandidatePtr clone (new SliceCandidate());
	
	llvm::ValueToValueMapTy programToProgramClone;
	clone->program = llvm::CloneModule(program.get(), programToProgramClone);

	llvm::ValueToValueMapTy candidateToCandidateClone;
	clone->candidate = llvm::CloneModule(candidate.get(), candidateToCandidateClone);

	for (auto it = this->valueMap.begin(); it != this->valueMap.end(); it++) {
		auto programValue = programToProgramClone[it->first];

		if (it->second != nullptr) {
			auto candidateValue = candidateToCandidateClone[it->second];
			if (programValue != nullptr && candidateValue != nullptr) {
				clone->valueMap[programValue] = candidateValue;
			}
		}
	}

	clone->criterion = criterion;
	return clone;
}

