#include "PathAnalysis.h"

#include <iostream>
#include "MarkAnalysis.h"
#include "SExpr.h"

#include "llvm/IR/Instructions.h"

char PathAnalysis::PassID;

PathMap PathAnalysis::run(llvm::Function &F,
                          llvm::FunctionAnalysisManager *AM) {
    PathMap MyPaths;
    auto MarkedBlocks = AM->getResult<MarkAnalysis>(F);
    for (auto BB : MarkedBlocks) {
        // don't start at return instructions
        if (BB.second != -2) {
            std::map<llvm::BasicBlock *, Paths> NewPaths =
                findPaths(BB.first, MarkedBlocks);
            MyPaths.insert(make_pair(BB.first, std::move(NewPaths)));
        }
    }
    return MyPaths;
}

std::map<llvm::BasicBlock *, Paths>
findPaths(llvm::BasicBlock *BB,
          std::map<llvm::BasicBlock *, int> MarkedBlocks) {
    std::map<llvm::BasicBlock *, Paths> FoundPaths;
    auto MyPaths = traverse(BB, MarkedBlocks, true);
    for (auto &Path : MyPaths) {
        auto It = FoundPaths.find(Path.back().Block);
        if (It == FoundPaths.end()) {
            FoundPaths.insert(std::make_pair(Path.back().Block, Paths()));
            It = FoundPaths.find(Path.back().Block);
        }
        It->second.push_back(std::move(Path));
    }
    return FoundPaths;
}

Paths traverse(llvm::BasicBlock *BB,
               std::map<llvm::BasicBlock *, int> MarkedBlocks, bool first) {
    if (!first && MarkedBlocks.find(BB) != MarkedBlocks.end()) {
        Paths MyPaths;
        MyPaths.push_back(Path());
        return MyPaths;
    }
    auto TermInst = BB->getTerminator();
    if (auto BranchInst = llvm::dyn_cast<llvm::BranchInst>(TermInst)) {
        if (BranchInst->isUnconditional()) {
            auto TraversedPaths =
                traverse(BranchInst->getSuccessor(0), MarkedBlocks, false);
            for (auto &P : TraversedPaths) {
                P.insert(P.begin(), Edge(nullptr, BranchInst->getSuccessor(0)));
            }
            return TraversedPaths;
        }
        auto TraversedPaths_0 =
            traverse(BranchInst->getSuccessor(0), MarkedBlocks, false);
        auto TraversedPaths_1 =
            traverse(BranchInst->getSuccessor(1), MarkedBlocks, false);
        for (auto &P : TraversedPaths_0) {
            P.insert(P.begin(),
                     Edge(name(BranchInst->getCondition()->getName()),
                          BranchInst->getSuccessor(0)));
        }
        for (auto &P : TraversedPaths_1) {
            P.insert(P.begin(),
                     Edge(makeUnaryOp("not", name(BranchInst->getCondition()->getName())),
                          BranchInst->getSuccessor(1)));
        }
        for (auto &Path : TraversedPaths_1) {
            TraversedPaths_0.push_back(std::move(Path));
        }
        return TraversedPaths_0;
    }
    llvm::errs() << "Unknown terminator\n";
    TermInst->print(llvm::errs());
    llvm::errs() << "\n";
    return Paths();
}
