#include "PathAnalysis.h"

#include "MarkAnalysis.h"
#include "SExpr.h"
#include <iostream>

#include "llvm/IR/Instructions.h"

char PathAnalysis::PassID;

PathMap PathAnalysis::run(llvm::Function &F,
                          llvm::FunctionAnalysisManager *AM) {
    PathMap MyPaths;
    auto MarkedBlocks = AM->getResult<MarkAnalysis>(F);
    for (auto BB : MarkedBlocks) {
        // don't start at return instructions
        if (BB.first != -2) {
            std::map<int, Paths> NewPaths = findPaths(BB.second, MarkedBlocks);
            MyPaths.insert(make_pair(BB.first, std::move(NewPaths)));
        }
    }

    // for (auto &MappedPaths : MyPaths) {
    //     llvm::errs() << "Paths for: " << MappedPaths.first << "\n";
    //     llvm::errs() << "\n";
    //     for (auto &Paths : MappedPaths.second) {
    //         llvm::errs() << "End node: " << Paths.first << "\n";
    //         for (auto &Path : Paths.second) {
    //             llvm::errs() << "Path\n";
    //             Path.Start->print(llvm::errs());
    //             llvm::errs() << "\n";
    //             for (auto &Edge : Path.Edges) {
    //                 if (Edge.Condition) {
    //                     std::cerr << *Edge.Condition->toSExpr();
    //                 }
    //                 Edge.Block->print(llvm::errs());
    //                 llvm::errs() << "\n";
    //             }
    //         }
    //     }
    // }

    return MyPaths;
}

std::map<int, Paths>
findPaths(llvm::BasicBlock *BB,
          std::map<int, llvm::BasicBlock *> MarkedBlocks) {
    std::map<int, Paths> FoundPaths;
    auto MyPaths = traverse(BB, MarkedBlocks, true);
    for (auto &PathIt : MyPaths) {
        auto Index = reverseLookup(PathIt.back().Block, MarkedBlocks);
        auto It = FoundPaths.find(Index->first);
        if (It == FoundPaths.end()) {
            FoundPaths.insert(std::make_pair(Index->first, Paths()));
            It = FoundPaths.find(Index->first);
        }
        It->second.push_back(Path(BB, std::move(PathIt)));
    }
    return FoundPaths;
}

Paths_ traverse(llvm::BasicBlock *BB,
               std::map<int, llvm::BasicBlock *> MarkedBlocks, bool first) {
    if (!first && isTerminator(BB, MarkedBlocks)) {
        Paths_ MyPaths;
        MyPaths.push_back(Path_());
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
            P.insert(
                P.begin(),
                Edge(makeUnaryOp("not",
                                 name(BranchInst->getCondition()->getName())),
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
    return Paths_();
}

bool isTerminator(llvm::BasicBlock *BB,
                  std::map<int, llvm::BasicBlock *> MarkedBlocks) {
    for (auto Pair : MarkedBlocks) {
        if (Pair.second == BB) {
            return true;
        }
    }
    return false;
}
