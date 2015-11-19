#include "PathAnalysis.h"

#include "SExpr.h"
#include <iostream>

#include "llvm/IR/Instructions.h"

char PathAnalysis::PassID;

PathMap PathAnalysis::run(llvm::Function &F,
                          llvm::FunctionAnalysisManager *AM) {
    PathMap MyPaths;
    auto BidirMarkBlockMap = AM->getResult<MarkAnalysis>(F);
    for (auto BBTuple : BidirMarkBlockMap.MarkToBlocksMap) {
        // don't start at return instructions
        if (BBTuple.first != -2) {
            for (auto BB : BBTuple.second) {
                std::map<int, Paths> NewPaths =
                    findPaths(BB, BidirMarkBlockMap);
                for (auto NewPathTuple : NewPaths) {
                    MyPaths[BBTuple.first][NewPathTuple.first].insert(
                        MyPaths[BBTuple.first][NewPathTuple.first].end(),
                        NewPathTuple.second.begin(), NewPathTuple.second.end());
                }
            }
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

std::map<int, Paths> findPaths(llvm::BasicBlock *BB,
                               BidirBlockMarkMap BidirBlockMarkMap) {
    std::map<int, Paths> FoundPaths;
    auto MyPaths = traverse(BB, BidirBlockMarkMap, true);
    for (auto &PathIt : MyPaths) {
        set<int> Indices;
        if (PathIt.empty()) {
            Indices.insert(-2);
        } else {
            Indices = BidirBlockMarkMap.BlockToMarksMap.at(PathIt.back().Block);
        }
        for (auto Index : Indices) {
            FoundPaths[Index].push_back(Path(BB, PathIt));
        }
    }
    return FoundPaths;
}

Paths_ traverse(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks,
                bool First) {
    if ((!First && isMarked(BB, MarkedBlocks)) || isReturn(BB, MarkedBlocks)) {
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
        auto TraversedPaths0 =
            traverse(BranchInst->getSuccessor(0), MarkedBlocks, false);
        auto TraversedPaths1 =
            traverse(BranchInst->getSuccessor(1), MarkedBlocks, false);
        for (auto &P : TraversedPaths0) {
            P.insert(P.begin(),
                     Edge(name(BranchInst->getCondition()->getName()),
                          BranchInst->getSuccessor(0)));
        }
        for (auto &P : TraversedPaths1) {
            P.insert(
                P.begin(),
                Edge(makeUnaryOp("not",
                                 name(BranchInst->getCondition()->getName())),
                     BranchInst->getSuccessor(1)));
        }
        for (auto &Path : TraversedPaths1) {
            TraversedPaths0.push_back(Path);
        }
        return TraversedPaths0;
    }
    llvm::errs() << "Unknown terminator\n";
    TermInst->print(llvm::errs());
    llvm::errs() << "\n";
    return Paths_();
}

bool isMarked(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks) {
    auto Marks = MarkedBlocks.BlockToMarksMap.find(BB);
    if (Marks != MarkedBlocks.BlockToMarksMap.end()) {
        return !(Marks->second.empty());
    }
    return false;
}

bool isReturn(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks) {
    auto Marks = MarkedBlocks.BlockToMarksMap.find(BB);
    if (Marks != MarkedBlocks.BlockToMarksMap.end()) {
        return Marks->second.find(-2) != Marks->second.end();
    }
    return false;
}
