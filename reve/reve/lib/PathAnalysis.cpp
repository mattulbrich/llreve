#include "PathAnalysis.h"

#include "Helper.h"
#include "InferMarks.h"

#include <iostream>

#include "llvm/IR/Constants.h"

using std::make_shared;
using std::unique_ptr;
using smt::Op;
using smt::stringExpr;
using std::set;
using smt::SharedSMTRef;
using smt::SMTRef;
using smt::SMTExpr;

char PathAnalysis::ID = 0;

bool PathAnalysis::runOnFunction(llvm::Function & /*unused*/) {
    if (InferMarks) {
        auto markedBlocks = getAnalysis<InferMarksAnalysis>().getBlockMarkMap();
        PathsMap = findPaths(markedBlocks);
    } else {
        auto markedBlocks = getAnalysis<MarkAnalysis>().getBlockMarkMap();
        PathsMap = findPaths(markedBlocks);
    }
    return false;
}

PathMap findPaths(BidirBlockMarkMap markedBlocks) {
    PathMap MyPaths;
    for (auto BBTuple : markedBlocks.MarkToBlocksMap) {
        // don't start at return instructäions
        if (BBTuple.first != EXIT_MARK && BBTuple.first != UNREACHABLE_MARK) {
            for (auto BB : BBTuple.second) {
                const std::map<int, Paths> NewPaths =
                    findPathsStartingAt(BBTuple.first, BB, markedBlocks);
                for (auto NewPathTuple : NewPaths) {
                    MyPaths[BBTuple.first][NewPathTuple.first].insert(
                        MyPaths[BBTuple.first][NewPathTuple.first].end(),
                        NewPathTuple.second.begin(), NewPathTuple.second.end());
                }
            }
        }
    }
    return MyPaths;
}

PathMap PathAnalysis::getPathMap() const { return PathsMap; }

void PathAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<MarkAnalysis>();
    AU.addRequired<InferMarksAnalysis>();
}

std::map<int, Paths> findPathsStartingAt(int For, llvm::BasicBlock *BB,
                                         BidirBlockMarkMap BidirBlockMarkMap) {
    std::map<int, Paths> FoundPaths;
    const auto MyPaths = traverse(BB, BidirBlockMarkMap, true, {});
    for (auto &PathIt : MyPaths) {
        set<int> Indices;
        if (PathIt.empty()) {
            Indices.insert(EXIT_MARK);
        } else {
            Indices = BidirBlockMarkMap.BlockToMarksMap.at(PathIt.back().Block);
        }
        for (auto Index : Indices) {
            // don't allow paths to the same node but with a different mark
            if (PathIt.empty() ||
                !(PathIt.back().Block == BB && Index != For)) {
                FoundPaths[Index].push_back(Path(BB, PathIt));
            }
        }
    }
    return FoundPaths;
}

Paths_ traverse(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks,
                bool First, std::set<const llvm::BasicBlock *> Visited) {
    std::set<std::string> Constructed;
    if ((!First && isMarked(*BB, MarkedBlocks)) ||
        isReturn(*BB, MarkedBlocks)) {
        Paths_ MyPaths;
        MyPaths.push_back(Path_());
        return MyPaths;
    }
    if (Visited.find(BB) != Visited.end()) {
        logErrorData("Found cycle at block:\n", *BB);
        exit(1);
    }
    Visited.insert(BB);
    auto TermInst = BB->getTerminator();
    if (auto BranchInst = llvm::dyn_cast<llvm::BranchInst>(TermInst)) {
        if (BranchInst->isUnconditional()) {
            auto TraversedPaths = traverse(BranchInst->getSuccessor(0),
                                           MarkedBlocks, false, Visited);
            for (auto &P : TraversedPaths) {
                P.insert(P.begin(), Edge(nullptr, BranchInst->getSuccessor(0)));
            }
            return TraversedPaths;
        }
        auto TraversedPaths0 =
            traverse(BranchInst->getSuccessor(0), MarkedBlocks, false, Visited);
        auto TraversedPaths1 =
            traverse(BranchInst->getSuccessor(1), MarkedBlocks, false, Visited);
        for (auto &P : TraversedPaths0) {
            P.insert(P.begin(), Edge(make_shared<const BooleanCondition>(
                                         BranchInst->getCondition(), true),
                                     BranchInst->getSuccessor(0)));
        }
        for (auto &P : TraversedPaths1) {
            P.insert(P.begin(), Edge(make_shared<const BooleanCondition>(
                                         BranchInst->getCondition(), false),
                                     BranchInst->getSuccessor(1)));
        }
        TraversedPaths0.insert(TraversedPaths0.end(), TraversedPaths1.begin(),
                               TraversedPaths1.end());
        return TraversedPaths0;
    }
    if (auto SwitchInst = llvm::dyn_cast<llvm::SwitchInst>(TermInst)) {
        Paths_ TraversedPaths;
        std::vector<int64_t> Vals;
        for (auto Case : SwitchInst->cases()) {
            int64_t Val = Case.getCaseValue()->getSExtValue();
            Vals.push_back(Val);
            auto TraversedPaths_ =
                traverse(Case.getCaseSuccessor(), MarkedBlocks, false, Visited);
            for (auto &P : TraversedPaths_) {
                P.insert(P.begin(), Edge(make_shared<const SwitchCondition>(
                                             SwitchInst->getCondition(), Val),
                                         Case.getCaseSuccessor()));
            }
            TraversedPaths.insert(TraversedPaths.end(), TraversedPaths_.begin(),
                                  TraversedPaths_.end());
        }
        // Handle default case separately
        auto TraversedPaths_ = traverse(SwitchInst->getDefaultDest(),
                                        MarkedBlocks, false, Visited);
        for (auto &P : TraversedPaths_) {
            P.insert(P.begin(), Edge(make_shared<const SwitchDefault>(
                                         SwitchInst->getCondition(), Vals),
                                     SwitchInst->getDefaultDest()));
        }
        TraversedPaths.insert(TraversedPaths.end(), TraversedPaths_.begin(),
                              TraversedPaths_.end());

        return TraversedPaths;
    }
    logWarningData("Unknown terminator\n", *TermInst);
    return Paths_();
}

bool isMarked(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) {
    const auto Marks = MarkedBlocks.BlockToMarksMap.find(&BB);
    if (Marks != MarkedBlocks.BlockToMarksMap.end()) {
        return !(Marks->second.empty());
    }
    return false;
}

bool isReturn(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) {
    const auto Marks = MarkedBlocks.BlockToMarksMap.find(&BB);
    if (Marks != MarkedBlocks.BlockToMarksMap.end()) {
        return Marks->second.find(EXIT_MARK) != Marks->second.end() ||
               llvm::isa<llvm::UnreachableInst>(BB.getTerminator());
    }
    return false;
}

llvm::BasicBlock *lastBlock(Path Path) {
    if (Path.Edges.empty()) {
        return Path.Start;
    }
    return Path.Edges.back().Block;
}

Condition::~Condition() = default;

SMTRef BooleanCondition::toSmt() const {
    SMTRef result = instrNameOrVal(Cond, Cond->getType());
    if (True) {
        return result;
    }
    return makeUnaryOp("not", std::move(result));
}

SMTRef SwitchCondition::toSmt() const {
    return makeBinOp("=", instrNameOrVal(Cond, Cond->getType()),
                     stringExpr(std::to_string(Val)));
}

SMTRef SwitchDefault::toSmt() const {
    std::vector<SharedSMTRef> StringVals;
    for (auto Val : Vals) {
        StringVals.push_back(stringExpr(std::to_string(Val)));
    }
    StringVals.push_back(instrNameOrVal(Cond, Cond->getType()));
    return llvm::make_unique<Op>("distinct", StringVals);
}

static llvm::RegisterPass<PathAnalysis>
    RegisterMarkAnalysis("path-analysis", "Path Analysis", true, true);
