#ifndef PATHANALYSIS_H
#define PATHANALYSIS_H

#include "SMT.h"

#include "llvm/IR/PassManager.h"

class Edge {
  public:
    Edge(SMTRef Condition, llvm::BasicBlock *Block)
        : Condition(std::move(Condition)), Block(std::move(Block)) {}
    SMTRef Condition;
    llvm::BasicBlock *Block;
};

class Path {
  public:
    Path(llvm::BasicBlock *Start, std::vector<Edge> Edges)
        : Start(std::move(Start)), Edges(std::move(Edges)) {}
    llvm::BasicBlock *Start;
    std::vector<Edge> Edges;
};

using Path_ = std::vector<Edge>;
using Paths_ = std::vector<Path_>;
using Paths = std::vector<Path>;
using PathMap = std::map<int, std::map<int, Paths>>;

class PathAnalysis {
  public:
    typedef PathMap Result;
    static llvm::StringRef name() { return "PathAnalysis"; }
    static void *ID() { return static_cast<void *>(&PassID); }
    Result run(llvm::Function &F, llvm::FunctionAnalysisManager *AM);

  private:
    static char PassID;
};

auto findPaths(llvm::BasicBlock *BB,
               std::map<int, llvm::BasicBlock *> MarkedBlocks)
    -> std::map<int, Paths>;

auto traverse(llvm::BasicBlock *BB,
              std::map<int, llvm::BasicBlock *> MarkedBlocks, bool First)
    -> Paths_;

auto isTerminator(llvm::BasicBlock *BB,
                  std::map<int, llvm::BasicBlock *> MarkedBlocks) -> bool;

template <class Key, class T>
std::_Rb_tree_iterator<std::pair<const Key, T>>
reverseLookup(T Val, std::map<Key, T> Map) {
    return std::find_if(
        Map.begin(), Map.end(),
        [=](const std::pair<Key, T> &P) { return P.second == Val; });
}

#endif // PATHANALYSIS_H
