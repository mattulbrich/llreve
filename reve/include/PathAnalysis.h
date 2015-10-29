#ifndef PATHANALYSIS_H
#define PATHANALYSIS_H

#include "SMT.h"

#include "llvm/IR/PassManager.h"

class Edge {
  public:
    Edge(SMTRef Condition_, llvm::BasicBlock *Block_)
        : Condition(Condition_), Block(Block_) {}
    SMTRef Condition;
    llvm::BasicBlock *Block;
};

class Path {
  public:
    Path(llvm::BasicBlock *Start_, std::vector<Edge> Edges_)
        : Start(Start_), Edges(Edges_) {}
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
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
    static void *ID() { return static_cast<void *>(&PassID); }

  private:
    static char PassID;
};

auto findPaths(llvm::BasicBlock * BB,
               std::map<int, llvm::BasicBlock *> MarkedBlocks)
    -> std::map<int, Paths>;

auto traverse(llvm::BasicBlock *BB,
              std::map<int, llvm::BasicBlock *> MarkedBlocks, bool first)
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
