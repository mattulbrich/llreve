#ifndef PATHANALYSIS_H
#define PATHANALYSIS_H

#include "SMT.h"
#include "MarkAnalysis.h"

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

auto lastBlock(Path Path) -> llvm::BasicBlock*;

auto findPaths(int For, llvm::BasicBlock *BB,
               BidirBlockMarkMap MarkedBlocks)
    -> std::map<int, Paths>;

auto traverse(llvm::BasicBlock *BB,
              BidirBlockMarkMap MarkedBlocks, bool First)
    -> Paths_;

auto isMarked(llvm::BasicBlock *BB,
              BidirBlockMarkMap MarkedBlocks) -> bool;

auto isReturn(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks) -> bool;

#endif // PATHANALYSIS_H
