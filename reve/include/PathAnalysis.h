#ifndef PATHANALYSIS_H
#define PATHANALYSIS_H

#include "SMT.h"

#include "llvm/IR/PassManager.h"

class Edge {
  public:
    Edge(SMTRef Condition_, llvm::BasicBlock *Block_)
        : Condition(std::move(Condition_)), Block(Block_) {}
    SMTRef Condition;
    llvm::BasicBlock *Block;
};

using Path = std::vector<Edge>;
using Paths = std::vector<Path>;
using PathMap =
    std::map<llvm::BasicBlock *, std::map<llvm::BasicBlock *, Paths>>;

class PathAnalysis {
  public:
    typedef PathMap Result;
    static llvm::StringRef name() { return "PathAnalysis"; }
    Result run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
    static void *ID() { return static_cast<void *>(&PassID); }

  private:
    static char PassID;
};

auto findPaths(llvm::BasicBlock *,
               std::map<llvm::BasicBlock *, int> MarkedBlocks)
    -> std::map<llvm::BasicBlock *, Paths>;

auto traverse(llvm::BasicBlock *BB,
              std::map<llvm::BasicBlock *, int> MarkedBlocks, bool first)
    -> Paths;
#endif // PATHANALYSIS_H
