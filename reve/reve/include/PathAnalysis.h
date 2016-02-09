#pragma once

#include "SMT.h"
#include "MarkAnalysis.h"

#include "llvm/IR/PassManager.h"

class Condition {
  public:
    virtual smt::SMTRef toSmt() const = 0;
    virtual ~Condition();
};

class Edge {
  public:
    Edge(std::shared_ptr<const Condition> Cond, llvm::BasicBlock *Block)
        : Cond(std::move(Cond)), Block(std::move(Block)) {}
    std::shared_ptr<const Condition> Cond;
    llvm::BasicBlock *Block;
};

class Path {
  public:
    Path(llvm::BasicBlock *Start, std::vector<Edge> Edges)
        : Start(std::move(Start)), Edges(std::move(Edges)) {}
    llvm::BasicBlock *Start;
    std::vector<Edge> Edges;
};

class BooleanCondition : public Condition {
  public:
    BooleanCondition(const llvm::Value *Cond, const bool True)
        : Cond(std::move(Cond)), True(std::move(True)) {}
    const llvm::Value *const Cond;
    const bool True;
    smt::SMTRef toSmt() const override;
};

class SwitchCondition : public Condition {
  public:
    SwitchCondition(const llvm::Value *Cond, int64_t Val)
        : Cond(std::move(Cond)), Val(std::move(Val)) {}
    const llvm::Value *const Cond;
    const int64_t Val;
    smt::SMTRef toSmt() const override;
};

class SwitchDefault : public Condition {
  public:
    SwitchDefault(const llvm::Value *Cond, std::vector<int64_t> Vals)
        : Cond(std::move(Cond)), Vals(std::move(Vals)) {}
    const llvm::Value *const Cond;
    const std::vector<int64_t> Vals;
    smt::SMTRef toSmt() const override;
};

using Path_ = std::vector<Edge>;
using Paths_ = std::vector<Path_>;
using Paths = std::vector<Path>;
using PathMap = std::map<int, std::map<int, Paths>>;

class PathAnalysis {
  public:
    using Result = PathMap;
    static llvm::StringRef name() { return "PathAnalysis"; }
    static void *ID() { return static_cast<void *>(&PassID); }
    Result run(llvm::Function &F, llvm::FunctionAnalysisManager *AM);

  private:
    static char PassID;
};

auto lastBlock(Path Path) -> llvm::BasicBlock *;

auto findPaths(int For, llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks)
    -> std::map<int, Paths>;

auto traverse(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks, bool First,
              std::set<const llvm::BasicBlock *> Visited) -> Paths_;

auto isMarked(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;

auto isReturn(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;
