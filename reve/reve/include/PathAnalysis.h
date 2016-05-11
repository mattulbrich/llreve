#pragma once

#include "MarkAnalysis.h"
#include "SMT.h"

#include "llvm/IR/PassManager.h"

class Condition {
  public:
    virtual std::unique_ptr<const smt::SMTExpr> toSmt() const = 0;
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
    std::unique_ptr<const smt::SMTExpr> toSmt() const override;
};

class SwitchCondition : public Condition {
  public:
    SwitchCondition(const llvm::Value *Cond, int64_t Val)
        : Cond(std::move(Cond)), Val(std::move(Val)) {}
    const llvm::Value *const Cond;
    const int64_t Val;
    std::unique_ptr<const smt::SMTExpr> toSmt() const override;
};

class SwitchDefault : public Condition {
  public:
    SwitchDefault(const llvm::Value *Cond, std::vector<int64_t> Vals)
        : Cond(std::move(Cond)), Vals(std::move(Vals)) {}
    const llvm::Value *const Cond;
    const std::vector<int64_t> Vals;
    std::unique_ptr<const smt::SMTExpr> toSmt() const override;
};

// I really suck at finding nice names
using Path_ = std::vector<Edge>;
using Paths_ = std::vector<Path_>;
using Paths = std::vector<Path>;
using PathMap = std::map<int, std::map<int, Paths>>;

class PathAnalysis : public llvm::FunctionPass {
  public:
    using Result = PathMap;
    static llvm::StringRef name() { return "PathAnalysis"; }
    bool runOnFunction(llvm::Function &F) override;
    PathAnalysis() : llvm::FunctionPass(ID) {}
    PathMap getPathMap() const;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    static char ID;
    PathMap PathsMap;
    bool InferMarks;
};

auto lastBlock(Path Path) -> llvm::BasicBlock *;

auto findPaths(BidirBlockMarkMap markedBlocks) -> PathMap;

auto findPathsStartingAt(int For, llvm::BasicBlock *BB,
                         BidirBlockMarkMap MarkedBlocks)
    -> std::map<int, Paths>;

auto traverse(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks, bool First,
              std::set<const llvm::BasicBlock *> Visited) -> Paths_;

auto isMarked(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;

auto isReturn(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;
