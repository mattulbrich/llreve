/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "MarkAnalysis.h"
namespace smt {
class SMTExpr;
}

class Condition {
  public:
    virtual std::unique_ptr<smt::SMTExpr> toSmt() const = 0;
    virtual ~Condition();
};

class Edge {
  public:
    std::shared_ptr<Condition> Cond;
    llvm::BasicBlock *Block;

    Edge(std::shared_ptr<Condition> Cond, llvm::BasicBlock *Block)
        : Cond(std::move(Cond)), Block(std::move(Block)) {}
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
    const llvm::Value *Cond;
    bool True;
    std::unique_ptr<smt::SMTExpr> toSmt() const override;
};

class SwitchCondition : public Condition {
  public:
    SwitchCondition(const llvm::Value *Cond, const llvm::APInt Val)
        : Cond(std::move(Cond)), Val(std::move(Val)) {}
    const llvm::Value *const Cond;
    llvm::APInt Val;
    std::unique_ptr<smt::SMTExpr> toSmt() const override;
};

class SwitchDefault : public Condition {
  public:
    SwitchDefault(const llvm::Value *Cond, std::vector<llvm::APInt> Vals)
        : Cond(std::move(Cond)), Vals(std::move(Vals)) {}
    const llvm::Value *const Cond;
    const std::vector<llvm::APInt> Vals;
    std::unique_ptr<smt::SMTExpr> toSmt() const override;
};

// I really suck at finding nice names
using Path_ = std::vector<Edge>;
using Paths_ = std::vector<Path_>;
using Paths = std::vector<Path>;

// This just wraps an std::map specialized to the appropriate types. The only
// reason why this is a struct instead of a type is to avoid ADL kicking in when
// instantiating this pass
struct PathMap {
  private:
    std::map<Mark, std::map<Mark, Paths>> value;

  public:
    auto begin() { return value.begin(); }
    auto end() { return value.end(); }
    auto begin() const { return value.begin(); }
    auto end() const { return value.end(); }
    std::map<Mark, Paths> &at(Mark mark) { return value.at(mark); }
    const std::map<Mark, Paths> &at(Mark mark) const { return value.at(mark); }
    auto find(Mark mark) { return value.find(mark); }
    auto find(Mark mark) const { return value.find(mark); }
    auto &operator[](Mark mark) { return value[mark]; }
};

class PathAnalysis : public llvm::AnalysisInfoMixin<PathAnalysis> {
  public:
    using Result = PathMap;
    PathMap run(llvm::Function &F, llvm::FunctionAnalysisManager &am);
    PathAnalysis(bool inferMarks) : InferMarks(inferMarks) {}

  private:
    PathMap pathMap;
    bool InferMarks;
    bool firstRun = true;
    friend llvm::AnalysisInfoMixin<PathAnalysis>;
    static llvm::AnalysisKey Key;
};

auto lastBlock(Path Path) -> llvm::BasicBlock *;

auto findPaths(BidirBlockMarkMap markedBlocks) -> PathMap;

auto findPathsStartingAt(Mark For, llvm::BasicBlock *BB,
                         BidirBlockMarkMap MarkedBlocks)
    -> std::map<Mark, Paths>;

auto traverse(llvm::BasicBlock *BB, BidirBlockMarkMap MarkedBlocks, bool First,
              std::set<const llvm::BasicBlock *> Visited) -> Paths_;

auto isMarked(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;

auto isReturn(llvm::BasicBlock &BB, BidirBlockMarkMap MarkedBlocks) -> bool;
