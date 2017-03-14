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

#include <map>
#include <set>

#include "llvm/IR/PassManager.h"

struct Mark {
  private:
    int index;

  public:
    explicit Mark(int index) : index(index) {}
    inline bool operator<(const Mark &other) const {
        return index < other.index;
    }
    inline bool operator>(const Mark &other) const { return other < *this; }
    inline bool operator<=(const Mark &other) const { return !(*this > other); }
    inline bool operator>=(const Mark &other) const { return !(*this < other); }
    inline bool operator==(const Mark &other) const {
        return index == other.index;
    }
    inline bool operator!=(const Mark &other) const {
        return !(index == other.index);
    }
    inline int asInt() const { return index; }
    friend std::ostream &operator<<(std::ostream &out, const Mark &mark);
    std::string toString() const;
    bool hasInvariant() const;
};

inline std::ostream &operator<<(std::ostream &out, const Mark &mark) {
    out << mark.index;
    return out;
}

const Mark UNREACHABLE_MARK(-3);
const Mark EXIT_MARK(-2);
const Mark ENTRY_MARK(-1);
const Mark FORBIDDEN_MARK(-4);

struct BidirBlockMarkMap {
    std::map<llvm::BasicBlock *, std::set<Mark>> BlockToMarksMap;
    std::map<Mark, std::set<llvm::BasicBlock *>> MarkToBlocksMap;
    BidirBlockMarkMap() : BlockToMarksMap({}), MarkToBlocksMap({}) {}
    BidirBlockMarkMap(
        std::map<llvm::BasicBlock *, std::set<Mark>> BlockToMarksMap,
        std::map<Mark, std::set<llvm::BasicBlock *>> MarkToBlocksMap)
        : BlockToMarksMap(BlockToMarksMap), MarkToBlocksMap(MarkToBlocksMap) {}
};
class MarkAnalysis : public llvm::AnalysisInfoMixin<MarkAnalysis> {
  public:
    using Result = BidirBlockMarkMap;
    Result run(llvm::Function &fun, llvm::FunctionAnalysisManager &am);
    BidirBlockMarkMap blockMarkMap;

  private:
    bool firstRun = true;
    friend llvm::AnalysisInfoMixin<MarkAnalysis>;
    static llvm::AnalysisKey Key;
};
