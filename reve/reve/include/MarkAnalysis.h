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

#include "llvm/IR/LegacyPassManager.h"

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
    std::string toString() const;
};

const Mark UNREACHABLE_MARK(-3);
const Mark EXIT_MARK(-2);
const Mark ENTRY_MARK(-1);

struct BidirBlockMarkMap {
    std::map<llvm::BasicBlock *, std::set<Mark>> BlockToMarksMap;
    std::map<Mark, std::set<llvm::BasicBlock *>> MarkToBlocksMap;
    BidirBlockMarkMap() : BlockToMarksMap({}), MarkToBlocksMap({}) {}
    BidirBlockMarkMap(
        std::map<llvm::BasicBlock *, std::set<Mark>> BlockToMarksMap,
        std::map<Mark, std::set<llvm::BasicBlock *>> MarkToBlocksMap)
        : BlockToMarksMap(BlockToMarksMap), MarkToBlocksMap(MarkToBlocksMap) {}
};
class MarkAnalysis : public llvm::FunctionPass {
  public:
    using Result = BidirBlockMarkMap;
    static llvm::StringRef name() { return "MarkAnalysis"; }
    bool runOnFunction(llvm::Function &Fun) override;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    BidirBlockMarkMap getBlockMarkMap() const;
    MarkAnalysis() : llvm::FunctionPass(ID) {}
    static char ID;
    // it’s not possible to have non default constructors with the legacy
    // passmanager so we can’t just pass a pointer there to escape this
    BidirBlockMarkMap BlockMarkMap;
};
