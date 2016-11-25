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

#include "AnalysisResults.h"
#include "Helper.h"
#include "MonoPair.h"

#include <gmpxx.h>
#include <map>
#include <vector>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

#include "json.hpp"

#include "Integer.h"

namespace llvm {
template <> struct llvm::DenseMapInfo<std::string> {
    static inline std::string getEmptyKey() { return std::string(); }
    static inline StringRef getTombstoneKey() { return std::string(); }
    static unsigned getHashValue(std::string Val) {
        return (unsigned)(hash_value(Val));
    }
    static bool isEqual(std::string LHS, std::string RHS) { return LHS == RHS; }
};

template <> struct llvm::DenseMapInfo<Integer> {
    // Odd bitwidths should never occur in practise, so these are good special
    // values
    static inline Integer getEmptyKey() {
        return Integer(llvm::APInt::getMaxValue(3));
    }
    static inline Integer getTombstoneKey() {
        return Integer(llvm::APInt::getMaxValue(5));
    }
    static unsigned getHashValue(Integer val) {
        switch (val.type) {
        case IntType::Unbounded:
            // abs is necessary because gmp is shitty
            return (unsigned)(hash_combine_range(
                val.unbounded.get_mpz_t()->_mp_d,
                val.unbounded.get_mpz_t()->_mp_d +
                    std::abs(val.unbounded.get_mpz_t()->_mp_size)));
        case IntType::Bounded:
            return (unsigned)(hash_value(val.bounded));
        }
    }
    static bool isEqual(Integer lhs, Integer rhs) {
        switch (lhs.type) {
        case IntType::Unbounded:
            switch (rhs.type) {
            case IntType::Unbounded:
                return lhs.unbounded == rhs.unbounded;
            case IntType::Bounded:
                return false;
            }
        case IntType::Bounded:
            switch (rhs.type) {
            case IntType::Unbounded:
                return false;
            case IntType::Bounded:
                // LLVM doesn’t allow comparison of APInts of different
                // bitwidths, since this is the case for tombstones we have to
                // treat them separately
                if (lhs.bounded.getBitWidth() == rhs.bounded.getBitWidth()) {
                    return lhs.bounded == rhs.bounded;
                } else {
                    return false;
                }
            }
        }
        return lhs == rhs;
    }
};

template <typename K, typename V>
void insertOrReplace(llvm::DenseMap<K, V> &map, const std::pair<K, V> &kv) {
    auto ret = map.insert(kv);
    if (!ret.second) {
        ret.first->second = kv.second;
    }
}
template <typename K, typename V>
void insertOrReplace(llvm::DenseMap<K, V> &map, std::pair<K, V> &&kv) {
    auto ret = map.insert(kv);
    if (!ret.second) {
        ret.first->second = kv.second;
    }
}
}

namespace llreve {
namespace dynamic {
using BlockName = llvm::StringRef;
using VarName = const llvm::Value *;
using HeapAddress = Integer;

nlohmann::json toJSON(const Integer &v);
bool unsafeBool(const Integer &v);

struct Heap {
    llvm::SmallDenseMap<HeapAddress, Integer> assignedValues;
    Integer background;
    Heap() : assignedValues({}), background(mpz_class(0)) {}
    Heap(llvm::SmallDenseMap<HeapAddress, Integer> assignedValues,
         Integer background)
        : assignedValues(std::move(assignedValues)),
          background(std::move(background)) {}
};

bool isContainedIn(const llvm::SmallDenseMap<HeapAddress, Integer> &small,
                   const Heap &big);

bool operator==(const Heap &lhs, const Heap &rhs);

template <typename T> using VarMap = llvm::DenseMap<T, Integer>;
using FastVarMap = VarMap<const llvm::Value *>;

template <typename T> struct State {
    VarMap<T> variables;
    Heap heap;
    State(VarMap<T> variables, Heap heap)
        : variables(std::move(variables)), heap(std::move(heap)) {}
    State() = default;
    State(State &&other) = default;
    State(const State &other) = default;
    State &operator=(const State &other) = default;
    State &operator=(State &&other) = default;
};

template <typename T>
nlohmann::json stateToJSON(State<T> state,
                           std::function<std::string(T)> getName);

using FastState = State<const llvm::Value *>;

template <typename T> struct Step {
    virtual ~Step() = default;
    Step(const Step &other) = default;
    Step() = default;
    Step &operator=(const Step &other) = default;
    virtual nlohmann::json
    toJSON(std::function<std::string(T)> varName) const = 0;
};

template <typename T> struct BlockStep;

template <typename T> struct Call : Step<T> {
    const llvm::Function *function;
    State<T> entryState;
    State<T> returnState;
    std::vector<BlockStep<T>> steps;
    // Did we exit because we ran out of steps?
    bool earlyExit;
    uint32_t blocksVisited;
    Call(const llvm::Function *function, State<T> entryState,
         State<T> returnState, std::vector<BlockStep<T>> steps, bool earlyExit,
         uint32_t blocksVisited)
        : function(std::move(function)), entryState(std::move(entryState)),
          returnState(std::move(returnState)), steps(std::move(steps)),
          earlyExit(std::move(earlyExit)),
          blocksVisited(std::move(blocksVisited)) {}
    nlohmann::json
    toJSON(std::function<std::string(T)> varName) const override {
        nlohmann::json j;
        j["entry_state"] = stateToJSON<T>(entryState, varName);
        j["return_state"] = stateToJSON<T>(returnState, varName);
        std::vector<nlohmann::json> jsonSteps;
        for (const auto &step : steps) {
            jsonSteps.push_back(step.toJSON(varName));
        }
        j["steps"] = jsonSteps;
        j["early_exit"] = earlyExit;
        j["blocks_visited"] = blocksVisited;
        return j;
    }
};

using FastCall = Call<const llvm::Value *>;

template <typename T> struct BlockStep : Step<T> {
    BlockName blockName;
    State<T> state;
    // The calls performed in this block
    std::vector<Call<T>> calls;
    BlockStep(BlockName blockName, State<T> state, std::vector<Call<T>> calls)
        : blockName(std::move(blockName)), state(std::move(state)),
          calls(std::move(calls)) {}
    BlockStep(BlockStep &&other) = default;
    BlockStep(const BlockStep &other) = default;
    BlockStep &operator=(BlockStep &&other) = default;
    BlockStep &operator=(const BlockStep &other) = default;
    nlohmann::json
    toJSON(std::function<std::string(T)> varName) const override {
        nlohmann::json j;
        j["block_name"] = blockName;
        j["state"] = stateToJSON(state, varName);
        std::vector<nlohmann::json> jsonCalls;
        for (auto call : calls) {
            jsonCalls.push_back(call.toJSON(varName));
        }
        j["calls"] = jsonCalls;
        return j;
    }
};

template <typename T> struct BlockUpdate {
    // State after phi nodes
    State<T> step;
    // next block, null if the block ended with a return instruction
    const llvm::BasicBlock *nextBlock;
    // function calls in this block in the order they were called
    std::vector<Call<T>> calls;
    // Indicates a stop because we ran out of steps
    bool earlyExit;
    // steps this block has needed, if there are no function calls exactly one
    // step per block is needed
    uint32_t blocksVisited;
    BlockUpdate(State<T> step, // State end,
                const llvm::BasicBlock *nextBlock, std::vector<Call<T>> calls,
                bool earlyExit, uint32_t blocksVisited)
        : step(std::move(step)), nextBlock(nextBlock), calls(std::move(calls)),
          earlyExit(earlyExit), blocksVisited(blocksVisited) {}
    BlockUpdate() = default;
};

struct TerminatorUpdate {
    // State end;
    const llvm::BasicBlock *nextBlock;
    TerminatorUpdate(const llvm::BasicBlock *nextBlock)
        : nextBlock(nextBlock) {}
    TerminatorUpdate() = default;
};

/// The variables in the entry state will be renamed appropriately for both
/// programs
MonoPair<FastCall>
interpretFunctionPair(MonoPair<const llvm::Function *> funs,
                      MonoPair<FastVarMap> variables, MonoPair<Heap> heaps,
                      uint32_t maxSteps,
                      const AnalysisResultsMap &analysisResults);
MonoPair<FastCall> interpretFunctionPair(
    MonoPair<const llvm::Function *> funs, MonoPair<FastVarMap> variables,
    MonoPair<Heap> heaps, MonoPair<const llvm::BasicBlock *> startBlocks,
    uint32_t maxSteps, const AnalysisResultsMap &analysisResults);
auto interpretFunction(const llvm::Function &fun, FastState entry,
                       uint32_t maxSteps,
                       const AnalysisResultsMap &analysisResults) -> FastCall;
auto interpretFunction(const llvm::Function &fun, FastState entry,
                       const llvm::BasicBlock *bb, uint32_t maxSteps,
                       const AnalysisResultsMap &analysisResults) -> FastCall;
auto interpretBlock(const llvm::BasicBlock &block,
                    const llvm::BasicBlock *prevBlock, FastState &state,
                    bool skipPhi, uint32_t maxStep,
                    const AnalysisResultsMap &analysisResults)
    -> BlockUpdate<const llvm::Value *>;
auto interpretPHI(const llvm::PHINode &instr, FastState &state,
                  const llvm::BasicBlock *prevBlock) -> void;
auto interpretInstruction(const llvm::Instruction *instr, FastState &state)
    -> void;
auto interpretTerminator(const llvm::TerminatorInst *instr, FastState &state)
    -> TerminatorUpdate;
auto resolveValue(const llvm::Value *val, const FastState &state,
                  const llvm::Type *type) -> Integer;
auto interpretICmpInst(const llvm::ICmpInst *instr, FastState &state) -> void;
auto interpretIntPredicate(const llvm::ICmpInst *instr,
                           llvm::CmpInst::Predicate pred, const Integer &i0,
                           const Integer &i1, FastState &state) -> void;
auto interpretBinOp(const llvm::BinaryOperator *instr, FastState &state)
    -> void;
auto interpretIntBinOp(const llvm::BinaryOperator *instr,
                       llvm::Instruction::BinaryOps op, const Integer &i0,
                       const Integer &i1, FastState &state) -> void;
auto interpretBoolBinOp(const llvm::BinaryOperator *instr,
                        llvm::Instruction::BinaryOps op, bool b0, bool b1,
                        FastState &state) -> void;

template <typename A, typename T> Integer resolveGEP(T &gep, State<A> &state) {
    Integer offset = resolveValue(gep.getPointerOperand(), state,
                                  gep.getPointerOperand()->getType());
    const auto type = gep.getSourceElementType();
    std::vector<llvm::Value *> indices;
    for (auto ix = gep.idx_begin(), e = gep.idx_end(); ix != e; ++ix) {
        // Try several ways of finding the module
        const llvm::Module *mod = nullptr;
        if (auto instr = llvm::dyn_cast<llvm::Instruction>(&gep)) {
            mod = instr->getModule();
        }
        if (auto global =
                llvm::dyn_cast<llvm::GlobalValue>(gep.getPointerOperand())) {
            mod = global->getParent();
        }
        if (mod == nullptr) {
            logErrorData("Couldn’t cast gep to an instruction:\n", gep);
        }
        indices.push_back(*ix);
        const auto indexedType = llvm::GetElementPtrInst::getIndexedType(
            type, llvm::ArrayRef<llvm::Value *>(indices));
        const auto size = typeSize(indexedType, mod->getDataLayout());
        Integer val = resolveValue(*ix, state, (*ix)->getType());
        offset += Integer(mpz_class(size)).asPointer() *
                  Integer(val.asUnbounded()).asPointer();
    }
    return offset;
}

std::string valueName(const llvm::Value *val);

extern unsigned HeapElemSizeFlag;
}
}
