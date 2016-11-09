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

#include "Helper.h"
#include "MonoPair.h"

#include <gmpxx.h>
#include <map>
#include <vector>

#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

#include "json.hpp"

#include "Integer.h"

namespace llreve {
namespace dynamic {
using BlockName = std::string;
using VarName = const llvm::Value *;
using VarIntVal = Integer;
using HeapAddress = Integer;
enum class VarType { Int, Bool };
const VarName ReturnName = nullptr;

VarType getType(const VarIntVal &v);
nlohmann::json toJSON(const VarIntVal &v);
VarIntVal unsafeIntVal(const VarIntVal &v);
const VarIntVal &unsafeIntValRef(const VarIntVal &v);
bool unsafeBool(const VarIntVal &v);

VarType getType(const bool &b);
nlohmann::json toJSON(const bool &b);
VarIntVal unsafeIntVal(const bool &b);
const VarIntVal &unsafeIntValRef(const bool &b);
bool unsafeBool(const bool &b);

// This technique is from the talk “Inheritance is The Base Class of Evil”
// https://channel9.msdn.com/Events/GoingNative/2013/Inheritance-Is-The-Base-Class-of-Evil
// It gives us value semantics and polymorphism at the same time
class VarVal {
  public:
    template <typename T> VarVal(T x) : self_(new model<T>(std::move(x))) {}
    /* This is only here to make it possible to use [] on maps */
    VarVal() : self_(nullptr) {}

    VarVal(const VarVal &x) {
        if (x.self_) {
            self_ = std::unique_ptr<const VarValConcept>(x.self_->copy_());
        } else {
            self_ = nullptr;
        }
    }
    VarVal(VarVal &&) noexcept = default;

    VarVal &operator=(const VarVal &x) {
        VarVal tmp(x);
        *this = std::move(tmp);
        return *this;
    }
    VarVal &operator=(VarVal &&) noexcept = default;
    VarVal &operator=(VarIntVal x) {
        self_.reset(new model<VarIntVal>(std::move(x)));
        return *this;
    }
    VarVal &operator=(bool x) {
        self_.reset(new model<bool>(std::move(x)));
        return *this;
    }

    friend VarType getType(const VarVal &x) { return x.self_->getType_(); }
    friend nlohmann::json toJSON(const VarVal &x) { return x.self_->toJSON_(); }
    friend VarIntVal unsafeIntVal(const VarVal &x) {
        return x.self_->unsafeIntVal_();
    }
    friend const VarIntVal &unsafeIntValRef(const VarVal &x) {
        return x.self_->unsafeIntValRef_();
    }
    friend bool unsafeBool(const VarVal &x) { return x.self_->unsafeBool_(); }

  private:
    struct VarValConcept {
        // The virtual destructor exists purely to have something which can be
        // implemented in a source file to pin the vtable
        virtual ~VarValConcept();
        VarValConcept() = default;
        VarValConcept(const VarValConcept &x) = default;
        virtual VarValConcept *copy_() const = 0;
        virtual VarType getType_() const = 0;
        virtual nlohmann::json toJSON_() const = 0;
        virtual VarIntVal unsafeIntVal_() const = 0;
        virtual const VarIntVal &unsafeIntValRef_() const = 0;
        virtual bool unsafeBool_() const = 0;
    };
    template <typename T> struct model : VarValConcept {
        model(T x) : data_(std::move(x)) {}
        VarValConcept *copy_() const override { return new model(*this); }
        VarType getType_() const override { return getType(data_); }
        nlohmann::json toJSON_() const override { return toJSON(data_); }
        VarIntVal unsafeIntVal_() const override { return unsafeIntVal(data_); }
        const VarIntVal &unsafeIntValRef_() const override {
            return unsafeIntValRef(data_);
        }
        bool unsafeBool_() const override { return unsafeBool(data_); }
        T data_;
    };

    std::unique_ptr<const VarValConcept> self_;
};

bool varValEq(const VarVal &lhs, const VarVal &rhs);

using Heap = std::map<HeapAddress, VarIntVal>;
template <typename T> using VarMap = std::map<T, VarVal>;
using FastVarMap = VarMap<const llvm::Value *>;

template <typename T> struct State {
    VarMap<T> variables;
    // If an address is not in the map, it’s value is zero
    // Note that the values in the map can also be zero
    Heap heap;
    Integer heapBackground;
    State(VarMap<T> variables, Heap heap, Integer heapBackground)
        : variables(variables), heap(heap), heapBackground(heapBackground) {}
    State() = default;
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
        for (auto step : steps) {
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
MonoPair<FastCall> interpretFunctionPair(MonoPair<const llvm::Function *> funs,
                                         MonoPair<FastVarMap> variables,
                                         MonoPair<Heap> heaps,
                                         MonoPair<Integer> heapBackgrounds,
                                         uint32_t maxSteps);
MonoPair<FastCall> interpretFunctionPair(
    MonoPair<const llvm::Function *> funs, MonoPair<FastVarMap> variables,
    MonoPair<Heap> heaps, MonoPair<Integer> heapBackgrounds,
    MonoPair<const llvm::BasicBlock *> startBlocks, uint32_t maxSteps);
auto interpretFunction(const llvm::Function &fun, FastState entry,
                       uint32_t maxSteps) -> FastCall;
auto interpretFunction(const llvm::Function &fun, FastState entry,
                       const llvm::BasicBlock *bb, uint32_t maxSteps)
    -> FastCall;
auto interpretBlock(const llvm::BasicBlock &block,
                    const llvm::BasicBlock *prevBlock, FastState &state,
                    bool skipPhi, uint32_t maxStep)
    -> BlockUpdate<const llvm::Value *>;
auto interpretPHI(const llvm::PHINode &instr, FastState &state,
                  const llvm::BasicBlock *prevBlock) -> void;
auto interpretInstruction(const llvm::Instruction *instr, FastState &state)
    -> void;
auto interpretTerminator(const llvm::TerminatorInst *instr, FastState &state)
    -> TerminatorUpdate;
auto resolveValue(const llvm::Value *val, const FastState &state,
                  const llvm::Type *type) -> VarVal;
auto interpretICmpInst(const llvm::ICmpInst *instr, FastState &state) -> void;
auto interpretIntPredicate(const llvm::ICmpInst *instr,
                           llvm::CmpInst::Predicate pred, const VarIntVal &i0,
                           const VarIntVal &i1, FastState &state) -> void;
auto interpretBinOp(const llvm::BinaryOperator *instr, FastState &state)
    -> void;
auto interpretIntBinOp(const llvm::BinaryOperator *instr,
                       llvm::Instruction::BinaryOps op, const VarIntVal &i0,
                       const VarIntVal &i1, FastState &state) -> void;
auto interpretBoolBinOp(const llvm::BinaryOperator *instr,
                        llvm::Instruction::BinaryOps op, bool b0, bool b1,
                        FastState &state) -> void;

template <typename A, typename T> VarIntVal resolveGEP(T &gep, State<A> state) {
    VarVal val = resolveValue(gep.getPointerOperand(), state,
                              gep.getPointerOperand()->getType());
    assert(getType(val) == VarType::Int);
    VarIntVal offset = unsafeIntVal(val);
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
        VarVal val = resolveValue(*ix, state, (*ix)->getType());
        assert(getType(val) == VarType::Int);
        offset += Integer(mpz_class(size)).asPointer() *
                  Integer(unsafeIntVal(val).asUnbounded()).asPointer();
    }
    return offset;
}

std::string valueName(const llvm::Value *val);

extern unsigned HeapElemSizeFlag;
}
}
