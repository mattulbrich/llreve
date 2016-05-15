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

#include "cbor.h"
#include "json.hpp"

using BlockName = std::string;
using VarName = const llvm::Value *;
using VarIntVal = mpz_class;
using HeapAddress = mpz_class;
enum class VarType { Int, Bool };
const VarName ReturnName = nullptr;

struct VarVal {
    virtual VarType getType() const = 0;
    virtual nlohmann::json toJSON() const = 0;
    virtual cbor_item_t *toCBOR() const = 0;
    virtual ~VarVal();
    VarVal(const VarVal &other) = default;
    VarVal() = default;
    VarVal &operator=(const VarVal &other) = default;
    virtual VarIntVal unsafeIntVal() const = 0;
};

bool varValEq(const VarVal &lhs, const VarVal &rhs);

std::shared_ptr<VarVal> cborToVarVal(const cbor_item_t *item);

struct VarInt : VarVal {
    VarIntVal val;
    VarType getType() const override;
    nlohmann::json toJSON() const override;
    cbor_item_t *toCBOR() const override;
    VarInt(VarIntVal val) : val(val) {}
    VarInt() : val(0) {}
    VarIntVal unsafeIntVal() const override;
};

struct VarBool : VarVal {
    bool val;
    VarType getType() const override;
    nlohmann::json toJSON() const override;
    cbor_item_t *toCBOR() const override;
    VarBool(bool val) : val(val) {}
    VarIntVal unsafeIntVal() const override;
};

using Heap = std::map<HeapAddress, VarIntVal>;
template <typename T> using VarMap = std::map<T, std::shared_ptr<VarVal>>;
using FastVarMap = VarMap<const llvm::Value *>;

template <typename T> struct State {
    VarMap<T> variables;
    // If an address is not in the map, it’s value is zero
    // Note that the values in the map can also be zero
    Heap heap;
    State(VarMap<T> variables, Heap heap) : variables(variables), heap(heap) {}
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
    virtual cbor_item_t *toCBOR() const = 0;
};

std::shared_ptr<Step<std::string>> cborToStep(const cbor_item_t *item);

template <typename T> struct BlockStep;

template <typename T> struct Call : Step<T> {
    std::string functionName;
    State<T> entryState;
    State<T> returnState;
    std::vector<std::shared_ptr<BlockStep<T>>> steps;
    // Did we exit because we ran out of steps?
    bool earlyExit;
    uint32_t blocksVisited;
    Call(std::string functionName, State<T> entryState, State<T> returnState,
         std::vector<std::shared_ptr<BlockStep<T>>> steps, bool earlyExit,
         uint32_t blocksVisited)
        : functionName(std::move(functionName)),
          entryState(std::move(entryState)),
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
            jsonSteps.push_back(step->toJSON(varName));
        }
        j["steps"] = jsonSteps;
        j["early_exit"] = earlyExit;
        j["blocks_visited"] = blocksVisited;
        return j;
    }
    cbor_item_t *toCBOR() const override {
        logError("Only specialized version cab be serialized to cbor\n");
        return nullptr;
    }
};

using FastCall = Call<const llvm::Value *>;
template <> cbor_item_t *FastCall::toCBOR() const;

Call<std::string> cborToCall(const cbor_item_t *item);

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
    cbor_item_t *toCBOR() const override {
        logError("Only specialized version can be serialized to cbor\n");
        return nullptr;
    }
};

template <> cbor_item_t *BlockStep<const llvm::Value *>::toCBOR() const;

std::shared_ptr<BlockStep<std::string>>
cborToBlockStep(const cbor_item_t *item);

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
                      std::map<std::string, std::shared_ptr<VarVal>> variables,
                      Heap heap, uint32_t maxSteps);
auto interpretFunction(const llvm::Function &fun, FastState entry,
                       uint32_t maxSteps) -> FastCall;
auto interpretBlock(const llvm::BasicBlock &block,
                    const llvm::BasicBlock *prevBlock, FastState &state,
                    uint32_t maxStep) -> BlockUpdate<const llvm::Value *>;
auto interpretPHI(const llvm::PHINode &instr, FastState &state,
                  const llvm::BasicBlock *prevBlock) -> void;
auto interpretInstruction(const llvm::Instruction *instr, FastState &state)
    -> void;
auto interpretTerminator(const llvm::TerminatorInst *instr, FastState &state)
    -> TerminatorUpdate;
auto resolveValue(const llvm::Value *val, const FastState &state)
    -> std::shared_ptr<VarVal>;
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

cbor_item_t *stateToCBOR(FastState state);
State<std::string> cborToState(const cbor_item_t *item);

template <typename A, typename T> VarInt resolveGEP(T &gep, State<A> state) {
    std::shared_ptr<VarVal> val = resolveValue(gep.getPointerOperand(), state);
    assert(val->getType() == VarType::Int);
    VarIntVal offset = std::static_pointer_cast<VarInt>(val)->val;
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
        std::shared_ptr<VarVal> val = resolveValue(*ix, state);
        assert(val->getType() == VarType::Int);
        offset += size * std::static_pointer_cast<VarInt>(val)->val;
    }
    return VarInt(offset);
}

std::string cborToString(const cbor_item_t *item);
VarIntVal cborToVarIntVal(const cbor_item_t *item);

template <typename T>
std::vector<T> cborToVector(const cbor_item_t *item,
                            std::function<T(const cbor_item_t *)> fun);
std::map<std::string, const cbor_item_t *>
cborToKeyMap(const cbor_item_t *item);

std::string valueName(const llvm::Value *val);
