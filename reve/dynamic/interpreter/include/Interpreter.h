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

using BlockName = std::string;
using VarName = const llvm::Value *;
using VarIntVal = mpz_class;
using HeapAddress = mpz_class;
enum class VarType { Int, Bool };
const VarName ReturnName = nullptr;

struct VarVal {
    virtual VarType getType() const = 0;
    virtual nlohmann::json toJSON() const = 0;
    virtual ~VarVal();
    VarVal(const VarVal &other) = default;
    VarVal() = default;
    VarVal &operator=(const VarVal &other) = default;
};

struct VarInt : VarVal {
    VarIntVal val;
    VarType getType() const override;
    nlohmann::json toJSON() const override;
    VarInt(VarIntVal val) : val(val) {}
    VarInt() : val(0) {}
};

struct VarBool : VarVal {
    bool val;
    VarType getType() const override;
    nlohmann::json toJSON() const override;
    VarBool(bool val) : val(val) {}
};

using Heap = std::map<HeapAddress, VarInt>;
using VarMap = std::map<const llvm::Value *, std::shared_ptr<VarVal>>;

struct State {
    VarMap variables;
    // If an address is not in the map, it’s value is zero
    // Note that the values in the map can also be zero
    Heap heap;
    State(VarMap variables, Heap heap) : variables(variables), heap(heap) {}
    State() = default;
};

struct Step {
    virtual ~Step();
    Step(const Step &other) = default;
    Step() = default;
    Step &operator=(const Step &other) = default;
    virtual nlohmann::json toJSON() const = 0;
};

struct Call : Step {
    std::string functionName;
    State entryState;
    State returnState;
    std::vector<std::shared_ptr<Step>> steps;
    // Did we exit because we ran out of steps?
    bool earlyExit;
    int blocksVisited;
    Call(std::string functionName, State entryState, State returnState,
         std::vector<std::shared_ptr<Step>> steps, bool earlyExit,
         int blocksVisited)
        : functionName(functionName), entryState(entryState),
          returnState(returnState), steps(steps), earlyExit(earlyExit),
          blocksVisited(blocksVisited) {}
    nlohmann::json toJSON() const override;
};

struct BlockStep : Step {
    BlockName blockName;
    State state;
    // The calls performed in this block
    std::vector<Call> calls;
    BlockStep(BlockName blockName, State state, std::vector<Call> calls)
        : blockName(blockName), state(state), calls(calls) {}
    nlohmann::json toJSON() const override;
};

struct BlockUpdate {
    // State after phi nodes
    State step;
    // next block, null if the block ended with a return instruction
    const llvm::BasicBlock *nextBlock;
    // function calls in this block in the order they were called
    std::vector<Call> calls;
    // Indicates a stop because we ran out of steps
    bool earlyExit;
    // steps this block has needed, if there are no function calls exactly one
    // step per block is needed
    int blocksVisited;
    BlockUpdate(State step, // State end,
                const llvm::BasicBlock *nextBlock, std::vector<Call> calls,
                bool earlyExit, int blocksVisited)
        : step(step), nextBlock(nextBlock), calls(calls), earlyExit(earlyExit),
          blocksVisited(blocksVisited) {}
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
MonoPair<Call>
interpretFunctionPair(MonoPair<const llvm::Function *> funs,
                      std::map<std::string, std::shared_ptr<VarVal>> variables,
                      Heap heap, int maxSteps);
auto interpretFunction(const llvm::Function &fun, State entry, int maxSteps)
    -> Call;
auto interpretBlock(const llvm::BasicBlock &block,
                    const llvm::BasicBlock *prevBlock, State &state,
                    int maxStep) -> BlockUpdate;
auto interpretPHI(const llvm::PHINode &instr, State &state,
                  const llvm::BasicBlock *prevBlock) -> void;
auto interpretInstruction(const llvm::Instruction *instr, State &state) -> void;
auto interpretTerminator(const llvm::TerminatorInst *instr, State &state)
    -> TerminatorUpdate;
auto resolveValue(const llvm::Value *val, const State &state)
    -> std::shared_ptr<VarVal>;
auto interpretICmpInst(const llvm::ICmpInst *instr, State &state) -> void;
auto interpretIntPredicate(const llvm::ICmpInst *instr, llvm::CmpInst::Predicate pred,
                           VarIntVal i0, VarIntVal i1, State &state) -> void;
auto interpretBinOp(const llvm::BinaryOperator *instr, State &state) -> void;
auto interpretIntBinOp(const llvm::BinaryOperator *instr,
                       llvm::Instruction::BinaryOps op, VarIntVal i0,
                       VarIntVal i1, State &state) -> void;

nlohmann::json stateToJSON(State state);

template <typename T> VarInt resolveGEP(T &gep, State state) {
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
