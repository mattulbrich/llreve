#include "Interpreter.h"

#include "Compat.h"
#include "Helper.h"

#include "llvm/IR/Constants.h"

using llvm::LoadInst;
using llvm::StoreInst;
using llvm::GetElementPtrInst;
using llvm::Argument;
using llvm::BasicBlock;
using llvm::BinaryOperator;
using llvm::BranchInst;
using llvm::Function;
using llvm::SwitchInst;
using llvm::ICmpInst;
using llvm::CmpInst;
using llvm::Instruction;
using llvm::SelectInst;
using llvm::PHINode;
using llvm::ReturnInst;
using llvm::TerminatorInst;
using llvm::Value;
using llvm::dyn_cast;
using llvm::isa;
using llvm::ConstantInt;
using llvm::CastInst;

using std::vector;
using std::string;
using std::map;
using std::shared_ptr;
using std::make_shared;
using std::static_pointer_cast;

using nlohmann::json;

VarVal::~VarVal() = default;
Step::~Step() = default;

VarType VarInt::getType() const { return VarType::Int; }
json VarInt::toJSON() const { return val.get_str(); }
cbor_item_t *VarInt::toCBOR() const {
    return cbor_build_string(val.get_str().c_str());
}
json VarBool::toJSON() const { return json(val); }
cbor_item_t *VarBool::toCBOR() const { return cbor_build_bool(val); }

VarType VarBool::getType() const { return VarType::Bool; }

MonoPair<Call> interpretFunctionPair(MonoPair<const Function *> funs,
                                     map<string, shared_ptr<VarVal>> variables,
                                     Heap heap, uint32_t maxSteps) {
    VarMap var1;
    VarMap var2;
    for (auto &arg : funs.first->args()) {
        std::string varName = arg.getName();
        size_t i = varName.find_first_of('$');
        varName = varName.substr(0, i);
        const llvm::Value *a = &arg;
        var1[a] = variables.at(varName);
    }
    for (auto &arg : funs.second->args()) {
        std::string varName = arg.getName();
        size_t i = varName.find_first_of('$');
        varName = varName.substr(0, i);
        const llvm::Value *a = &arg;
        var2[a] = variables.at(varName);
    }
    return makeMonoPair(
        interpretFunction(*funs.first, State(var1, heap), maxSteps),
        interpretFunction(*funs.second, State(var2, heap), maxSteps));
}

Call interpretFunction(const Function &fun, State entry, uint32_t maxSteps) {
    const BasicBlock *prevBlock = nullptr;
    const BasicBlock *currentBlock = &fun.getEntryBlock();
    vector<shared_ptr<Step>> steps;
    State currentState = entry;
    BlockUpdate update;
    uint32_t blocksVisited = 0;
    do {
        update = interpretBlock(*currentBlock, prevBlock, currentState,
                                maxSteps - blocksVisited);
        blocksVisited += update.blocksVisited;
        steps.push_back(make_shared<BlockStep>(currentBlock->getName(),
                                               update.step, update.calls));
        prevBlock = currentBlock;
        currentBlock = update.nextBlock;
        if (blocksVisited > maxSteps || update.earlyExit) {
            return Call(fun.getName(), entry, currentState, steps, true,
                        blocksVisited);
        }
    } while (currentBlock != nullptr);
    return Call(fun.getName(), entry, currentState, steps, false,
                blocksVisited);
}

BlockUpdate interpretBlock(const BasicBlock &block, const BasicBlock *prevBlock,
                           State &state, uint32_t maxSteps) {
    uint32_t blocksVisited = 1;
    const Instruction *firstNonPhi = block.getFirstNonPHI();
    const Instruction *terminator = block.getTerminator();
    // Handle phi instructions
    BasicBlock::const_iterator instrIterator;
    for (instrIterator = block.begin(); &*instrIterator != firstNonPhi;
         ++instrIterator) {
        const Instruction *inst = &*instrIterator;
        assert(isa<PHINode>(inst));
        interpretPHI(*dyn_cast<PHINode>(inst), state, prevBlock);
    }
    State step(state);

    vector<Call> calls;
    // Handle non phi instructions
    for (; &*instrIterator != terminator; ++instrIterator) {
        if (const auto call = dyn_cast<llvm::CallInst>(&*instrIterator)) {
            const Function *fun = call->getFunction();
            VarMap args;
            auto argIt = fun->getArgumentList().begin();
            for (const auto &arg : call->arg_operands()) {
                args[&*argIt] = resolveValue(arg, state);
                ++argIt;
            }
            Call c = interpretFunction(*fun, State(args, state.heap),
                                       maxSteps - blocksVisited);
            blocksVisited += c.blocksVisited;
            if (blocksVisited > maxSteps || c.earlyExit) {
                return BlockUpdate(step, nullptr, calls, true, blocksVisited);
            }
            calls.push_back(c);
            state.heap = c.returnState.heap;
            state.variables[call] = c.returnState.variables[ReturnName];
        } else {
            interpretInstruction(&*instrIterator, state);
        }
    }

    // Terminator instruction
    TerminatorUpdate update = interpretTerminator(block.getTerminator(), state);

    return BlockUpdate(step, update.nextBlock, calls, false, blocksVisited);
}

void interpretInstruction(const Instruction *instr, State &state) {
    if (const auto binOp = dyn_cast<BinaryOperator>(instr)) {
        interpretBinOp(binOp, state);
    } else if (const auto icmp = dyn_cast<ICmpInst>(instr)) {
        interpretICmpInst(icmp, state);
    } else if (const auto cast = dyn_cast<CastInst>(instr)) {
        assert(cast->getNumOperands() == 1);
        state.variables[cast] = resolveValue(cast->getOperand(0), state);
    } else if (const auto gep = dyn_cast<GetElementPtrInst>(instr)) {
        state.variables[gep] = make_shared<VarInt>(resolveGEP(*gep, state));
    } else if (const auto load = dyn_cast<LoadInst>(instr)) {
        shared_ptr<VarVal> ptr = resolveValue(load->getPointerOperand(), state);
        assert(ptr->getType() == VarType::Int);
        VarInt heapVal = VarInt(0);
        auto heapIt = state.heap.find(static_pointer_cast<VarInt>(ptr)->val);
        if (heapIt != state.heap.end()) {
            heapVal = heapIt->second;
        }
        state.variables[load] = make_shared<VarInt>(heapVal);
    } else if (const auto store = dyn_cast<StoreInst>(instr)) {
        shared_ptr<VarVal> ptr =
            resolveValue(store->getPointerOperand(), state);
        assert(ptr->getType() == VarType::Int);
        shared_ptr<VarVal> val = resolveValue(store->getValueOperand(), state);
        assert(val->getType() == VarType::Int);
        HeapAddress addr = static_pointer_cast<VarInt>(ptr)->val;
        state.heap[addr] = *static_pointer_cast<VarInt>(val);
    } else if (const auto select = dyn_cast<SelectInst>(instr)) {
        shared_ptr<VarVal> cond = resolveValue(select->getCondition(), state);
        assert(cond->getType() == VarType::Bool);
        bool condVal = static_pointer_cast<VarBool>(cond)->val;
        shared_ptr<VarVal> var;
        if (condVal) {
            var = resolveValue(select->getTrueValue(), state);
        } else {
            var = resolveValue(select->getFalseValue(), state);
        }
        state.variables[select] = var;
    } else {
        logErrorData("unsupported instruction:\n", *instr);
    }
}

void interpretPHI(const PHINode &instr, State &state,
                  const BasicBlock *prevBlock) {
    const Value *val = instr.getIncomingValueForBlock(prevBlock);
    shared_ptr<VarVal> var = resolveValue(val, state);
    state.variables[&instr] = var;
}

TerminatorUpdate interpretTerminator(const TerminatorInst *instr,
                                     State &state) {
    if (const auto retInst = dyn_cast<ReturnInst>(instr)) {
        state.variables[ReturnName] =
            resolveValue(retInst->getReturnValue(), state);
        return TerminatorUpdate(nullptr);
    } else if (const auto branchInst = dyn_cast<BranchInst>(instr)) {
        if (branchInst->isUnconditional()) {
            assert(branchInst->getNumSuccessors() == 1);
            return TerminatorUpdate(branchInst->getSuccessor(0));
        } else {
            shared_ptr<VarVal> cond =
                resolveValue(branchInst->getCondition(), state);
            assert(cond->getType() == VarType::Bool);
            bool condVal = static_pointer_cast<VarBool>(cond)->val;
            assert(branchInst->getNumSuccessors() == 2);
            if (condVal) {
                return TerminatorUpdate(branchInst->getSuccessor(0));
            } else {
                return TerminatorUpdate(branchInst->getSuccessor(1));
            }
        }
    } else if (const auto switchInst = dyn_cast<SwitchInst>(instr)) {
        shared_ptr<VarVal> cond =
            resolveValue(switchInst->getCondition(), state);
        assert(cond->getType() == VarType::Int);
        VarIntVal condVal = static_pointer_cast<VarInt>(cond)->val;
        for (auto c : switchInst->cases()) {
            VarIntVal caseVal = c.getCaseValue()->getSExtValue();
            if (caseVal == condVal) {
                return TerminatorUpdate(c.getCaseSuccessor());
            }
        }
        return TerminatorUpdate(switchInst->getDefaultDest());

    } else {
        logError("Only return and branches are supported\n");
        return TerminatorUpdate(nullptr);
    }
}

shared_ptr<VarVal> resolveValue(const Value *val, const State &state) {
    if (isa<Instruction>(val) || isa<Argument>(val)) {
        return state.variables.at(val);
    } else if (const auto constInt = dyn_cast<ConstantInt>(val)) {
        return make_shared<VarInt>(constInt->getSExtValue());
    }
    logErrorData("Operators are not yet handled\n", *val);
    return make_shared<VarInt>(42);
}

void interpretICmpInst(const ICmpInst *instr, State &state) {
    assert(instr->getNumOperands() == 2);
    const auto op0 = resolveValue(instr->getOperand(0), state);
    const auto op1 = resolveValue(instr->getOperand(1), state);
    switch (instr->getPredicate()) {
    default:
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        VarIntVal i0 = static_pointer_cast<VarInt>(op0)->val;
        VarIntVal i1 = static_pointer_cast<VarInt>(op1)->val;
        interpretIntPredicate(instr, instr->getPredicate(), i0, i1, state);
    }
}

void interpretIntPredicate(const ICmpInst *instr, CmpInst::Predicate pred,
                           VarIntVal i0, VarIntVal i1, State &state) {
    bool predVal = false;
    switch (pred) {
    case CmpInst::ICMP_SGE:
        predVal = i0 >= i1;
        break;
    case CmpInst::ICMP_SGT:
        predVal = i0 > i1;
        break;
    case CmpInst::ICMP_SLE:
        predVal = i0 <= i1;
        break;
    case CmpInst::ICMP_SLT:
        predVal = i0 < i1;
        break;
    case CmpInst::ICMP_EQ:
        predVal = i0 == i1;
        break;
    case CmpInst::ICMP_NE:
        predVal = i0 != i1;
        break;
    default:
        logErrorData("Unsupported predicate:\n", *instr);
    }
    state.variables[instr] = make_shared<VarBool>(predVal);
}

void interpretBinOp(const BinaryOperator *instr, State &state) {
    const auto op0 = resolveValue(instr->getOperand(0), state);
    const auto op1 = resolveValue(instr->getOperand(1), state);
    switch (instr->getOpcode()) {
    default:
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        VarIntVal i0 = static_pointer_cast<VarInt>(op0)->val;
        VarIntVal i1 = static_pointer_cast<VarInt>(op1)->val;
        interpretIntBinOp(instr, instr->getOpcode(), i0, i1, state);
    }
}

void interpretIntBinOp(const BinaryOperator *instr, Instruction::BinaryOps op,
                       VarIntVal i0, VarIntVal i1, State &state) {
    VarIntVal result = 0;
    switch (op) {
    case Instruction::Add:
        result = i0 + i1;
        break;
    case Instruction::Sub:
        result = i0 - i1;
        break;
    case Instruction::SDiv:
        result = i0 / i1;
        break;
    default:
        logErrorData("Unsupported binop:\n", *instr);
    }
    state.variables[instr] = make_shared<VarInt>(result);
}

json Call::toJSON() const {
    json j;
    j["entry_state"] = stateToJSON(entryState);
    j["return_state"] = stateToJSON(returnState);
    vector<json> jsonSteps;
    for (auto step : steps) {
        jsonSteps.push_back(step->toJSON());
    }
    j["steps"] = jsonSteps;
    j["early_exit"] = earlyExit;
    j["blocks_visited"] = blocksVisited;
    return j;
}

cbor_item_t *Call::toCBOR() const {
    bool ret;
    cbor_item_t *map = cbor_new_definite_map(5);
    ret = cbor_map_add(
        map,
        (struct cbor_pair){.key = cbor_move(cbor_build_string("entry_state")),
                           .value = cbor_move(stateToCBOR(entryState))});
    assert(ret);
    ret = cbor_map_add(
        map,
        (struct cbor_pair){.key = cbor_move(cbor_build_string("return_state")),
                           .value = cbor_move(stateToCBOR(returnState))});
    assert(ret);
    cbor_item_t *cborSteps = cbor_new_definite_array(steps.size());

    for (const auto &step : steps) {
        ret = cbor_array_push(cborSteps, cbor_move(step->toCBOR()));
        assert(ret);
    }
    ret = cbor_map_add(
        map, (struct cbor_pair){.key = cbor_move(cbor_build_string("steps")),
                                .value = cbor_move(cborSteps)});
    assert(ret);
    ret = cbor_map_add(
        map,
        (struct cbor_pair){.key = cbor_move(cbor_build_string("early_exit")),
                           .value = cbor_move(cbor_build_bool(earlyExit))});
    assert(ret);
    ret = cbor_map_add(
        map, (struct cbor_pair){
                 .key = cbor_move(cbor_build_string("blocks_visited")),
                 .value = cbor_move(cbor_build_uint32(blocksVisited))});
    assert(ret);
    return map;
}

json BlockStep::toJSON() const {
    json j;
    j["block_name"] = blockName;
    j["state"] = stateToJSON(state);
    vector<json> jsonCalls;
    for (auto call : calls) {
        jsonCalls.push_back(call.toJSON());
    }
    j["calls"] = jsonCalls;
    return j;
}

cbor_item_t *BlockStep::toCBOR() const {
    cbor_item_t *map = cbor_new_definite_map(3);
    bool ret;
    ret = cbor_map_add(
        map, (struct cbor_pair){
                 .key = cbor_move(cbor_build_string("block_name")),
                 .value = cbor_move(cbor_build_string(blockName.c_str()))});
    assert(ret);
    ret = cbor_map_add(
        map, (struct cbor_pair){.key = cbor_move(cbor_build_string("state")),
                                .value = cbor_move(stateToCBOR(state))});
    assert(ret);
    cbor_item_t *cborCalls = cbor_new_definite_array(calls.size());
    for (const auto &call : calls) {
        ret = cbor_array_push(cborCalls, cbor_move(call.toCBOR()));
        assert(ret);
    }
    cbor_map_add(
        map, (struct cbor_pair){.key = cbor_move(cbor_build_string("calls")),
                                .value = cbor_move(cborCalls)});
    return map;
}

json stateToJSON(State state) {
    map<string, json> jsonVariables;
    map<string, json> jsonHeap;
    for (auto var : state.variables) {
        string varName = var.first == nullptr ? "return" : var.first->getName();
        jsonVariables.insert({varName, var.second->toJSON()});
    }
    for (auto index : state.heap) {
        jsonHeap.insert({index.first.get_str(), index.second.val.get_str()});
    }
    json j;
    j["variables"] = jsonVariables;
    j["heap"] = jsonHeap;
    return j;
}

cbor_item_t *stateToCBOR(State state) {
    cbor_item_t *cborVariables = cbor_new_definite_map(state.variables.size());
    cbor_item_t *cborHeap = cbor_new_definite_map(state.heap.size());
    for (const auto &var : state.variables) {
        string varName = var.first == nullptr ? "return" : var.first->getName();
        cbor_map_add(cborVariables,
                     (struct cbor_pair){
                         .key = cbor_move(cbor_build_string(varName.c_str())),
                         .value = cbor_move(var.second->toCBOR())});
    }
    for (const auto &index : state.heap) {
        cbor_map_add(cborHeap, (struct cbor_pair){
                                   .key = cbor_move(cbor_build_string(
                                       index.first.get_str().c_str())),
                                   .value = cbor_move(cbor_build_string(
                                       index.second.val.get_str().c_str()))});
    }
    cbor_item_t *map = cbor_new_definite_map(2);
    cbor_map_add(map, (struct cbor_pair){
                          .key = cbor_move(cbor_build_string("variables")),
                          .value = cbor_move(cborVariables)});
    cbor_map_add(map,
                 (struct cbor_pair){.key = cbor_move(cbor_build_string("heap")),
                                    .value = cbor_move(cborHeap)});
    return map;
}
