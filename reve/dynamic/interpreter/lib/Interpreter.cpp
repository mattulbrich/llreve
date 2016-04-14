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
using llvm::ICmpInst;
using llvm::CmpInst;
using llvm::Instruction;
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
json VarBool::toJSON() const { return json(val); }

VarType VarBool::getType() const { return VarType::Bool; }

Call interpretFunction(const Function &fun, State entry) {
    const BasicBlock *prevBlock = nullptr;
    const BasicBlock *currentBlock = &fun.getEntryBlock();
    vector<shared_ptr<Step>> steps;
    State currentState = entry;
    BlockUpdate update;
    do {
        update = interpretBlock(*currentBlock, prevBlock, currentState);
        steps.push_back(make_shared<BlockStep>(currentBlock->getName(),
                                               update.step, update.calls));
        prevBlock = currentBlock;
        currentBlock = update.nextBlock;
        currentState = update.end;
    } while (currentBlock != nullptr);
    return Call(fun.getName(), entry, update.end, steps);
}

BlockUpdate interpretBlock(const BasicBlock &block, const BasicBlock *prevBlock,
                           State state) {
    // VarMap variables = state.variables;
    // Heap heap = state.heap;
    const Instruction *firstNonPhi = block.getFirstNonPHI();
    const Instruction *terminator = block.getTerminator();
    // Handle phi instructions
    BasicBlock::const_iterator instrIterator;
    for (instrIterator = block.begin(); &*instrIterator != firstNonPhi;
         ++instrIterator) {
        const Instruction *inst = &*instrIterator;
        assert(isa<PHINode>(inst));
        state = interpretPHI(*dyn_cast<PHINode>(inst), state, prevBlock);
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
                args[argIt->getName()] = resolveValue(arg, state);
                ++argIt;
            }
            Call c = interpretFunction(*fun, State(args, state.heap));
            calls.push_back(c);
            state.heap = c.returnState.heap;
            state.variables[call->getName()] =
                c.returnState.variables[ReturnName];
        } else {
            state = interpretInstruction(&*instrIterator, state);
        }
    }

    // Terminator instruction
    TerminatorUpdate update = interpretTerminator(block.getTerminator(), state);

    return BlockUpdate(step, update.end, update.nextBlock, calls);
}

State interpretInstruction(const Instruction *instr, State state) {
    if (const auto binOp = dyn_cast<BinaryOperator>(instr)) {
        return interpretBinOp(binOp, state);
    } else if (const auto icmp = dyn_cast<ICmpInst>(instr)) {
        return interpretICmpInst(icmp, state);
    } else if (const auto cast = dyn_cast<CastInst>(instr)) {
        assert(cast->getNumOperands() == 1);
        state.variables[cast->getName()] =
            resolveValue(cast->getOperand(0), state);
        return state;
    } else if (const auto gep = dyn_cast<GetElementPtrInst>(instr)) {
        state.variables[gep->getName()] =
            make_shared<VarInt>(resolveGEP(*gep, state));
        return state;
    } else if (const auto load = dyn_cast<LoadInst>(instr)) {
        shared_ptr<VarVal> ptr = resolveValue(load->getPointerOperand(), state);
        assert(ptr->getType() == VarType::Int);
        VarInt heapVal = VarInt(0);
        auto heapIt = state.heap.find(static_pointer_cast<VarInt>(ptr)->val);
        if (heapIt != state.heap.end()) {
            heapVal = heapIt->second;
        }
        state.variables[load->getName()] = make_shared<VarInt>(heapVal);
        return state;
    } else if (const auto store = dyn_cast<StoreInst>(instr)) {
        shared_ptr<VarVal> ptr =
            resolveValue(store->getPointerOperand(), state);
        assert(ptr->getType() == VarType::Int);
        shared_ptr<VarVal> val = resolveValue(store->getValueOperand(), state);
        assert(val->getType() == VarType::Int);
        HeapAddress addr = static_pointer_cast<VarInt>(ptr)->val;
        state.heap[addr] = *static_pointer_cast<VarInt>(val);
        return state;
    } else {
        logErrorData("unsupported instruction:\n", *instr);
        return state;
    }
}

State interpretPHI(const PHINode &instr, State state,
                   const BasicBlock *prevBlock) {
    const Value *val = instr.getIncomingValueForBlock(prevBlock);
    shared_ptr<VarVal> var = resolveValue(val, state);
    state.variables[instr.getName()] = var;
    return state;
}

TerminatorUpdate interpretTerminator(const TerminatorInst *instr, State state) {
    if (const auto retInst = dyn_cast<ReturnInst>(instr)) {
        state.variables[ReturnName] =
            resolveValue(retInst->getReturnValue(), state);
        return TerminatorUpdate(state, nullptr);
    } else if (const auto branchInst = dyn_cast<BranchInst>(instr)) {
        if (branchInst->isUnconditional()) {
            assert(branchInst->getNumSuccessors() == 1);
            return TerminatorUpdate(state, branchInst->getSuccessor(0));
        } else {
            shared_ptr<VarVal> cond =
                resolveValue(branchInst->getCondition(), state);
            assert(cond->getType() == VarType::Bool);
            bool condVal = static_pointer_cast<VarBool>(cond)->val;
            assert(branchInst->getNumSuccessors() == 2);
            if (condVal) {
                return TerminatorUpdate(state, branchInst->getSuccessor(0));
            } else {
                return TerminatorUpdate(state, branchInst->getSuccessor(1));
            }
        }
    } else {
        logError("Only return and branches are supported\n");
        return TerminatorUpdate(state, nullptr);
    }
}

shared_ptr<VarVal> resolveValue(const Value *val, State state) {
    if (isa<Instruction>(val) || isa<Argument>(val)) {
        logWarning("Reading: " + val->getName() + "\n");
        return state.variables.at(val->getName());
    } else if (const auto constInt = dyn_cast<ConstantInt>(val)) {
        return make_shared<VarInt>(constInt->getSExtValue());
    }
    logErrorData("Operators are not yet handled\n", *val);
    return make_shared<VarInt>(42);
}

State interpretICmpInst(const ICmpInst *instr, State state) {
    assert(instr->getNumOperands() == 2);
    const auto op0 = resolveValue(instr->getOperand(0), state);
    const auto op1 = resolveValue(instr->getOperand(1), state);
    switch (instr->getPredicate()) {
    default:
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        mpz_class i0 = static_pointer_cast<VarInt>(op0)->val;
        mpz_class i1 = static_pointer_cast<VarInt>(op1)->val;
        return interpretIntPredicate(instr->getName(), instr->getPredicate(),
                                     i0, i1, state);
    }
}

State interpretIntPredicate(string name, CmpInst::Predicate pred, mpz_class i0,
                            mpz_class i1, State state) {
    bool predVal = false;
    switch (pred) {
    case CmpInst::ICMP_SGE:
        predVal = i0 >= i1;
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
        logError("Unsupported predicate\n");
    }
    state.variables[name] = make_shared<VarBool>(predVal);
    return state;
}

State interpretBinOp(const BinaryOperator *instr, State state) {
    const auto op0 = resolveValue(instr->getOperand(0), state);
    const auto op1 = resolveValue(instr->getOperand(1), state);
    switch (instr->getOpcode()) {
    default:
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        mpz_class i0 = static_pointer_cast<VarInt>(op0)->val;
        mpz_class i1 = static_pointer_cast<VarInt>(op1)->val;
        return interpretIntBinOp(instr->getName(), instr->getOpcode(), i0, i1,
                                 state);
    }
}

State interpretIntBinOp(string name, Instruction::BinaryOps op, mpz_class i0,
                        mpz_class i1, State state) {
    mpz_class result = 0;
    switch (op) {
    case Instruction::Add:
        result = i0 + i1;
        break;
    case Instruction::Sub:
        result = i0 - i1;
        break;
    default:
        logError("Unsupported binop\n");
    }
    state.variables[name] = make_shared<VarInt>(result);
    return state;
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
    return j;
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

json stateToJSON(State state) {
    map<string, json> jsonVariables;
    map<string, json> jsonHeap;
    for (auto var : state.variables) {
        jsonVariables.insert({var.first, var.second->toJSON()});
    }
    for (auto index : state.heap) {
        jsonHeap.insert({index.first.get_str(), index.second.val.get_str()});
    }
    json j;
    j["variables"] = jsonVariables;
    j["heap"] = jsonHeap;
    return j;
}
