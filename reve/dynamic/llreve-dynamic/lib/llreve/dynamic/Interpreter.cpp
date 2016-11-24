/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Interpreter.h"

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
using std::function;

using nlohmann::json;

using namespace llreve::opts;

namespace llreve {
namespace dynamic {
VarVal::VarValConcept::~VarValConcept() = default;

unsigned HeapElemSizeFlag;
static llreve::cl::opt<unsigned, true> // The parser
    HeapElemSize("heap-elem-size",
                 llreve::cl::desc("Size for a random heap element"),
                 llreve::cl::location(HeapElemSizeFlag), llreve::cl::init(8));

VarType getType(const VarIntVal & /* unused */) { return VarType::Int; }
json toJSON(const VarIntVal &v) { return v.get_str(); }
VarIntVal unsafeIntVal(const VarIntVal &v) { return v; }
const VarIntVal &unsafeIntValRef(const VarIntVal &v) { return v; }
bool unsafeBool(const VarIntVal & /* unused */) {
    logError("Called unsafeBool on an int\n");
    exit(1);
}

VarType getType(const bool & /* unused */) { return VarType::Bool; }
json toJSON(const bool &b) { return json(b); }
VarIntVal unsafeIntVal(const bool & /* unused */) {
    logError("Called unsafeIntVal on a bool\n");
    exit(1);
}
const VarIntVal &unsafeIntValRef(const bool & /* unused */) {
    logError("Called unsafeIntVal on a bool\n");
    exit(1);
}
bool unsafeBool(const bool &b) { return b; }

MonoPair<FastCall>
interpretFunctionPair(MonoPair<const Function *> funs,
                      MonoPair<FastVarMap> variables, MonoPair<Heap> heaps,
                      MonoPair<Integer> heapBackgrounds, uint32_t maxSteps,
                      const AnalysisResultsMap &analysisResults) {
    return makeMonoPair(
        interpretFunction(*funs.first, FastState(variables.first, heaps.first,
                                                 heapBackgrounds.first),
                          maxSteps, analysisResults),
        interpretFunction(
            *funs.second,
            FastState(variables.second, heaps.second, heapBackgrounds.second),
            maxSteps, analysisResults));
}

MonoPair<FastCall> interpretFunctionPair(
    MonoPair<const llvm::Function *> funs, MonoPair<FastVarMap> variables,
    MonoPair<Heap> heaps, MonoPair<Integer> heapBackgrounds,
    MonoPair<const llvm::BasicBlock *> startBlocks, uint32_t maxSteps,
    const AnalysisResultsMap &analysisResults) {
    return makeMonoPair(
        interpretFunction(*funs.first, FastState(variables.first, heaps.first,
                                                 heapBackgrounds.first),
                          startBlocks.first, maxSteps, analysisResults),
        interpretFunction(
            *funs.second,
            FastState(variables.second, heaps.second, heapBackgrounds.second),
            startBlocks.second, maxSteps, analysisResults));
}

FastCall interpretFunction(const Function &fun, FastState entry,
                           const llvm::BasicBlock *startBlock,
                           uint32_t maxSteps,
                           const AnalysisResultsMap &analysisResults) {
    const BasicBlock *prevBlock = nullptr;
    const BasicBlock *currentBlock = startBlock;
    vector<BlockStep<const llvm::Value *>> steps;
    FastState currentState = entry;
    BlockUpdate<const llvm::Value *> update;
    uint32_t blocksVisited = 0;
    bool firstBlock = true;
    do {
        update =
            interpretBlock(*currentBlock, prevBlock, currentState, firstBlock,
                           maxSteps - blocksVisited, analysisResults);
        firstBlock = false;
        blocksVisited += update.blocksVisited;
        steps.push_back(BlockStep<const llvm::Value *>(
            currentBlock->getName(), std::move(update.step),
            std::move(update.calls)));
        prevBlock = currentBlock;
        currentBlock = update.nextBlock;
        if (blocksVisited > maxSteps || update.earlyExit) {
            return FastCall(&fun, std::move(entry), std::move(currentState),
                            std::move(steps), true, blocksVisited);
        }
    } while (currentBlock != nullptr);
    return FastCall(&fun, std::move(entry), std::move(currentState),
                    std::move(steps), false, blocksVisited);
}

FastCall interpretFunction(const Function &fun, FastState entry,
                           uint32_t maxSteps,
                           const AnalysisResultsMap &analysisResults) {
    return interpretFunction(fun, entry, &fun.getEntryBlock(), maxSteps,
                             analysisResults);
}

BlockUpdate<const llvm::Value *>
interpretBlock(const BasicBlock &block, const BasicBlock *prevBlock,
               FastState &state, bool skipPhi, uint32_t maxSteps,
               const AnalysisResultsMap &analysisResults) {
    uint32_t blocksVisited = 1;
    const Instruction *firstNonPhi = block.getFirstNonPHI();
    const Instruction *terminator = block.getTerminator();
    // Handle phi instructions
    BasicBlock::const_iterator instrIterator;
    for (instrIterator = block.begin(); &*instrIterator != firstNonPhi;
         ++instrIterator) {
        const Instruction *inst = &*instrIterator;
        assert(isa<PHINode>(inst));
        if (!skipPhi) {
            interpretPHI(*dyn_cast<PHINode>(inst), state, prevBlock);
        }
    }
    FastState step(state);

    vector<FastCall> calls;
    // Handle non phi instructions
    for (; &*instrIterator != terminator; ++instrIterator) {
        if (const auto call = dyn_cast<llvm::CallInst>(&*instrIterator)) {
            const Function *fun = call->getCalledFunction();
            FastVarMap args;
            auto argIt = fun->getArgumentList().begin();
            for (const auto &arg : call->arg_operands()) {
                args.insert(std::make_pair(
                    &*argIt, resolveValue(arg, state, arg->getType())));
                ++argIt;
            }
            FastCall c = interpretFunction(
                *fun, FastState(args, state.heap, state.heapBackground),
                maxSteps - blocksVisited, analysisResults);
            blocksVisited += c.blocksVisited;
            if (blocksVisited > maxSteps || c.earlyExit) {
                return BlockUpdate<const llvm::Value *>(
                    std::move(step), nullptr, std::move(calls), true,
                    blocksVisited);
            }
            state.heap = c.returnState.heap;
            state.variables[call] =
                c.returnState
                    .variables[analysisResults.at(fun).returnInstruction];
            calls.push_back(std::move(c));
        } else {
            interpretInstruction(&*instrIterator, state);
        }
    }

    // Terminator instruction
    TerminatorUpdate update = interpretTerminator(block.getTerminator(), state);

    return BlockUpdate<const llvm::Value *>(std::move(step), update.nextBlock,
                                            std::move(calls), false,
                                            blocksVisited);
}

void interpretInstruction(const Instruction *instr, FastState &state) {
    if (const auto binOp = dyn_cast<BinaryOperator>(instr)) {
        interpretBinOp(binOp, state);
    } else if (const auto icmp = dyn_cast<ICmpInst>(instr)) {
        interpretICmpInst(icmp, state);
    } else if (const auto cast = dyn_cast<CastInst>(instr)) {
        assert(cast->getNumOperands() == 1);
        if (cast->getSrcTy()->isIntegerTy(1) &&
            cast->getDestTy()->getIntegerBitWidth() > 1) {
            // Convert a bool to an integer
            VarVal operand = state.variables.at(cast->getOperand(0));
            assert(getType(operand) == VarType::Bool);
            if (SMTGenerationOpts::getInstance().BitVect) {
                state.variables[cast] = Integer(
                    makeBoundedInt(cast->getType()->getIntegerBitWidth(),
                                   unsafeBool(operand) ? 1 : 0));
            } else {
                state.variables[cast] =
                    Integer(mpz_class(unsafeBool(operand) ? 1 : 0));
            }
        } else {
            if (const auto zext = dyn_cast<llvm::ZExtInst>(instr)) {
                state.variables[zext] =
                    unsafeIntVal(resolveValue(zext->getOperand(0), state,
                                              zext->getType()))
                        .zext(zext->getType()->getIntegerBitWidth());
            } else if (const auto sext = dyn_cast<llvm::SExtInst>(instr)) {
                state.variables[sext] =
                    unsafeIntVal(resolveValue(sext->getOperand(0), state,
                                              sext->getType()))
                        .sext(sext->getType()->getIntegerBitWidth());
            } else if (const auto trunc = dyn_cast<llvm::TruncInst>(instr)) {
                state.variables[trunc] =
                    unsafeIntVal(resolveValue(trunc->getOperand(0), state,
                                              trunc->getType()))
                        .zextOrTrunc(trunc->getType()->getIntegerBitWidth());
            } else if (const auto ptrToInt =
                           dyn_cast<llvm::PtrToIntInst>(instr)) {
                state.variables[ptrToInt] =
                    unsafeIntVal(
                        resolveValue(ptrToInt->getPointerOperand(), state,
                                     ptrToInt->getPointerOperand()->getType()))
                        .zextOrTrunc(ptrToInt->getType()->getIntegerBitWidth());
            } else if (const auto intToPtr =
                           dyn_cast<llvm::IntToPtrInst>(instr)) {
                state.variables[ptrToInt] =
                    unsafeIntVal(
                        resolveValue(intToPtr->getOperand(0), state,
                                     intToPtr->getOperand(0)->getType()))
                        .zextOrTrunc(64);
            } else {
                logErrorData("Unsupported instruction:\n", *instr);
                exit(1);
            }
        }
    } else if (const auto gep = dyn_cast<GetElementPtrInst>(instr)) {
        state.variables[gep] = resolveGEP(*gep, state);
    } else if (const auto load = dyn_cast<LoadInst>(instr)) {
        VarVal ptr =
            resolveValue(load->getPointerOperand(), state, load->getPointerOperand()->getType());
        assert(getType(ptr) == VarType::Int);
        // This will only insert 0 if there is not already a different element
        if (SMTGenerationOpts::getInstance().BitVect) {
            unsigned bytes = load->getType()->getIntegerBitWidth() / 8;
            llvm::APInt val =
                makeBoundedInt(load->getType()->getIntegerBitWidth(), 0);
            for (unsigned i = 0; i < bytes; ++i) {
                auto heapIt = state.heap.insert(std::make_pair(
                    unsafeIntVal(ptr).asPointer() +
                        Integer(mpz_class(i)).asPointer(),
                    Integer(makeBoundedInt(
                        8, state.heapBackground.asUnbounded().get_si()))));
                assert(heapIt.first->second.type == IntType::Bounded);
                assert(heapIt.first->second.bounded.getBitWidth() == 8);
                val = (val << 8) |
                      (heapIt.first->second.bounded).sextOrSelf(bytes * 8);
            }
            state.variables[load] = Integer(val);
        } else {
            auto heapIt = state.heap.insert(std::make_pair(
                unsafeIntVal(ptr).asPointer(), state.heapBackground));
            state.variables[load] = heapIt.first->second;
        }
    } else if (const auto store = dyn_cast<StoreInst>(instr)) {
        VarVal ptr = resolveValue(store->getPointerOperand(), state,
                                  store->getPointerOperand()->getType());
        assert(getType(ptr) == VarType::Int);
        HeapAddress addr = unsafeIntVal(ptr);
        VarIntVal val =
            unsafeIntVal(resolveValue(store->getValueOperand(), state,
                                      store->getValueOperand()->getType()));
        if (SMTGenerationOpts::getInstance().BitVect) {
            int bytes =
                store->getValueOperand()->getType()->getIntegerBitWidth() / 8;
            assert(val.type == IntType::Bounded);
            llvm::APInt bval = val.bounded;
            if (bytes == 1) {
                state.heap[addr] = val;
            } else {
                uint64_t i = 0;
                for (; bytes >= 0; --bytes) {
                    llvm::APInt el = bval.trunc(8);
                    bval = bval.ashr(8);
                    state.heap[addr + Integer(llvm::APInt(
                                          64, static_cast<uint64_t>(bytes)))] =
                        Integer(el);
                    ++i;
                }
            }
        } else {
            state.heap[addr] = val;
        }
    } else if (const auto select = dyn_cast<SelectInst>(instr)) {
        VarVal cond = resolveValue(select->getCondition(), state,
                                   select->getCondition()->getType());
        assert(getType(cond) == VarType::Bool);
        bool condVal = unsafeBool(cond);
        if (condVal) {
            VarVal var =
                resolveValue(select->getTrueValue(), state, select->getType());
            state.variables[select] = var;
        } else {
            VarVal var =
                resolveValue(select->getFalseValue(), state, select->getType());
            state.variables[select] = var;
        }

    } else {
        logErrorData("unsupported instruction:\n", *instr);
    }
}

void interpretPHI(const PHINode &instr, FastState &state,
                  const BasicBlock *prevBlock) {
    const Value *val = instr.getIncomingValueForBlock(prevBlock);
    VarVal var = resolveValue(val, state, val->getType());
    state.variables[&instr] = var;
}

TerminatorUpdate interpretTerminator(const TerminatorInst *instr,
                                     FastState &state) {
    if (const auto retInst = dyn_cast<ReturnInst>(instr)) {
        if (retInst->getReturnValue() == nullptr) {
            state.variables[retInst] = 0;
        } else {
            state.variables[retInst] =
                resolveValue(retInst->getReturnValue(), state,
                             retInst->getReturnValue()->getType());
        }
        return TerminatorUpdate(nullptr);
    } else if (const auto branchInst = dyn_cast<BranchInst>(instr)) {
        if (branchInst->isUnconditional()) {
            assert(branchInst->getNumSuccessors() == 1);
            return TerminatorUpdate(branchInst->getSuccessor(0));
        } else {
            VarVal cond = resolveValue(branchInst->getCondition(), state,
                                       branchInst->getCondition()->getType());
            assert(getType(cond) == VarType::Bool);
            bool condVal = unsafeBool(cond);
            assert(branchInst->getNumSuccessors() == 2);
            if (condVal) {
                return TerminatorUpdate(branchInst->getSuccessor(0));
            } else {
                return TerminatorUpdate(branchInst->getSuccessor(1));
            }
        }
    } else if (const auto switchInst = dyn_cast<SwitchInst>(instr)) {
        VarVal cond = resolveValue(switchInst->getCondition(), state,
                                   switchInst->getCondition()->getType());
        assert(getType(cond) == VarType::Int);
        const VarIntVal &condVal = unsafeIntVal(cond);
        for (auto c : switchInst->cases()) {
            VarIntVal caseVal;
            if (SMTGenerationOpts::getInstance().BitVect) {
                caseVal = Integer(c.getCaseValue()->getValue());
            } else {
                caseVal = Integer(mpz_class(c.getCaseValue()->getSExtValue()));
            }
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

VarVal resolveValue(const Value *val, const FastState &state,
                    const llvm::Type * /* unused */) {
    if (isa<Instruction>(val) || isa<Argument>(val)) {
        return state.variables.at(val);
    } else if (const auto constInt = dyn_cast<ConstantInt>(val)) {
        if (constInt->getBitWidth() == 1) {
            return constInt->isOne();
        } else if (!SMTGenerationOpts::getInstance().BitVect) {
            return Integer(mpz_class(constInt->getSExtValue()));
        } else {
            return Integer(constInt->getValue());
        }
    } else if (llvm::isa<llvm::ConstantPointerNull>(val)) {
        return Integer(makeBoundedInt(64, 0));
    }
    logErrorData("Operators are not yet handled\n", *val);
    exit(1);
}

void interpretICmpInst(const ICmpInst *instr, FastState &state) {
    assert(instr->getNumOperands() == 2);
    const VarVal op0 = resolveValue(instr->getOperand(0), state,
                                    instr->getOperand(0)->getType());
    const VarVal op1 = resolveValue(instr->getOperand(1), state,
                                    instr->getOperand(0)->getType());
    switch (instr->getPredicate()) {
    default:
        assert(getType(op0) == VarType::Int);
        assert(getType(op1) == VarType::Int);
        const VarIntVal &i0 = unsafeIntVal(op0);
        const VarIntVal &i1 = unsafeIntVal(op1);
        interpretIntPredicate(instr, instr->getPredicate(), i0, i1, state);
    }
}

void interpretIntPredicate(const ICmpInst *instr, CmpInst::Predicate pred,
                           const VarIntVal &i0, const VarIntVal &i1,
                           FastState &state) {
    bool predVal = false;
    switch (pred) {
    case CmpInst::ICMP_EQ:
        predVal = i0.eq(i1);
        break;
    case CmpInst::ICMP_NE:
        predVal = i0.ne(i1);
        break;
    case CmpInst::ICMP_SGE:
        predVal = i0.sge(i1);
        break;
    case CmpInst::ICMP_SGT:
        predVal = i0.sgt(i1);
        break;
    case CmpInst::ICMP_SLE:
        predVal = i0.sle(i1);
        break;
    case CmpInst::ICMP_SLT:
        predVal = i0.slt(i1);
        break;
    case CmpInst::ICMP_UGE:
        predVal = i0.uge(i1);
        break;
    case CmpInst::ICMP_UGT:
        predVal = i0.ugt(i1);
        break;
    case CmpInst::ICMP_ULE:
        predVal = i0.ule(i1);
        break;
    case CmpInst::ICMP_ULT:
        predVal = i0.ult(i1);
        break;
    default:
        logErrorData("Unsupported predicate:\n", *instr);
    }
    state.variables[instr] = predVal;
}

void interpretBinOp(const BinaryOperator *instr, FastState &state) {
    const VarVal op0 = resolveValue(instr->getOperand(0), state,
                                    instr->getOperand(0)->getType());
    const VarVal op1 = resolveValue(instr->getOperand(1), state,
                                    instr->getOperand(1)->getType());
    if (instr->getType()->getIntegerBitWidth() == 1) {
        assert(getType(op0) == VarType::Bool);
        assert(getType(op1) == VarType::Bool);
        bool b0 = unsafeBool(op0);
        bool b1 = unsafeBool(op1);
        interpretBoolBinOp(instr, instr->getOpcode(), b0, b1, state);
    } else {
        assert(getType(op0) == VarType::Int);
        assert(getType(op1) == VarType::Int);
        const VarIntVal &i0 = unsafeIntVal(op0);
        const VarIntVal &i1 = unsafeIntVal(op1);
        interpretIntBinOp(instr, instr->getOpcode(), i0, i1, state);
    }
}

void interpretBoolBinOp(const BinaryOperator *instr, Instruction::BinaryOps op,
                        bool b0, bool b1, FastState &state) {
    bool result = false;
    switch (op) {
    case Instruction::Or:
        result = b0 || b1;
        break;
    case Instruction::And:
        result = b0 && b1;
        break;
    default:
        logErrorData("Unsupported binop:\n", *instr);
        llvm::errs() << "\n";
    }
    state.variables[instr] = result;
}

void interpretIntBinOp(const BinaryOperator *instr, Instruction::BinaryOps op,
                       const VarIntVal &i0, const VarIntVal &i1,
                       FastState &state) {
    VarIntVal result;
    switch (op) {
    case Instruction::Add:
        result = i0 + i1;
        break;
    case Instruction::Sub:
        result = i0 - i1;
        break;
    case Instruction::Mul:
        result = i0 * i1;
        break;
    case Instruction::SDiv:
        result = i0.sdiv(i1);
        break;
    case Instruction::UDiv:
        result = i0.udiv(i1);
        break;
    case Instruction::SRem:
        result = i0.srem(i1);
        break;
    case Instruction::URem:
        result = i0.urem(i1);
        break;
    case Instruction::Shl:
        result = i0.shl(i1);
        break;
    case Instruction::LShr:
        result = i0.lshr(i1);
        break;
    case Instruction::AShr:
        result = i0.ashr(i1);
        break;
    case Instruction::And:
        result = i0.and_(i1);
        break;
    case Instruction::Or:
        result = i0.or_(i1);
        break;
    case Instruction::Xor:
        result = i0.xor_(i1);
        break;
    default:
        logErrorData("Unsupported binop:\n", *instr);
        llvm::errs() << "\n";
    }
    state.variables[instr] = result;
}

bool varValEq(const VarVal &lhs, const VarVal &rhs) {
    if (getType(lhs) != getType(rhs)) {
        return false;
    } else if (getType(lhs) == VarType::Bool) {
        const bool lhsB = unsafeBool(lhs);
        const bool rhsB = unsafeBool(rhs);
        return lhsB == rhsB;
    } else {
        const VarIntVal lhsI = unsafeIntVal(lhs);
        const VarIntVal rhsI = unsafeIntVal(rhs);
        return lhsI == rhsI;
    }
}

string valueName(const llvm::Value *val) { return val->getName(); }
template <typename T>
json stateToJSON(State<T> state, function<string(T)> getName) {
    map<string, json> jsonVariables;
    map<string, json> jsonHeap;
    for (const auto &var : state.variables) {
        string varName = getName(var.first);
        jsonVariables.insert({varName, toJSON(var.second)});
    }
    for (const auto &index : state.heap) {
        jsonHeap.insert({index.first.get_str(), index.second.get_str()});
    }
    json j;
    j["variables"] = jsonVariables;
    j["heap"] = jsonHeap;
    j["heapBackground"] = toJSON(state.heapBackground);
    return j;
}
}
}
