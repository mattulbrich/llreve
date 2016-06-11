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
using std::function;

using nlohmann::json;

VarVal::~VarVal() = default;

bool BoundedFlag;
unsigned HeapElemSizeFlag;
static llvm::cl::opt<bool, true> // The parser
    Bounded("bounded", llvm::cl::desc("Use bounded integers"),
            llvm::cl::location(BoundedFlag));
static llvm::cl::opt<unsigned, true> // The parser
    HeapElemSize("heap-elem-size",
                 llvm::cl::desc("Size for a random heap element"),
                 llvm::cl::location(HeapElemSizeFlag), llvm::cl::init(8));

VarType VarInt::getType() const { return VarType::Int; }
VarIntVal VarInt::unsafeIntVal() const { return val; }
VarType VarBool::getType() const { return VarType::Bool; }
VarIntVal VarBool::unsafeIntVal() const {
    logError("Called unsafeIntVal on a VarBool\n");
    exit(1);
}

json VarInt::toJSON() const { return val.get_str(); }
json VarBool::toJSON() const { return json(val); }

MonoPair<FastCall> interpretFunctionPair(
    MonoPair<const Function *> funs,
    MonoPair<map<const llvm::Value *, shared_ptr<VarVal>>> variables,
    MonoPair<Heap> heaps, MonoPair<Integer> heapBackgrounds,
    uint32_t maxSteps) {
    return makeMonoPair(
        interpretFunction(*funs.first, FastState(variables.first, heaps.first,
                                                 heapBackgrounds.first),
                          maxSteps),
        interpretFunction(
            *funs.second,
            FastState(variables.second, heaps.second, heapBackgrounds.second),
            maxSteps));
}

MonoPair<FastCall> interpretFunctionPair(
    MonoPair<const llvm::Function *> funs,
    MonoPair<std::map<const llvm::Value *, std::shared_ptr<VarVal>>> variables,
    MonoPair<Heap> heaps, MonoPair<Integer> heapBackgrounds,
    MonoPair<const llvm::BasicBlock *> startBlocks, uint32_t maxSteps) {
    return makeMonoPair(
        interpretFunction(*funs.first, FastState(variables.first, heaps.first,
                                                 heapBackgrounds.first),
                          startBlocks.first, maxSteps),
        interpretFunction(
            *funs.second,
            FastState(variables.second, heaps.second, heapBackgrounds.second),
            startBlocks.second, maxSteps));
}

FastCall interpretFunction(const Function &fun, FastState entry,
                           const llvm::BasicBlock *startBlock,
                           uint32_t maxSteps) {
    const BasicBlock *prevBlock = nullptr;
    const BasicBlock *currentBlock = startBlock;
    vector<shared_ptr<BlockStep<const llvm::Value *>>> steps;
    FastState currentState = entry;
    BlockUpdate<const llvm::Value *> update;
    uint32_t blocksVisited = 0;
    bool firstBlock = true;
    do {
        update = interpretBlock(*currentBlock, prevBlock, currentState,
                                firstBlock,
                                maxSteps - blocksVisited);
        firstBlock = false;
        blocksVisited += update.blocksVisited;
        steps.push_back(make_shared<BlockStep<const llvm::Value *>>(
            currentBlock->getName(), std::move(update.step),
            std::move(update.calls)));
        prevBlock = currentBlock;
        currentBlock = update.nextBlock;
        if (blocksVisited > maxSteps || update.earlyExit) {
            return FastCall(fun.getName(), std::move(entry),
                            std::move(currentState), std::move(steps), true,
                            blocksVisited);
        }
    } while (currentBlock != nullptr);
    return FastCall(fun.getName(), std::move(entry), std::move(currentState),
                    std::move(steps), false, blocksVisited);
}

FastCall interpretFunction(const Function &fun, FastState entry,
                           uint32_t maxSteps) {
    return interpretFunction(fun, entry, &fun.getEntryBlock(), maxSteps);
}

BlockUpdate<const llvm::Value *> interpretBlock(const BasicBlock &block,
                                                const BasicBlock *prevBlock,
                                                FastState &state, bool skipPhi,
                                                uint32_t maxSteps) {
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
            const Function *fun = call->getFunction();
            FastVarMap args;
            auto argIt = fun->getArgumentList().begin();
            for (const auto &arg : call->arg_operands()) {
                args.insert(std::make_pair(
                    &*argIt, resolveValue(arg, state, arg->getType())));
                ++argIt;
            }
            FastCall c = interpretFunction(
                *fun, FastState(args, state.heap, state.heapBackground),
                maxSteps - blocksVisited);
            blocksVisited += c.blocksVisited;
            if (blocksVisited > maxSteps || c.earlyExit) {
                return BlockUpdate<const llvm::Value *>(
                    std::move(step), nullptr, std::move(calls), true,
                    blocksVisited);
            }
            state.heap = c.returnState.heap;
            state.variables[call] = c.returnState.variables[ReturnName];
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
            shared_ptr<VarVal> operand =
                state.variables.at(cast->getOperand(0));
            assert(operand->getType() == VarType::Bool);
            if (BoundedFlag) {
                state.variables[cast] =
                    make_shared<VarInt>(Integer(makeBoundedInt(
                        cast->getType()->getIntegerBitWidth(),
                        static_pointer_cast<VarBool>(operand)->val ? 1 : 0)));
            } else {
                state.variables[cast] = make_shared<VarInt>(Integer(mpz_class(
                    static_pointer_cast<VarBool>(operand)->val ? 1 : 0)));
            }
        } else {
            if (const auto zext = dyn_cast<llvm::ZExtInst>(instr)) {
                state.variables[zext] = std::make_shared<VarInt>(
                    resolveValue(zext->getOperand(0), state, zext->getType())
                        ->unsafeIntVal()
                        .zext(zext->getType()->getIntegerBitWidth()));
            } else if (const auto sext = dyn_cast<llvm::SExtInst>(instr)) {
                state.variables[sext] = std::make_shared<VarInt>(
                    resolveValue(sext->getOperand(0), state, sext->getType())
                        ->unsafeIntVal()
                        .sext(sext->getType()->getIntegerBitWidth()));
            } else if (const auto ptrToInt =
                           dyn_cast<llvm::PtrToIntInst>(instr)) {
                state.variables[ptrToInt] = std::make_shared<VarInt>(
                    resolveValue(ptrToInt->getPointerOperand(), state,
                                 ptrToInt->getPointerOperand()->getType())
                        ->unsafeIntVal()
                        .zextOrTrunc(
                            ptrToInt->getType()->getIntegerBitWidth()));
            } else if (const auto intToPtr =
                           dyn_cast<llvm::IntToPtrInst>(instr)) {
                state.variables[ptrToInt] = std::make_shared<VarInt>(
                    resolveValue(intToPtr->getOperand(0), state,
                                 intToPtr->getOperand(0)->getType())
                        ->unsafeIntVal()
                        .zextOrTrunc(64));
            }
        }
    } else if (const auto gep = dyn_cast<GetElementPtrInst>(instr)) {
        state.variables[gep] = make_shared<VarInt>(resolveGEP(*gep, state));
    } else if (const auto load = dyn_cast<LoadInst>(instr)) {
        shared_ptr<VarVal> ptr =
            resolveValue(load->getPointerOperand(), state, load->getType());
        assert(ptr->getType() == VarType::Int);
        // This will only insert 0 if there is not already a different element
        if (BoundedFlag) {
            unsigned bytes = load->getType()->getIntegerBitWidth() / 8;
            llvm::APInt val =
                makeBoundedInt(load->getType()->getIntegerBitWidth(), 0);
            for (unsigned i = 0; i < bytes; ++i) {
                auto heapIt = state.heap.insert(std::make_pair(
                    static_pointer_cast<VarInt>(ptr)->val.asPointer() +
                        Integer(mpz_class(i)).asPointer(),
                    Integer(makeBoundedInt(
                        8, state.heapBackground.asUnbounded().get_si()))));
                assert(heapIt.first->second.type == IntType::Bounded);
                assert(heapIt.first->second.bounded.getBitWidth() == 8);
                val = (val << 8) |
                      (heapIt.first->second.bounded).sextOrSelf(bytes * 8);
            }
            state.variables[load] = make_shared<VarInt>(Integer(val));
        } else {
            auto heapIt = state.heap.insert(std::make_pair(
                static_pointer_cast<VarInt>(ptr)->val.asPointer(),
                state.heapBackground));
            state.variables[load] = make_shared<VarInt>(heapIt.first->second);
        }
    } else if (const auto store = dyn_cast<StoreInst>(instr)) {
        shared_ptr<VarVal> ptr =
            resolveValue(store->getPointerOperand(), state,
                         store->getPointerOperand()->getType());
        assert(ptr->getType() == VarType::Int);
        HeapAddress addr = static_pointer_cast<VarInt>(ptr)->val;
        VarIntVal val = resolveValue(store->getValueOperand(), state,
                                     store->getValueOperand()->getType())
                            ->unsafeIntVal();
        if (BoundedFlag) {
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
        shared_ptr<VarVal> cond = resolveValue(
            select->getCondition(), state, select->getCondition()->getType());
        assert(cond->getType() == VarType::Bool);
        bool condVal = static_pointer_cast<VarBool>(cond)->val;
        shared_ptr<VarVal> var;
        if (condVal) {
            var =
                resolveValue(select->getTrueValue(), state, select->getType());
        } else {
            var =
                resolveValue(select->getFalseValue(), state, select->getType());
        }
        state.variables[select] = var;
    } else {
        logErrorData("unsupported instruction:\n", *instr);
    }
}

void interpretPHI(const PHINode &instr, FastState &state,
                  const BasicBlock *prevBlock) {
    const Value *val = instr.getIncomingValueForBlock(prevBlock);
    shared_ptr<VarVal> var = resolveValue(val, state, val->getType());
    state.variables[&instr] = var;
}

TerminatorUpdate interpretTerminator(const TerminatorInst *instr,
                                     FastState &state) {
    if (const auto retInst = dyn_cast<ReturnInst>(instr)) {
        state.variables[ReturnName] =
            resolveValue(retInst->getReturnValue(), state,
                         retInst->getReturnValue()->getType());
        return TerminatorUpdate(nullptr);
    } else if (const auto branchInst = dyn_cast<BranchInst>(instr)) {
        if (branchInst->isUnconditional()) {
            assert(branchInst->getNumSuccessors() == 1);
            return TerminatorUpdate(branchInst->getSuccessor(0));
        } else {
            shared_ptr<VarVal> cond =
                resolveValue(branchInst->getCondition(), state,
                             branchInst->getCondition()->getType());
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
            resolveValue(switchInst->getCondition(), state,
                         switchInst->getCondition()->getType());
        assert(cond->getType() == VarType::Int);
        const VarIntVal &condVal = static_pointer_cast<VarInt>(cond)->val;
        for (auto c : switchInst->cases()) {
            VarIntVal caseVal;
            if (BoundedFlag) {
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

shared_ptr<VarVal> resolveValue(const Value *val, const FastState &state,
                                const llvm::Type *type) {
    if (isa<Instruction>(val) || isa<Argument>(val)) {
        return state.variables.at(val);
    } else if (const auto constInt = dyn_cast<ConstantInt>(val)) {
        if (constInt->getBitWidth() == 1) {
            return make_shared<VarBool>(constInt->isOne());
        } else if (!BoundedFlag) {
            return make_shared<VarInt>(
                Integer(mpz_class(constInt->getSExtValue())));
        } else {
            return make_shared<VarInt>(Integer(constInt->getValue()));
        }
    } else if (llvm::isa<llvm::ConstantPointerNull>(val)) {
        return make_shared<VarInt>(Integer(makeBoundedInt(64, 0)));
    }
    logErrorData("Operators are not yet handled\n", *val);
    exit(1);
}

void interpretICmpInst(const ICmpInst *instr, FastState &state) {
    assert(instr->getNumOperands() == 2);
    const auto op0 = resolveValue(instr->getOperand(0), state,
                                  instr->getOperand(0)->getType());
    const auto op1 = resolveValue(instr->getOperand(1), state,
                                  instr->getOperand(0)->getType());
    switch (instr->getPredicate()) {
    default:
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        const VarIntVal &i0 = static_pointer_cast<VarInt>(op0)->val;
        const VarIntVal &i1 = static_pointer_cast<VarInt>(op1)->val;
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
    state.variables[instr] = make_shared<VarBool>(predVal);
}

void interpretBinOp(const BinaryOperator *instr, FastState &state) {
    const auto op0 = resolveValue(instr->getOperand(0), state,
                                  instr->getOperand(0)->getType());
    const auto op1 = resolveValue(instr->getOperand(1), state,
                                  instr->getOperand(1)->getType());
    if (instr->getType()->getIntegerBitWidth() == 1) {
        assert(op0->getType() == VarType::Bool);
        assert(op1->getType() == VarType::Bool);
        bool b0 = static_pointer_cast<VarBool>(op0)->val;
        bool b1 = static_pointer_cast<VarBool>(op1)->val;
        interpretBoolBinOp(instr, instr->getOpcode(), b0, b1, state);
    } else {
        assert(op0->getType() == VarType::Int);
        assert(op1->getType() == VarType::Int);
        const VarIntVal &i0 = static_pointer_cast<VarInt>(op0)->val;
        const VarIntVal &i1 = static_pointer_cast<VarInt>(op1)->val;
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
    default:
        logErrorData("Unsupported binop:\n", *instr);
        llvm::errs() << "\n";
    }
    state.variables[instr] = make_shared<VarBool>(result);
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
    state.variables[instr] = make_shared<VarInt>(result);
}

bool varValEq(const VarVal &lhs, const VarVal &rhs) {
    if (lhs.getType() != rhs.getType()) {
        return false;
    } else if (lhs.getType() == VarType::Bool) {
        const VarBool &lhsB = static_cast<const VarBool &>(lhs);
        const VarBool &rhsB = static_cast<const VarBool &>(rhs);
        return lhsB.val == rhsB.val;
    } else {
        const VarInt &lhsI = static_cast<const VarInt &>(lhs);
        const VarInt &rhsI = static_cast<const VarInt &>(rhs);
        return lhsI.val == rhsI.val;
    }
}

string valueName(const llvm::Value *val) {
    return val == nullptr ? "return" : val->getName();
}
template <typename T>
json stateToJSON(State<T> state, function<string(T)> getName) {
    map<string, json> jsonVariables;
    map<string, json> jsonHeap;
    for (auto var : state.variables) {
        string varName = getName(var.first);
        jsonVariables.insert({varName, var.second->toJSON()});
    }
    for (auto index : state.heap) {
        jsonHeap.insert({index.first.get_str(), index.second.get_str()});
    }
    json j;
    j["variables"] = jsonVariables;
    j["heap"] = jsonHeap;
    return j;
}
