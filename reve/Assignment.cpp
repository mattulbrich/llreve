#include "Assignment.h"

#include "Helper.h"

#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Metadata.h"

using std::vector;
using std::make_shared;
using llvm::Instruction;
using llvm::CmpInst;

/// Convert a basic block to a list of assignments
vector<DefOrCallInfo> blockAssignments(const llvm::BasicBlock &BB,
                                       const llvm::BasicBlock *prevBb,
                                       bool onlyPhis, Program prog, Memory heap,
                                       bool everythingSigned) {
    const int progIndex = programIndex(prog);
    vector<DefOrCallInfo> definitions;
    assert(BB.size() >= 1); // There should be at least a terminator instruction
    bool ignorePhis = prevBb == nullptr;
    for (auto instr = BB.begin(), e = std::prev(BB.end(), 1); instr != e;
         ++instr) {
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!ignorePhis && llvm::isa<llvm::PHINode>(instr)) {
            definitions.push_back(
                DefOrCallInfo(instrAssignment(*instr, prevBb, prog, everythingSigned)));
        }
        if (!onlyPhis && !llvm::isa<llvm::PHINode>(instr)) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(instr)) {
                const auto fun = CallInst->getCalledFunction();
                if (!fun) {
                    logErrorData("Call to undeclared function\n", *CallInst);
                    exit(1);
                }
                if (fun->getIntrinsicID() == llvm::Intrinsic::memcpy) {
                    const vector<DefOrCallInfo> defs =
                        memcpyIntrinsic(CallInst, prog);
                    definitions.insert(definitions.end(), defs.begin(),
                                       defs.end());
                } else {
                    if (heap & HEAP_MASK) {
                        definitions.push_back(DefOrCallInfo(makeAssignment(
                            "HEAP$" + std::to_string(progIndex),
                            name("HEAP$" + std::to_string(progIndex)))));
                    }
                    definitions.push_back(DefOrCallInfo(
                        toCallInfo(CallInst->getName(), prog, *CallInst)));
                    if (heap & HEAP_MASK) {
                        definitions.push_back(DefOrCallInfo(makeAssignment(
                            "HEAP$" + std::to_string(progIndex),
                            name("HEAP$" + std::to_string(progIndex) +
                                 "_res"))));
                    }
                }
            } else {
                definitions.push_back(DefOrCallInfo(
                    instrAssignment(*instr, prevBb, prog, everythingSigned)));
            }
        }
    }
    if (const auto retInst =
            llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator())) {
        // TODO (moritz): use a more clever approach for void functions
        auto retName = name("0");
        if (retInst->getReturnValue() != nullptr) {
            retName =
                instrNameOrVal(retInst->getReturnValue(), retInst->getType());
        }
        definitions.push_back(DefOrCallInfo(
            makeAssignment("result$" + std::to_string(progIndex), retName)));
        if (heap & HEAP_MASK) {
            definitions.push_back(DefOrCallInfo(
                makeAssignment("HEAP$" + std::to_string(progIndex) + "_res",
                               name("HEAP$" + std::to_string(progIndex)))));
        }
    }
    return definitions;
}

/// Convert a single instruction to an assignment
std::shared_ptr<std::pair<string, SMTRef>>
instrAssignment(const llvm::Instruction &Instr, const llvm::BasicBlock *prevBb,
                Program prog, bool everythingSigned) {
    const int progIndex = programIndex(prog);
    if (const auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        if (BinOp->getOpcode() == Instruction::SDiv) {
            // This is a heuristic to remove divisions by 4 of pointer
            // subtractions
            // Since we treat every int as a single value, we expect the
            // division to return the number of elements and not the number
            // of
            // bytes
            if (const auto instr =
                    llvm::dyn_cast<llvm::Instruction>(BinOp->getOperand(0))) {
                if (const auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(
                        BinOp->getOperand(1))) {
                    if (ConstInt->getSExtValue() == 4 && isPtrDiff(*instr)) {
                        return makeAssignment(
                            BinOp->getName(),
                            instrNameOrVal(BinOp->getOperand(0),
                                           BinOp->getOperand(0)->getType()));
                    } else {
                        logWarning("Division of pointer difference by " +
                                   std::to_string(ConstInt->getSExtValue()) +
                                   "\n");
                    }
                }
            }
        }
        if (BinOp->getOpcode() == Instruction::Or ||
            BinOp->getOpcode() == Instruction::And ||
            BinOp->getOpcode() == Instruction::Xor) {
            if (!(BinOp->getOperand(0)->getType()->isIntegerTy(1) &&
                  BinOp->getOperand(1)->getType()->isIntegerTy(1))) {
                logWarningData(
                    "Bitwise operators of bitwidth > 1 is not supported\n",
                    *BinOp);
            }
        }
        return makeAssignment(
            BinOp->getName(),
            combineOp (*BinOp)(
                opName(*BinOp), instrNameOrVal(BinOp->getOperand(0),
                                               BinOp->getOperand(0)->getType()),
                instrNameOrVal(BinOp->getOperand(1),
                               BinOp->getOperand(1)->getType())));
    }
    if (const auto cmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto fun = predicateFun(*cmpInst, everythingSigned);
        const auto cmp =
            makeBinOp(predicateName(cmpInst->getPredicate()),
                      fun(instrNameOrVal(cmpInst->getOperand(0),
                                         cmpInst->getOperand(0)->getType())),
                      fun(instrNameOrVal(cmpInst->getOperand(1),
                                         cmpInst->getOperand(0)->getType())));
        return makeAssignment(cmpInst->getName(), cmp);
    }
    if (const auto phiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        const auto Val = phiInst->getIncomingValueForBlock(prevBb);
        assert(Val);
        return makeAssignment(phiInst->getName(),
                              instrNameOrVal(Val, Val->getType()));
    }
    if (const auto selectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        const auto cond = selectInst->getCondition();
        const auto trueVal = selectInst->getTrueValue();
        const auto falseVal = selectInst->getFalseValue();
        const vector<SMTRef> args = {
            instrNameOrVal(cond, cond->getType()),
            instrNameOrVal(trueVal, trueVal->getType()),
            instrNameOrVal(falseVal, falseVal->getType())};
        return makeAssignment(selectInst->getName(),
                              std::make_shared<class Op>("ite", args));
    }
    if (const auto ptrToIntInst = llvm::dyn_cast<llvm::PtrToIntInst>(&Instr)) {
        return makeAssignment(ptrToIntInst->getName(),
                              instrNameOrVal(ptrToIntInst->getPointerOperand(),
                                             ptrToIntInst->getType()));
    }
    if (const auto getElementPtrInst =
            llvm::dyn_cast<llvm::GetElementPtrInst>(&Instr)) {
        return makeAssignment(getElementPtrInst->getName(),
                              resolveGEP(*getElementPtrInst));
    }
    if (const auto loadInst = llvm::dyn_cast<llvm::LoadInst>(&Instr)) {
        SMTRef pointer = instrNameOrVal(loadInst->getOperand(0),
                                        loadInst->getOperand(0)->getType());
        const auto load = makeBinOp(
            "select", name("HEAP$" + std::to_string(progIndex)), pointer);
        return makeAssignment(loadInst->getName(), load);
    }
    if (const auto storeInst = llvm::dyn_cast<llvm::StoreInst>(&Instr)) {
        string heap = "HEAP$" + std::to_string(progIndex);
        const auto val =
            instrNameOrVal(storeInst->getValueOperand(),
                           storeInst->getValueOperand()->getType());
        const auto pointer =
            instrNameOrVal(storeInst->getPointerOperand(),
                           storeInst->getPointerOperand()->getType());
        const std::vector<SMTRef> args = {name(heap), pointer, val};
        const auto store = make_shared<Op>("store", args);
        return makeAssignment("HEAP$" + std::to_string(progIndex), store);
    }
    if (const auto truncInst = llvm::dyn_cast<llvm::TruncInst>(&Instr)) {
        const auto val = instrNameOrVal(truncInst->getOperand(0),
                                        truncInst->getOperand(0)->getType());
        return makeAssignment(truncInst->getName(), val);
    }
    const llvm::Instruction *ext = nullptr;
    if ((ext = llvm::dyn_cast<llvm::ZExtInst>(&Instr)) ||
        (ext = llvm::dyn_cast<llvm::SExtInst>(&Instr))) {
        const auto operand = ext->getOperand(0);
        const auto val = instrNameOrVal(operand, operand->getType());
        const auto retTy = ext->getType();
        if (retTy->isIntegerTy() && retTy->getIntegerBitWidth() > 1 &&
            operand->getType()->isIntegerTy(1)) {
            // Extensions are usually noops, but when we convert a boolean
            // (1bit
            // integer) to something bigger it needs to be an explicit
            // conversion
            std::vector<SMTRef> args;
            args.push_back(val);
            args.push_back(name("1"));
            args.push_back(name("0"));
            return makeAssignment(ext->getName(), make_shared<Op>("ite", args));
        } else {
            return makeAssignment(ext->getName(), val);
        }
    }
    if (const auto bitCast = llvm::dyn_cast<llvm::CastInst>(&Instr)) {
        const auto val = instrNameOrVal(bitCast->getOperand(0),
                                        bitCast->getOperand(0)->getType());
        return makeAssignment(bitCast->getName(), val);
    }
    if (const auto allocaInst = llvm::dyn_cast<llvm::AllocaInst>(&Instr)) {
        return makeAssignment(
            allocaInst->getName(),
            name(llvm::cast<llvm::MDString>(
                     allocaInst->getMetadata("reve.stack_pointer")
                         ->getOperand(0))
                     ->getString()));
    }
    logErrorData("Couldn’t convert instruction to def\n", Instr);
    return makeAssignment("UNKNOWN INSTRUCTION", name("UNKNOWN ARGS"));
}

/// Convert an LLVM predicate to an SMT predicate
string predicateName(llvm::CmpInst::Predicate pred) {
    switch (pred) {
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_ULT:
        return "<";
    case CmpInst::ICMP_SLE:
    case CmpInst::ICMP_ULE:
        return "<=";
    case CmpInst::ICMP_EQ:
        return "=";
    case CmpInst::ICMP_SGE:
    case CmpInst::ICMP_UGE:
        return ">=";
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_UGT:
        return ">";
    case CmpInst::ICMP_NE:
        return "distinct";
    default:
        return "unsupported predicate";
    }
}

/// A function that is abblied to the arguments of a predicate
std::function<SMTRef(SMTRef)> predicateFun(const llvm::CmpInst::CmpInst &cmp,
                                           bool everythingSigned) {
    if (cmp.isUnsigned() && !everythingSigned) {
        return [](SMTRef everythingSigned) { return makeUnaryOp("abs", everythingSigned); };
    }
    return [](SMTRef everythingSigned) { return everythingSigned; };
}

/// Convert an LLVM op to an SMT op
string opName(const llvm::BinaryOperator &Op) {
    switch (Op.getOpcode()) {
    case Instruction::Add:
        return "+";
    case Instruction::Sub:
        return "-";
    case Instruction::Mul:
        return "*";
    case Instruction::SDiv:
        return "div";
    case Instruction::UDiv:
        return "div";
    case Instruction::SRem:
        return "mod";
    case Instruction::URem:
        return "mod";
    case Instruction::Or:
        return "or";
    case Instruction::And:
        return "and";
    case Instruction::Xor:
        return "xor";
    case Instruction::AShr:
    case Instruction::LShr:
        return "div";
    case Instruction::Shl:
        return "*";
    default:
        logError("Unknown opcode: " + std::string(Op.getOpcodeName()) + "\n");
        return Op.getOpcodeName();
    }
}

std::function<SMTRef(string, SMTRef, SMTRef)>
combineOp(const llvm::BinaryOperator &Op) {
    if (Op.getOpcode() == Instruction::AShr ||
        Op.getOpcode() == Instruction::LShr ||
        Op.getOpcode() == Instruction::Shl) {
        // We can only do that if there is a constant on the right side
        if (const auto constInt =
                llvm::dyn_cast<llvm::ConstantInt>(Op.getOperand(1))) {
            // rounding conversion to guard for floating point errors
            uint64_t divisor =
                static_cast<uint64_t>(pow(2, constInt->getZExtValue()) + 0.5);
            return
                [divisor](string opName, SMTRef firstArg, SMTRef /*unused*/) {
                    return makeBinOp(opName, firstArg,
                                     name(std::to_string(divisor)));
                };
        } else {
            logErrorData("Only shifts by a constant are supported\n", Op);
        }
    }
    return [](string opName, SMTRef firstArg, SMTRef secondArg) {
        return makeBinOp(opName, firstArg, secondArg);
    };
}

vector<DefOrCallInfo> memcpyIntrinsic(const llvm::CallInst *callInst,
                                      Program prog) {
    const int program = programIndex(prog);
    vector<DefOrCallInfo> definitions;
    const auto castInst0 =
        llvm::dyn_cast<llvm::CastInst>(callInst->getArgOperand(0));
    const auto castInst1 =
        llvm::dyn_cast<llvm::CastInst>(callInst->getArgOperand(1));
    if (castInst0 && castInst1) {
        const auto ty0 =
            llvm::dyn_cast<llvm::PointerType>(castInst0->getSrcTy());
        const auto ty1 =
            llvm::dyn_cast<llvm::PointerType>(castInst1->getSrcTy());
        const auto StructTy0 =
            llvm::dyn_cast<llvm::StructType>(ty0->getElementType());
        const auto StructTy1 =
            llvm::dyn_cast<llvm::StructType>(ty1->getElementType());
        if (StructTy0 && StructTy1) {
            assert(StructTy0->isLayoutIdentical(StructTy1));
            const SMTRef basePointerDest =
                instrNameOrVal(callInst->getArgOperand(0),
                               callInst->getArgOperand(0)->getType());
            const SMTRef basePointerSrc =
                instrNameOrVal(callInst->getArgOperand(1),
                               callInst->getArgOperand(1)->getType());
            string heapNameSelect = "HEAP$" + std::to_string(program);
            if (isStackOp(*castInst1)) {
                heapNameSelect = "STACK$" + std::to_string(program);
            }
            string heapNameStore = "HEAP$" + std::to_string(program);
            if (isStackOp(*castInst0)) {
                heapNameStore = "STACK$" + std::to_string(program);
            }
            int i = 0;
            for (const auto elTy : StructTy0->elements()) {
                const SMTRef heapSelect = name(heapNameSelect);
                const SMTRef heapStore = name(heapNameStore);
                for (int j = 0; j < typeSize(elTy); ++j) {
                    const SMTRef select =
                        makeBinOp("select", heapSelect,
                                  makeBinOp("+", basePointerSrc,
                                            name(std::to_string(i))));
                    const vector<SMTRef> args = {
                        heapStore, makeBinOp("+", basePointerDest,
                                             name(std::to_string(i))),
                        select};
                    const SMTRef store = make_shared<Op>("store", args);
                    definitions.push_back(makeAssignment(heapNameStore, store));
                    ++i;
                }
            }
        } else {
            logError("currently only memcpy of structs is "
                     "supported\n");
            exit(1);
        }
    } else {
        logError("currently only memcpy of "
                 "bitcasted pointers is supported\n");
        exit(1);
    }
    return definitions;
}

std::shared_ptr<CallInfo> toCallInfo(string assignedTo, Program prog,
                                     const llvm::CallInst &callInst) {
    vector<SMTRef> args;
    if (assignedTo.empty()) {
        assignedTo = "res" + std::to_string(programIndex(prog));
    }
    uint32_t i = 0;
    const auto &funTy = *callInst.getFunctionType();
    const llvm::Function &fun = *callInst.getCalledFunction();
    for (auto &arg : callInst.arg_operands()) {
        args.push_back(instrNameOrVal(arg, funTy.getParamType(i)));
        ++i;
    }
    return make_shared<CallInfo>(assignedTo, fun.getName(), args,
                                 fun.isDeclaration(), fun);
}

bool isPtrDiff(const llvm::Instruction &instr) {
    if (const auto binOp = llvm::dyn_cast<llvm::BinaryOperator>(&instr)) {
        return binOp->getOpcode() == Instruction::Sub &&
               llvm::isa<llvm::PtrToIntInst>(binOp->getOperand(0)) &&
               llvm::isa<llvm::PtrToIntInst>(binOp->getOperand(1));
    }
    return false;
}

bool isStackOp(const llvm::Instruction &inst) {
    return inst.getMetadata("reve.stackop");
}

shared_ptr<Assignment> makeAssignment(string name, SMTRef val) {
    return make_shared<Assignment>(name, val);
}
