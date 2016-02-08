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
                                       const llvm::BasicBlock *PrevBB,
                                       bool OnlyPhis, Program Prog, Memory Heap,
                                       bool Signed) {
    const int ProgramIndex = programIndex(Prog);
    vector<DefOrCallInfo> Definitions;
    assert(BB.size() >= 1); // There should be at least a terminator instruction
    bool IgnorePhis = PrevBB == nullptr;
    for (auto Instr = BB.begin(), E = std::prev(BB.end(), 1); Instr != E;
         ++Instr) {
        // Ignore phi nodes if we are in a loop as they're bound in a
        // forall quantifier
        if (!IgnorePhis && llvm::isa<llvm::PHINode>(Instr)) {
            Definitions.push_back(
                DefOrCallInfo(instrAssignment(*Instr, PrevBB, Prog, Signed)));
        }
        if (!OnlyPhis && !llvm::isa<llvm::PHINode>(Instr)) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(Instr)) {
                const auto Fun = CallInst->getCalledFunction();
                if (!Fun) {
                    logErrorData("Call to undeclared function\n", *CallInst);
                    exit(1);
                }
                if (Fun->getIntrinsicID() == llvm::Intrinsic::memcpy) {
                    const vector<DefOrCallInfo> Defs =
                        memcpyIntrinsic(CallInst, Prog);
                    Definitions.insert(Definitions.end(), Defs.begin(),
                                       Defs.end());
                } else {
                    if (Heap & HEAP_MASK) {
                        Definitions.push_back(DefOrCallInfo(makeAssignment(
                            "HEAP$" + std::to_string(ProgramIndex),
                            name("HEAP$" + std::to_string(ProgramIndex)))));
                    }
                    Definitions.push_back(DefOrCallInfo(
                        toCallInfo(CallInst->getName(), Prog, *CallInst)));
                    if (Heap & HEAP_MASK) {
                        Definitions.push_back(DefOrCallInfo(makeAssignment(
                            "HEAP$" + std::to_string(ProgramIndex),
                            name("HEAP$" + std::to_string(ProgramIndex) +
                                 "_res"))));
                    }
                }
            } else {
                Definitions.push_back(DefOrCallInfo(
                    instrAssignment(*Instr, PrevBB, Prog, Signed)));
            }
        }
    }
    if (const auto RetInst =
            llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator())) {
        // TODO (moritz): use a more clever approach for void functions
        auto RetName = name("0");
        if (RetInst->getReturnValue() != nullptr) {
            RetName =
                instrNameOrVal(RetInst->getReturnValue(), RetInst->getType());
        }
        Definitions.push_back(DefOrCallInfo(
            makeAssignment("result$" + std::to_string(ProgramIndex), RetName)));
        if (Heap & HEAP_MASK) {
            Definitions.push_back(DefOrCallInfo(
                makeAssignment("HEAP$" + std::to_string(ProgramIndex) + "_res",
                               name("HEAP$" + std::to_string(ProgramIndex)))));
        }
    }
    return Definitions;
}

/// Convert a single instruction to an assignment
std::shared_ptr<std::pair<string, SMTRef>>
instrAssignment(const llvm::Instruction &Instr, const llvm::BasicBlock *PrevBB,
                Program Prog, bool Signed) {
    const int ProgramIndex = programIndex(Prog);
    if (const auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        if (BinOp->getOpcode() == Instruction::SDiv) {
            // This is a heuristic to remove divisions by 4 of pointer
            // subtractions
            // Since we treat every int as a single value, we expect the
            // division to return the number of elements and not the number
            // of
            // bytes
            if (const auto Instr =
                    llvm::dyn_cast<llvm::Instruction>(BinOp->getOperand(0))) {
                if (const auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(
                        BinOp->getOperand(1))) {
                    if (ConstInt->getSExtValue() == 4 && isPtrDiff(*Instr)) {
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
    if (const auto CmpInst = llvm::dyn_cast<llvm::CmpInst>(&Instr)) {
        auto Fun = predicateFun(*CmpInst, Signed);
        const auto Cmp =
            makeBinOp(predicateName(CmpInst->getPredicate()),
                      Fun(instrNameOrVal(CmpInst->getOperand(0),
                                         CmpInst->getOperand(0)->getType())),
                      Fun(instrNameOrVal(CmpInst->getOperand(1),
                                         CmpInst->getOperand(0)->getType())));
        return makeAssignment(CmpInst->getName(), Cmp);
    }
    if (const auto PhiInst = llvm::dyn_cast<llvm::PHINode>(&Instr)) {
        const auto Val = PhiInst->getIncomingValueForBlock(PrevBB);
        assert(Val);
        return makeAssignment(PhiInst->getName(),
                              instrNameOrVal(Val, Val->getType()));
    }
    if (const auto SelectInst = llvm::dyn_cast<llvm::SelectInst>(&Instr)) {
        const auto Cond = SelectInst->getCondition();
        const auto TrueVal = SelectInst->getTrueValue();
        const auto FalseVal = SelectInst->getFalseValue();
        const vector<SMTRef> Args = {
            instrNameOrVal(Cond, Cond->getType()),
            instrNameOrVal(TrueVal, TrueVal->getType()),
            instrNameOrVal(FalseVal, FalseVal->getType())};
        return makeAssignment(SelectInst->getName(),
                              std::make_shared<class Op>("ite", Args));
    }
    if (const auto PtrToIntInst = llvm::dyn_cast<llvm::PtrToIntInst>(&Instr)) {
        return makeAssignment(PtrToIntInst->getName(),
                              instrNameOrVal(PtrToIntInst->getPointerOperand(),
                                             PtrToIntInst->getType()));
    }
    if (const auto GetElementPtrInst =
            llvm::dyn_cast<llvm::GetElementPtrInst>(&Instr)) {
        return makeAssignment(GetElementPtrInst->getName(),
                              resolveGEP(*GetElementPtrInst));
    }
    if (const auto LoadInst = llvm::dyn_cast<llvm::LoadInst>(&Instr)) {
        SMTRef Pointer = instrNameOrVal(LoadInst->getOperand(0),
                                        LoadInst->getOperand(0)->getType());
        const auto Load = makeBinOp(
            "select", name("HEAP$" + std::to_string(ProgramIndex)), Pointer);
        return makeAssignment(LoadInst->getName(), Load);
    }
    if (const auto StoreInst = llvm::dyn_cast<llvm::StoreInst>(&Instr)) {
        string Heap = "HEAP$" + std::to_string(ProgramIndex);
        const auto Val =
            instrNameOrVal(StoreInst->getValueOperand(),
                           StoreInst->getValueOperand()->getType());
        const auto Pointer =
            instrNameOrVal(StoreInst->getPointerOperand(),
                           StoreInst->getPointerOperand()->getType());
        const std::vector<SMTRef> Args = {name(Heap), Pointer, Val};
        const auto Store = make_shared<Op>("store", Args);
        return makeAssignment("HEAP$" + std::to_string(ProgramIndex), Store);
    }
    if (const auto TruncInst = llvm::dyn_cast<llvm::TruncInst>(&Instr)) {
        const auto Val = instrNameOrVal(TruncInst->getOperand(0),
                                        TruncInst->getOperand(0)->getType());
        return makeAssignment(TruncInst->getName(), Val);
    }
    const llvm::Instruction *Ext = nullptr;
    if ((Ext = llvm::dyn_cast<llvm::ZExtInst>(&Instr)) ||
        (Ext = llvm::dyn_cast<llvm::SExtInst>(&Instr))) {
        const auto Operand = Ext->getOperand(0);
        const auto Val = instrNameOrVal(Operand, Operand->getType());
        const auto RetTy = Ext->getType();
        if (RetTy->isIntegerTy() && RetTy->getIntegerBitWidth() > 1 &&
            Operand->getType()->isIntegerTy(1)) {
            // Extensions are usually noops, but when we convert a boolean
            // (1bit
            // integer) to something bigger it needs to be an explicit
            // conversion
            std::vector<SMTRef> Args;
            Args.push_back(Val);
            Args.push_back(name("1"));
            Args.push_back(name("0"));
            return makeAssignment(Ext->getName(), make_shared<Op>("ite", Args));
        } else {
            return makeAssignment(Ext->getName(), Val);
        }
    }
    if (const auto BitCast = llvm::dyn_cast<llvm::CastInst>(&Instr)) {
        const auto Val = instrNameOrVal(BitCast->getOperand(0),
                                        BitCast->getOperand(0)->getType());
        return makeAssignment(BitCast->getName(), Val);
    }
    if (const auto AllocaInst = llvm::dyn_cast<llvm::AllocaInst>(&Instr)) {
        return makeAssignment(
            AllocaInst->getName(),
            name(llvm::cast<llvm::MDString>(
                     AllocaInst->getMetadata("reve.stack_pointer")
                         ->getOperand(0))
                     ->getString()));
    }
    logErrorData("Couldn’t convert instruction to def\n", Instr);
    return makeAssignment("UNKNOWN INSTRUCTION", name("UNKNOWN ARGS"));
}

/// Convert an LLVM predicate to an SMT predicate
string predicateName(llvm::CmpInst::Predicate Pred) {
    switch (Pred) {
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
std::function<SMTRef(SMTRef)> predicateFun(const llvm::CmpInst::CmpInst &Cmp,
                                           bool Signed) {
    if (Cmp.isUnsigned() && !Signed) {
        return [](SMTRef Signed) { return makeUnaryOp("abs", Signed); };
    }
    return [](SMTRef Signed) { return Signed; };
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
        if (const auto ConstInt =
                llvm::dyn_cast<llvm::ConstantInt>(Op.getOperand(1))) {
            // rounding conversion to guard for floating point errors
            uint64_t Divisor =
                static_cast<uint64_t>(pow(2, ConstInt->getZExtValue()) + 0.5);
            return
                [Divisor](string OpName, SMTRef FirstArg, SMTRef /*unused*/) {
                    return makeBinOp(OpName, FirstArg,
                                     name(std::to_string(Divisor)));
                };
        } else {
            logErrorData("Only shifts by a constant are supported\n", Op);
        }
    }
    return [](string OpName, SMTRef FirstArg, SMTRef SecondArg) {
        return makeBinOp(OpName, FirstArg, SecondArg);
    };
}

vector<DefOrCallInfo> memcpyIntrinsic(const llvm::CallInst *CallInst,
                                      Program Prog) {
    const int Program = programIndex(Prog);
    vector<DefOrCallInfo> Definitions;
    const auto CastInst0 =
        llvm::dyn_cast<llvm::CastInst>(CallInst->getArgOperand(0));
    const auto CastInst1 =
        llvm::dyn_cast<llvm::CastInst>(CallInst->getArgOperand(1));
    if (CastInst0 && CastInst1) {
        const auto Ty0 =
            llvm::dyn_cast<llvm::PointerType>(CastInst0->getSrcTy());
        const auto Ty1 =
            llvm::dyn_cast<llvm::PointerType>(CastInst1->getSrcTy());
        const auto StructTy0 =
            llvm::dyn_cast<llvm::StructType>(Ty0->getElementType());
        const auto StructTy1 =
            llvm::dyn_cast<llvm::StructType>(Ty1->getElementType());
        if (StructTy0 && StructTy1) {
            assert(StructTy0->isLayoutIdentical(StructTy1));
            const SMTRef BasePointerDest =
                instrNameOrVal(CallInst->getArgOperand(0),
                               CallInst->getArgOperand(0)->getType());
            const SMTRef BasePointerSrc =
                instrNameOrVal(CallInst->getArgOperand(1),
                               CallInst->getArgOperand(1)->getType());
            string HeapNameSelect = "HEAP$" + std::to_string(Program);
            if (isStackOp(*CastInst1)) {
                HeapNameSelect = "STACK$" + std::to_string(Program);
            }
            string HeapNameStore = "HEAP$" + std::to_string(Program);
            if (isStackOp(*CastInst0)) {
                HeapNameStore = "STACK$" + std::to_string(Program);
            }
            int i = 0;
            for (const auto ElTy : StructTy0->elements()) {
                const SMTRef HeapSelect = name(HeapNameSelect);
                const SMTRef HeapStore = name(HeapNameStore);
                for (int j = 0; j < typeSize(ElTy); ++j) {
                    const SMTRef Select =
                        makeBinOp("select", HeapSelect,
                                  makeBinOp("+", BasePointerSrc,
                                            name(std::to_string(i))));
                    const vector<SMTRef> Args = {
                        HeapStore, makeBinOp("+", BasePointerDest,
                                             name(std::to_string(i))),
                        Select};
                    const SMTRef Store = make_shared<Op>("store", Args);
                    Definitions.push_back(makeAssignment(HeapNameStore, Store));
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
    return Definitions;
}

std::shared_ptr<CallInfo> toCallInfo(string AssignedTo, Program Prog,
                                     const llvm::CallInst &CallInst) {
    vector<SMTRef> Args;
    if (AssignedTo.empty()) {
        AssignedTo = "res" + std::to_string(programIndex(Prog));
    }
    uint32_t i = 0;
    const auto &FunTy = *CallInst.getFunctionType();
    const llvm::Function &Fun = *CallInst.getCalledFunction();
    for (auto &Arg : CallInst.arg_operands()) {
        Args.push_back(instrNameOrVal(Arg, FunTy.getParamType(i)));
        ++i;
    }
    return make_shared<CallInfo>(AssignedTo, Fun.getName(), Args,
                                 Fun.isDeclaration(), Fun);
}

bool isPtrDiff(const llvm::Instruction &Instr) {
    if (const auto BinOp = llvm::dyn_cast<llvm::BinaryOperator>(&Instr)) {
        return BinOp->getOpcode() == Instruction::Sub &&
               llvm::isa<llvm::PtrToIntInst>(BinOp->getOperand(0)) &&
               llvm::isa<llvm::PtrToIntInst>(BinOp->getOperand(1));
    }
    return false;
}

bool isStackOp(const llvm::Instruction &Inst) {
    return Inst.getMetadata("reve.stackop");
}

shared_ptr<Assignment> makeAssignment(string Name, SMTRef Val) {
    return make_shared<Assignment>(Name, Val);
}
