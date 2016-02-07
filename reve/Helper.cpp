#include "Helper.h"

#include "Memory.h"

#include <regex>

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef instrNameOrVal(const llvm::Value *Val, const llvm::Type *Ty) {
    if (const auto ConstInt = llvm::dyn_cast<llvm::ConstantInt>(Val)) {
        const auto ApInt = ConstInt->getValue();
        if (ApInt.isIntN(1) && Ty->isIntegerTy(1)) {
            return name(ApInt.getBoolValue() ? "true" : "false");
        }
        if (ApInt.isNegative()) {
            return makeUnaryOp(
                "-", name(ApInt.toString(10, true).substr(1, string::npos)));
        }
        return name(ApInt.toString(10, true));
    }
    if (llvm::isa<llvm::ConstantPointerNull>(Val)) {
        return name("0");
    }
    if (const auto GEP = llvm::dyn_cast<llvm::GEPOperator>(Val)) {
        if (!llvm::isa<llvm::Instruction>(Val)) {
            return resolveGEP(*GEP);
        }
    }

    if (const auto ConstExpr = llvm::dyn_cast<llvm::ConstantExpr>(Val)) {
        if (ConstExpr->getOpcode() == llvm::Instruction::IntToPtr) {
            return instrNameOrVal(ConstExpr->getOperand(0),
                                  ConstExpr->getOperand(0)->getType());
        }
    }
    if (llvm::isa<llvm::GlobalValue>(Val)) {
        return name(Val->getName());
    }
    if (Val->getName().empty()) {
        logErrorData("Unnamed variable\n", *Val);
        exit(1);
    }
    return name(Val->getName());
}

int typeSize(llvm::Type *Ty) {
    if (auto IntTy = llvm::dyn_cast<llvm::IntegerType>(Ty)) {
        if (IntTy->getBitWidth() <= 64) {
            return 1;
        }
        logError("Unsupported integer bitwidth: " +
                 std::to_string(IntTy->getBitWidth()) + "\n");
    }
    if (Ty->isDoubleTy()) {
        return 1;
    }
    if (auto StructTy = llvm::dyn_cast<llvm::StructType>(Ty)) {
        int Size = 0;
        for (auto ElTy : StructTy->elements()) {
            Size += typeSize(ElTy);
        }
        return Size;
    }
    if (auto ArrayTy = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
        return static_cast<int>(ArrayTy->getNumElements()) *
               typeSize(ArrayTy->getElementType());
    }
    if (llvm::isa<llvm::PointerType>(Ty)) {
        return 1;
    }
    logErrorData("Couldn’t calculate size of type\n", *Ty);
    return 0;
}

/// Filter vars to only include the ones from Program
std::vector<string> filterVars(int Program, std::vector<string> Vars) {
    std::vector<string> FilteredVars;
    const string ProgramName = std::to_string(Program);
    for (auto Var : Vars) {
        const auto Pos = Var.rfind("$");
        if (Var.substr(Pos + 1, ProgramName.length()) == ProgramName) {
            FilteredVars.push_back(Var);
        }
    }
    return FilteredVars;
}

string argSort(string Arg) {
    if (std::regex_match(Arg, HEAP_REGEX) || Arg == "HEAP$1_res" ||
        Arg == "HEAP$2_res") {
        return "(Array Int Int)";
    }
    return "Int";
}
