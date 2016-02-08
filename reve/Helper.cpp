#include "Helper.h"

#include "Memory.h"

#include <regex>

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"

/// Get the name of the instruction or a string representation of the value if
/// it's a constant
SMTRef instrNameOrVal(const llvm::Value *val, const llvm::Type *ty) {
    if (const auto constInt = llvm::dyn_cast<llvm::ConstantInt>(val)) {
        const auto apInt = constInt->getValue();
        if (apInt.isIntN(1) && ty->isIntegerTy(1)) {
            return name(apInt.getBoolValue() ? "true" : "false");
        }
        if (apInt.isNegative()) {
            return makeUnaryOp(
                "-", name(apInt.toString(10, true).substr(1, string::npos)));
        }
        return name(apInt.toString(10, true));
    }
    if (llvm::isa<llvm::ConstantPointerNull>(val)) {
        return name("0");
    }
    if (const auto gep = llvm::dyn_cast<llvm::GEPOperator>(val)) {
        if (!llvm::isa<llvm::Instruction>(val)) {
            return resolveGEP(*gep);
        }
    }

    if (const auto constExpr = llvm::dyn_cast<llvm::ConstantExpr>(val)) {
        if (constExpr->getOpcode() == llvm::Instruction::IntToPtr) {
            return instrNameOrVal(constExpr->getOperand(0),
                                  constExpr->getOperand(0)->getType());
        }
    }
    if (llvm::isa<llvm::GlobalValue>(val)) {
        return name(val->getName());
    }
    if (val->getName().empty()) {
        logErrorData("Unnamed variable\n", *val);
        exit(1);
    }
    return name(val->getName());
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
    if (auto structTy = llvm::dyn_cast<llvm::StructType>(Ty)) {
        int size = 0;
        for (auto elTy : structTy->elements()) {
            size += typeSize(elTy);
        }
        return size;
    }
    if (auto arrayTy = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
        return static_cast<int>(arrayTy->getNumElements()) *
               typeSize(arrayTy->getElementType());
    }
    if (llvm::isa<llvm::PointerType>(Ty)) {
        return 1;
    }
    logErrorData("Couldn’t calculate size of type\n", *Ty);
    return 0;
}

/// Filter vars to only include the ones from Program
std::vector<string> filterVars(int program, std::vector<string> vars) {
    std::vector<string> filteredVars;
    const string programName = std::to_string(program);
    for (auto var : vars) {
        const auto pos = var.rfind("$");
        if (var.substr(pos + 1, programName.length()) == programName) {
            filteredVars.push_back(var);
        }
    }
    return filteredVars;
}

string argSort(string arg) {
    if (std::regex_match(arg, HEAP_REGEX) || arg == "HEAP$1_res" ||
        arg == "HEAP$2_res") {
        return "(Array Int Int)";
    }
    return "Int";
}
