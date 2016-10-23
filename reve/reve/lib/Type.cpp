#include "Type.h"

#include "Helper.h"
#include "Memory.h"
#include "Opts.h"

using std::make_unique;
using std::string;
using std::unique_ptr;
using std::vector;

using sexpr::Apply;
using sexpr::Value;

TypeTag BoolType::getTag() const { return TypeTag::Bool; }
TypeTag IntType::getTag() const { return TypeTag::Int; }
TypeTag FloatType::getTag() const { return TypeTag::Float; }
TypeTag ArrayType::getTag() const { return TypeTag::Array; }

SExprRef BoolType::toSExpr() const { return sexprFromString("Bool"); }
SExprRef IntType::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        vector<SExprRef> args;
        args.push_back(sexprFromString("BitVec"));
        args.push_back(sexprFromString(std::to_string(this->bitWidth)));
        return make_unique<Apply<string>>("_", std::move(args));
    } else {
        return sexprFromString("Int");
    }
}
SExprRef FloatType::toSExpr() const {
    if (SMTGenerationOpts::getInstance().BitVect) {
        vector<SExprRef> args;
        args.push_back(sexprFromString("FloatingPoint"));
        args.push_back(sexprFromString(std::to_string(this->exponentWidth)));
        args.push_back(sexprFromString(std::to_string(this->significandWidth)));
        return make_unique<Apply<string>>("_", std::move(args));
    } else {
        return sexprFromString("Real");
    }
}
SExprRef ArrayType::toSExpr() const {
    vector<SExprRef> args;
    args.push_back(domain->toSExpr());
    args.push_back(target->toSExpr());
    return make_unique<Apply<string>>("Array", std::move(args));
}

unique_ptr<Type> BoolType::copy() const { return make_unique<BoolType>(); }
unique_ptr<Type> IntType::copy() const {
    return make_unique<IntType>(this->bitWidth);
}
unique_ptr<Type> FloatType::copy() const {
    return make_unique<FloatType>(this->exponentWidth, this->significandWidth);
}
unique_ptr<Type> ArrayType::copy() const {
    return make_unique<ArrayType>(domain->copy(), target->copy());
}

unique_ptr<ArrayType> int64ArrayType() {
    return make_unique<ArrayType>(int64Type(), int64Type());
}

unique_ptr<IntType> int64Type() { return make_unique<IntType>(64); }

unique_ptr<BoolType> boolType() { return make_unique<BoolType>(); }

unique_ptr<IntType> pointerType() { return make_unique<IntType>(64); }

static unsigned semanticsExponent(const llvm::fltSemantics &semantics) {
    return llvm::APFloat::semanticsSizeInBits(semantics) -
           llvm::APFloat::semanticsPrecision(semantics);
}

unique_ptr<Type> llvmType(const llvm::Type *type) {
    if (type->isPointerTy()) {
        return pointerType();
    } else if (type->isIntegerTy()) {
        return make_unique<IntType>(type->getIntegerBitWidth());
    } else if (type->isFloatingPointTy()) {
        return make_unique<FloatType>(
            semanticsExponent(type->getFltSemantics()),
            llvm::APFloat::semanticsPrecision(type->getFltSemantics()));
    } else if (type->isVoidTy()) {
        // Void is always a constant zero
        return int64Type();
    } else {
        logErrorData("Unsupported type\n", *type);
        exit(1);
    }
}

unique_ptr<Type> inferTypeByName(string arg) {
    if (std::regex_match(arg, HEAP_REGEX) || arg == "HEAP$1_res" ||
        arg == "HEAP$2_res") {
        return int64ArrayType();
    }
    return int64Type();
}
