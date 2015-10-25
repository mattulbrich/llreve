#include "SMT.h"

#include "SExpr.h"

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

using llvm::make_unique;

using sexpr::Apply;
using sexpr::Value;
using sexpr::List;

// Avoid out-of-line warning by defining function here
SMTExpr::~SMTExpr() {}

SExprRef SetLogic::toSExpr() const {
    std::vector<SExprRef> Args;
    SExprRef LogicPtr = make_unique<const Value<std::string>>(Logic);

    Args.push_back(std::move(LogicPtr));
    return make_unique<Apply<std::string>>("set-logic", std::move(Args));
}

SExprRef CheckSat::toSExpr() const {
    std::vector<SExprRef> Args;
    return make_unique<Apply<std::string>>("check-sat", std::move(Args));
}

SExprRef GetModel::toSExpr() const {
    std::vector<SExprRef> Args;
    return make_unique<Apply<std::string>>("get-model", std::move(Args));
}

SExprRef Assert::toSExpr() const {
    std::vector<SExprRef> Args;
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("assert", std::move(Args));
}

SExprRef Forall::toSExpr() const {
    std::vector<SExprRef> Args;
    std::vector<SExprRef> SortedVars;
    for (auto &SortedVar : Vars) {
        SortedVars.push_back(SortedVar.toSExpr());
    }
    Args.push_back(make_unique<List<std::string>>(std::move(SortedVars)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("forall", std::move(Args));
}

SExprRef SortedVar::toSExpr() const {
    std::vector<SExprRef> Type_;
    Type_.push_back(make_unique<const Value<std::string>>(Type));
    return make_unique<Apply<std::string>>(Name, std::move(Type_));
}

SExprRef Let::toSExpr() const {
    std::vector<SExprRef> Args;
    std::vector<SExprRef> Defs_;
    for (auto &Def : Defs) {
        std::vector<SExprRef> Args_;
        Args_.push_back(std::get<1>(Def)->toSExpr());
        Defs_.push_back(make_unique<Apply<std::string>>(std::get<0>(Def),
                                                        std::move(Args_)));
    }
    Args.push_back(make_unique<List<std::string>>(std::move(Defs_)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("let", std::move(Args));
}

SExprRef Op::toSExpr() const {
    std::vector<SExprRef> Args_;
    for (auto &Arg : Args) {
        Args_.push_back(Arg->toSExpr());
    }
    return make_unique<Apply<std::string>>(OpName, std::move(Args_));
}

std::shared_ptr<Op> makeBinOp(std::string OpName, std::string Arg_1, std::string Arg_2) {
    std::vector<SMTRef> Args;
    Args.push_back(name(Arg_1));
    Args.push_back(name(Arg_2));
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeBinOp(std::string OpName, SMTRef Arg_1, SMTRef Arg_2) {
    std::vector<SMTRef> Args;
    Args.push_back(Arg_1);
    Args.push_back(Arg_2);
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeUnaryOp(std::string OpName, std::string Arg) {
    std::vector<SMTRef> Args;
    Args.push_back(name(Arg));
    return make_unique<Op>(OpName, Args);
}

std::shared_ptr<Op> makeUnaryOp(std::string OpName, SMTRef Arg) {
    std::vector<SMTRef> Args;
    Args.push_back(Arg);
    return make_unique<Op>(OpName, Args);
}

SMTRef name(std::string Name) {
    return make_unique<Primitive<std::string>>(Name);
}

SMTRef makeOp(std::string OpName, std::vector<std::string> Args) {
    std::vector<SMTRef> Args_;
    for (auto Arg : Args) {
        Args_.push_back(name(Arg));
    }
    return make_unique<Op>(OpName, Args_);
}

SExprRef Fun::toSExpr() const {
    std::vector<SExprRef> InTypes_;
    for (auto InType : InTypes) {
        InTypes_.push_back(name(InType)->toSExpr());
    }
    std::vector<SExprRef> Args;
    Args.push_back(name(FunName)->toSExpr());
    Args.push_back(make_unique<List<std::string>>(std::move(InTypes_)));
    Args.push_back(name(OutType)->toSExpr());
    return make_unique<Apply<std::string>>("declare-fun", std::move(Args));
}
