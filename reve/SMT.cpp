#include "SMT.h"

#include "SExpr.h"

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
