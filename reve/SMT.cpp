#include "SMT.h"

#include "SExpr.h"

#include <sstream>
#include <string>
#include <vector>

using std::unique_ptr;
using llvm::make_unique;

using sexpr::Apply;
using sexpr::Value;
using sexpr::List;

// Avoid out-of-line warning by defining function here
SMTExpr::~SMTExpr() {}

unique_ptr<SExpr> SetLogic::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    unique_ptr<SExpr> LogicPtr = make_unique<const Value<std::string>>(Logic);

    Args.push_back(std::move(LogicPtr));
    return make_unique<Apply<std::string>>("set-logic", std::move(Args));
}

unique_ptr<SExpr> CheckSat::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    return make_unique<Apply<std::string>>("check-sat", std::move(Args));
}

unique_ptr<SExpr> GetModel::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    return make_unique<Apply<std::string>>("get-model", std::move(Args));
}

unique_ptr<SExpr> Assert::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("assert", std::move(Args));
}

unique_ptr<SExpr> Forall::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    std::vector<unique_ptr<SExpr>> SortedVars;
    for (auto &SortedVar : Vars) {
        SortedVars.push_back(SortedVar.toSExpr());
    }
    Args.push_back(make_unique<List<std::string>>(std::move(SortedVars)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("forall", std::move(Args));
}

unique_ptr<SExpr> SortedVar::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Type_;
    Type_.push_back(make_unique<const Value<std::string>>(Type));
    return make_unique<Apply<std::string>>(Name, std::move(Type_));
}

unique_ptr<SExpr> Let::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args;
    std::vector<unique_ptr<SExpr>> Defs_;
    for (auto &Def : Defs) {
        std::vector<unique_ptr<SExpr>> Args_;
        Args_.push_back(std::get<1>(Def)->toSExpr());
        Defs_.push_back(make_unique<Apply<std::string>>(std::get<0>(Def),
                                                        std::move(Args_)));
    }
    Args.push_back(make_unique<List<std::string>>(std::move(Defs_)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("let", std::move(Args));
}

unique_ptr<SExpr> Op::toSExpr() const {
    std::vector<unique_ptr<SExpr>> Args_;
    for (auto &Arg : Args) {
        Args_.push_back(Arg->toSExpr());
    }
    return make_unique<Apply<std::string>>(OpName, std::move(Args_));
}
