#include "SMT.h"

#include "SExpr.h"

#include <string>
#include <vector>

using std::unique_ptr;
using std::make_unique;

SMTExpr::~SMTExpr() {}

unique_ptr<const SExpr<std::string>> SetLogic::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Args;
    unique_ptr<const SExpr<std::string>> LogicPtr =
        make_unique<const Value<std::string>>(Logic);

    Args.push_back(std::move(LogicPtr));
    return make_unique<Apply<std::string>>("set-logic", std::move(Args));
}

unique_ptr<const SExpr<std::string>> CheckSat::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Args;
    return make_unique<Apply<std::string>>("check-sat", std::move(Args));
}

unique_ptr<const SExpr<std::string>> GetModel::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Args;
    return make_unique<Apply<std::string>>("get-model", std::move(Args));
}

unique_ptr<const SExpr<std::string>> Assert::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Args;
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("assert", std::move(Args));
}

unique_ptr<const SExpr<std::string>> Forall::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Args;
    std::vector<unique_ptr<const SExpr<std::string>>> SortedVars;
    for (auto &SortedVar : Vars) {
        SortedVars.push_back(SortedVar.toSExpr());
    }
    Args.push_back(make_unique<List<std::string>>(std::move(SortedVars)));
    Args.push_back(Expr->toSExpr());
    return make_unique<Apply<std::string>>("forall", std::move(Args));
}

unique_ptr<const SExpr<std::string>> SortedVar::toSExpr() const {
    std::vector<unique_ptr<const SExpr<std::string>>> Type_;
    Type_.push_back(make_unique<const Value<std::string>>(Type));
    return make_unique<Apply<std::string>>(Name, std::move(Type_));
}
