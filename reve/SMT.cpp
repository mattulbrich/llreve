#include "SMT.h"

#include "SExpr.h"

#include <string>
#include <vector>

SMTExpr::~SMTExpr() {}

std::unique_ptr<SExpr<std::string>> SetLogic::toSExpr() {
    std::vector<std::shared_ptr<SExpr<std::string>>> Args;
    auto LogicPtr = std::make_shared<Value<std::string>>(Logic);

    Args.push_back(LogicPtr);
    return std::make_unique<Apply<std::string>>("set-logic", Args);
}
