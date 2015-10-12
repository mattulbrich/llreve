#ifndef SMT_H
#define SMT_H

#include "SExpr.h"

#include <string>

class SMTExpr {
  public:
    virtual std::unique_ptr<SExpr<std::string>> toSExpr() = 0;
    virtual ~SMTExpr();
};

class SetLogic : public SMTExpr {
  public:
    SetLogic(std::string Logic_) : Logic(Logic_) {}
    std::unique_ptr<SExpr<std::string>> toSExpr();
    std::string Logic;
};

class Assert : public SMTExpr {};

class Forall : public SMTExpr {};

#endif // SMT_H
