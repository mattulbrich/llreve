#ifndef SMT_H
#define SMT_H

#include "SExpr.h"

#include <string>

using SExpr = const sexpr::SExpr<std::string>;

class SMTExpr {
  public:
    virtual std::unique_ptr<SExpr> toSExpr() const = 0;
    virtual ~SMTExpr();
    SMTExpr(const SMTExpr &Expr) = default;
    SMTExpr() = default;
};

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string Logic_) : Logic(Logic_) {}
    std::unique_ptr<SExpr> toSExpr() const override;
    std::string Logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(std::unique_ptr<const SMTExpr> Expr_)
        : Expr(std::move(Expr_)) {}
    std::unique_ptr<const SMTExpr> Expr;
    std::unique_ptr<SExpr> toSExpr() const override;
};

class SortedVar : public SMTExpr {
  public:
    SortedVar(std::string Name_, std::string Type_)
        : Name(Name_), Type(Type_) {}
    const std::string Name;
    const std::string Type;
    std::unique_ptr<SExpr> toSExpr() const override;
};

class Forall : public SMTExpr {
  public:
    Forall(std::vector<SortedVar> Vars_, std::unique_ptr<const SMTExpr> Expr_)
        : Vars(Vars_), Expr(std::move(Expr_)) {}
    std::unique_ptr<SExpr> toSExpr() const override;
    std::vector<SortedVar> Vars;
    std::unique_ptr<const SMTExpr> Expr;
};

class CheckSat : public SMTExpr {
  public:
    std::unique_ptr<SExpr> toSExpr() const override;
};

class GetModel : public SMTExpr {
  public:
    std::unique_ptr<SExpr> toSExpr() const override;
};

class Let : public SMTExpr {
  public:
    std::unique_ptr<SExpr> toSExpr() const override;
    std::vector<std::tuple<std::string, std::unique_ptr<const SMTExpr>>> Defs;
    std::unique_ptr<const SMTExpr> Expr;
    Let(std::vector<std::tuple<std::string, std::unique_ptr<const SMTExpr>>>
            Defs_,
        std::unique_ptr<const SMTExpr> Expr_)
        : Defs(std::move(Defs_)), Expr(std::move(Expr_)) {}
};

template <typename T> class Primitive : public SMTExpr {
  public:
    explicit Primitive(const T Val_) : Val(Val_) {}
    std::unique_ptr<SExpr> toSExpr() const override {
        return std::make_unique<sexpr::Value<std::string>>(Val);
    }
    const T Val;
};

class Op : public SMTExpr {
  public:
    Op(std::string OpName_, std::vector<std::unique_ptr<const SMTExpr>> Args_)
        : OpName(OpName_), Args(std::move(Args_)) {}
    std::string OpName;
    std::vector<std::unique_ptr<const SMTExpr>> Args;
    std::unique_ptr<const SExpr> toSExpr() const override;
};

#endif // SMT_H
