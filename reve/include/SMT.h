#ifndef SMT_H
#define SMT_H

#include "SExpr.h"

#include "llvm/ADT/STLExtras.h"

#include <sstream>
#include <string>
#include <set>

using std::set;
using std::string;
using std::shared_ptr;
using std::unique_ptr;

using SExpr = const sexpr::SExpr<std::string>;
using SExprRef = unique_ptr<SExpr>;

class SMTExpr {
  public:
    virtual SExprRef toSExpr() const = 0;
    virtual set<string> uses() const = 0;
    virtual ~SMTExpr();
    SMTExpr(const SMTExpr &Expr) = default;
    SMTExpr() = default;
};

using SMTRef = shared_ptr<const SMTExpr>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string Logic_) : Logic(Logic_) {}
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    std::string Logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(SMTRef Expr_) : Expr(Expr_) {}
    SMTRef Expr;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

class SortedVar : public SMTExpr {
  public:
    SortedVar(std::string Name_, std::string Type_)
        : Name(Name_), Type(Type_) {}
    const std::string Name;
    const std::string Type;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

class Forall : public SMTExpr {
  public:
    Forall(std::vector<SortedVar> Vars_, SMTRef Expr_)
        : Vars(Vars_), Expr(Expr_) {}
    SExprRef toSExpr() const override;
    std::vector<SortedVar> Vars;
    SMTRef Expr;
    set<string> uses() const override;
};

class CheckSat : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

class GetModel : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

class Let : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    std::vector<std::tuple<std::string, SMTRef>> Defs;
    SMTRef Expr;
    Let(std::vector<std::tuple<std::string, SMTRef>> Defs_, SMTRef Expr_)
        : Defs(Defs_), Expr(Expr_) {}
    set<string> uses() const override;
};

template <typename T> class Primitive : public SMTExpr {
  public:
    explicit Primitive(const T Val_) : Val(Val_) {}
    SExprRef toSExpr() const override {
        std::stringstream SStream;
        SStream << Val;
        return llvm::make_unique<sexpr::Value<std::string>>(SStream.str());
    }
    const T Val;
    set<string> uses() const override {
        return set<string>();
    }
};

class Op : public SMTExpr {
  public:
    Op(std::string OpName_, std::vector<SMTRef> Args_)
        : OpName(OpName_), Args(Args_) {}
    std::string OpName;
    std::vector<SMTRef> Args;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

auto makeBinOp(std::string OpName, std::string Arg_1, std::string Arg_2)
    -> std::shared_ptr<Op>;
auto makeBinOp(std::string OpName, SMTRef Arg_1, SMTRef Arg_2)
    -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string OpName, std::string Arg) -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string OpName, SMTRef Arg) -> std::shared_ptr<Op>;
auto name(std::string Name) -> SMTRef;
auto makeOp(std::string OpName, std::vector<std::string> Args) -> SMTRef;

class Fun : public SMTExpr {
  public:
    Fun(std::string FunName_, std::vector<std::string> InTypes_,
        std::string OutType_)
        : FunName(FunName_), InTypes(InTypes_), OutType(OutType_) {}
    std::string FunName;
    std::vector<std::string> InTypes;
    std::string OutType;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
};

#endif // SMT_H
