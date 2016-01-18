#pragma once

#include "SExpr.h"

#include "llvm/ADT/STLExtras.h"

#include <set>
#include <sstream>
#include <string>

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
    virtual shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs =
            std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>>())
        const = 0;
    virtual ~SMTExpr();
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr() = default;
};

using SMTRef = shared_ptr<const SMTExpr>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string Logic) : Logic(std::move(Logic)) {}
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
    std::string Logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(SMTRef Expr) : Expr(std::move(Expr)) {}
    SMTRef Expr;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class SortedVar : public SMTExpr {
  public:
    SortedVar(std::string Name, std::string Type)
        : Name(std::move(Name)), Type(std::move(Type)) {}
    const std::string Name;
    const std::string Type;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class Forall : public SMTExpr {
  public:
    Forall(std::vector<SortedVar> Vars, SMTRef Expr)
        : Vars(std::move(Vars)), Expr(std::move(Expr)) {}
    SExprRef toSExpr() const override;
    std::vector<SortedVar> Vars;
    SMTRef Expr;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class CheckSat : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class GetModel : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class Let : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    std::vector<std::tuple<std::string, SMTRef>> Defs;
    SMTRef Expr;
    Let(std::vector<std::tuple<std::string, SMTRef>> Defs, SMTRef Expr)
        : Defs(std::move(Defs)), Expr(std::move(Expr)) {}
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>>
                     PassedDefs) const override;
};

template <typename T> class Primitive : public SMTExpr {
  public:
    explicit Primitive(const T Val) : Val(Val) {}
    SExprRef toSExpr() const override {
        std::stringstream SStream;
        SStream << Val;
        return llvm::make_unique<sexpr::Value<std::string>>(SStream.str());
    }
    const T Val;
    set<string> uses() const override { return set<string>(); }
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class Op : public SMTExpr {
  public:
    Op(std::string OpName, std::vector<SMTRef> Args)
        : OpName(std::move(OpName)), Args(std::move(Args)) {}
    std::string OpName;
    std::vector<SMTRef> Args;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

auto makeBinOp(std::string OpName, std::string Arg1, std::string Arg2)
    -> std::shared_ptr<Op>;
auto makeBinOp(std::string OpName, SMTRef Arg1, SMTRef Arg2)
    -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string OpName, std::string Arg) -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string OpName, SMTRef Arg) -> std::shared_ptr<Op>;
auto name(std::string Name) -> SMTRef;
auto makeOp(std::string OpName, std::vector<std::string> Args) -> SMTRef;

class FunDecl : public SMTExpr {
  public:
    FunDecl(std::string FunName, std::vector<std::string> InTypes,
        std::string OutType)
        : FunName(std::move(FunName)), InTypes(std::move(InTypes)),
          OutType(std::move(OutType)) {}
    std::string FunName;
    std::vector<std::string> InTypes;
    std::string OutType;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

class FunDef : public SMTExpr {
  public:
    FunDef(std::string FunName, std::vector<SortedVar> Args,
           std::string OutType, SMTRef Body)
        : FunName(std::move(FunName)), Args(std::move(Args)),
          OutType(std::move(OutType)), Body(std::move(Body)) {}
    std::string FunName;
    std::vector<SortedVar> Args;
    std::string OutType;
    SMTRef Body;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};


class Comment : public SMTExpr {
  public:
    Comment(std::string Val) : Val(std::move(Val)) {}
    std::string Val;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr> compressLets(
        std::vector<std::tuple<std::string, shared_ptr<const SMTExpr>>> Defs)
        const override;
};

auto nestLets(SMTRef Clause, std::vector<std::tuple<std::string, SMTRef>> Defs)
    -> SMTRef;
