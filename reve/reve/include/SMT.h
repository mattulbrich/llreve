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
        std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>> defs =
            std::vector<std::pair<std::string, shared_ptr<const SMTExpr>>>())
        const = 0;
    virtual ~SMTExpr();
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr &operator=(SMTExpr &) = delete;
    SMTExpr() = default;
};

using SMTRef = shared_ptr<const SMTExpr>;
using Assignment = std::pair<std::string, SMTRef>;
auto makeAssignment(string name, SMTRef val) -> std::shared_ptr<Assignment>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string logic) : logic(std::move(logic)) {}
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
    std::string logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(SMTRef expr) : expr(std::move(expr)) {}
    SMTRef expr;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class SortedVar : public SMTExpr {
  public:
    SortedVar(std::string name, std::string type)
        : name(std::move(name)), type(std::move(type)) {}
    std::string name;
    std::string type;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
    SortedVar &operator=(const SortedVar other) {
        name = other.name;
        type = other.type;
        return *this;
    }
    SortedVar(const SortedVar &other) : name(other.name), type(other.type) {}
};

class Forall : public SMTExpr {
  public:
    Forall(std::vector<SortedVar> vars, SMTRef expr)
        : vars(std::move(vars)), expr(std::move(expr)) {}
    SExprRef toSExpr() const override;
    std::vector<SortedVar> vars;
    SMTRef expr;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class CheckSat : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class GetModel : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class Let : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    std::vector<Assignment> defs;
    SMTRef expr;
    Let(std::vector<Assignment> defs, SMTRef expr)
        : defs(std::move(defs)), expr(std::move(expr)) {}
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> passedDefs) const override;
};

template <typename T> class Primitive : public SMTExpr {
  public:
    explicit Primitive(const T val) : val(val) {}
    SExprRef toSExpr() const override {
        std::stringstream sStream;
        sStream << val;
        return llvm::make_unique<sexpr::Value<std::string>>(sStream.str());
    }
    const T val;
    set<string> uses() const override { return set<string>(); }
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class Op : public SMTExpr {
  public:
    Op(std::string opName, std::vector<SMTRef> args)
        : opName(std::move(opName)), args(std::move(args)) {}
    std::string opName;
    std::vector<SMTRef> args;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

auto makeBinOp(std::string opName, std::string arg1, std::string arg2)
    -> std::shared_ptr<Op>;
auto makeBinOp(std::string opName, SMTRef arg1, SMTRef arg2)
    -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string opName, std::string arg) -> std::shared_ptr<Op>;
auto makeUnaryOp(std::string opName, SMTRef arg) -> std::shared_ptr<Op>;
auto name(std::string name) -> SMTRef;
auto makeOp(std::string opName, std::vector<std::string> args) -> SMTRef;

class FunDecl : public SMTExpr {
  public:
    FunDecl(std::string funName, std::vector<std::string> inTypes,
            std::string outType)
        : funName(std::move(funName)), inTypes(std::move(inTypes)),
          outType(std::move(outType)) {}
    std::string funName;
    std::vector<std::string> inTypes;
    std::string outType;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class FunDef : public SMTExpr {
  public:
    FunDef(std::string funName, std::vector<SortedVar> args,
           std::string outType, SMTRef body)
        : funName(std::move(funName)), args(std::move(args)),
          outType(std::move(outType)), body(std::move(body)) {}
    std::string funName;
    std::vector<SortedVar> args;
    std::string outType;
    SMTRef body;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

class Comment : public SMTExpr {
  public:
    Comment(std::string val) : val(std::move(val)) {}
    std::string val;
    SExprRef toSExpr() const override;
    set<string> uses() const override;
    shared_ptr<const SMTExpr>
    compressLets(std::vector<Assignment> defs) const override;
};

auto nestLets(SMTRef clause, std::vector<Assignment> defs) -> SMTRef;
