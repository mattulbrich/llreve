#pragma once

#include "SExpr.h"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/STLExtras.h"

#include <map>
#include <set>
#include <sstream>
#include <string>

namespace smt {

using SExpr = const sexpr::SExpr<std::string>;
using SExprRef = std::unique_ptr<SExpr>;

struct HeapInfo {
    std::string arrayName;
    std::string index;
    std::string suffix;
    HeapInfo(std::string arrayName, std::string index, std::string suffix)
        : arrayName(arrayName), index(index), suffix(suffix) {}
};

class SMTExpr : public std::enable_shared_from_this<SMTExpr> {
  public:
    virtual SExprRef toSExpr() const = 0;
    virtual std::set<std::string> uses() const;
    virtual std::shared_ptr<const SMTExpr> compressLets(
        std::vector<std::pair<std::string, std::shared_ptr<const SMTExpr>>>
            defs = std::vector<
                std::pair<std::string, std::shared_ptr<const SMTExpr>>>())
        const;
    virtual std::shared_ptr<const SMTExpr> mergeImplications(
        std::vector<std::shared_ptr<const SMTExpr>> conditions) const;
    virtual std::shared_ptr<const SMTExpr> instantiateArrays() const;
    virtual std::unique_ptr<const HeapInfo> heapInfo() const;
    virtual ~SMTExpr() = default;
    SMTExpr(const SMTExpr & /*unused*/) = default;
    SMTExpr &operator=(SMTExpr &) = delete;
    SMTExpr() = default;
    // Necessary to prevent horn2vmt from fucking up
    virtual std::shared_ptr<const SMTExpr>
    renameDefineFuns(std::string suffix) const;
};

using SharedSMTRef = std::shared_ptr<const SMTExpr>;
using SMTRef = std::unique_ptr<const SMTExpr>;
using Assignment = std::pair<std::string, SharedSMTRef>;
auto makeAssignment(std::string name, SharedSMTRef val)
    -> std::unique_ptr<const Assignment>;

class SetLogic : public SMTExpr {
  public:
    explicit SetLogic(std::string logic) : logic(std::move(logic)) {}
    SExprRef toSExpr() const override;
    std::string logic;
};

class Assert : public SMTExpr {
  public:
    explicit Assert(SharedSMTRef expr) : expr(std::move(expr)) {}
    SharedSMTRef expr;
    SExprRef toSExpr() const override;
    std::set<std::string> uses() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    SharedSMTRef instantiateArrays() const override;
};

class SortedVar : public SMTExpr {
  public:
    SortedVar(std::string name, std::string type)
        : name(std::move(name)), type(std::move(type)) {}
    std::string name;
    std::string type;
    SExprRef toSExpr() const override;
    std::set<std::string> uses() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
    SortedVar &operator=(const SortedVar other) {
        name = other.name;
        type = other.type;
        return *this;
    }
    SortedVar(const SortedVar &other) : name(other.name), type(other.type) {}
};

using FreeVarsMap = std::map<int, std::vector<smt::SortedVar>>;

inline bool operator<(const SortedVar &lhs, const SortedVar &rhs) {
    return lhs.name < rhs.name;
}

inline bool operator>(const SortedVar &lhs, const SortedVar &rhs) {
    return rhs < lhs;
}

inline bool operator<=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs > rhs);
}

inline bool operator>=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs < rhs);
}

inline bool operator==(const SortedVar &lhs, const SortedVar &rhs) {
    return lhs.name == rhs.name;
}

inline bool operator!=(const SortedVar &lhs, const SortedVar &rhs) {
    return !(lhs == rhs);
}

class Forall : public SMTExpr {
  public:
    Forall(std::vector<SortedVar> vars, SharedSMTRef expr)
        : vars(std::move(vars)), expr(std::move(expr)) {}
    SExprRef toSExpr() const override;
    std::vector<SortedVar> vars;
    SharedSMTRef expr;
    std::set<std::string> uses() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    SharedSMTRef renameDefineFuns(std::string suffix) const override;
};

class CheckSat : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
};

class GetModel : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
};

class Let : public SMTExpr {
  public:
    SExprRef toSExpr() const override;
    std::vector<Assignment> defs;
    SharedSMTRef expr;
    Let(std::vector<Assignment> defs, SharedSMTRef expr)
        : defs(std::move(defs)), expr(std::move(expr)) {}
    std::set<std::string> uses() const override;
    SharedSMTRef
    compressLets(std::vector<Assignment> passedDefs) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    SharedSMTRef instantiateArrays() const override;
};

template <typename T> class Primitive : public SMTExpr {
  public:
    explicit Primitive(const T val) : val(val) {}
    SExprRef toSExpr() const override {
        std::stringstream sStream;
        sStream << val;
        return std::make_unique<sexpr::Value<std::string>>(sStream.str());
    }
    const T val;
    std::set<std::string> uses() const override {
        return std::set<std::string>();
    }
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
    std::unique_ptr<const HeapInfo> heapInfo() const override {
        return nullptr;
    }
    SharedSMTRef renameDefineFuns(std::string suffix) const override;
};

template <>
SharedSMTRef Primitive<std::string>::renameDefineFuns(std::string suffix) const;

class Op : public SMTExpr {
  public:
    Op(std::string opName, std::vector<SharedSMTRef> args)
        : opName(std::move(opName)), args(std::move(args)), instantiate(true) {}
    Op(std::string opName, std::vector<SharedSMTRef> args, bool instantiate)
        : opName(std::move(opName)), args(std::move(args)),
          instantiate(instantiate) {}
    std::string opName;
    std::vector<SharedSMTRef> args;
    bool instantiate;
    SExprRef toSExpr() const override;
    std::set<std::string> uses() const override;
    SharedSMTRef compressLets(std::vector<Assignment> defs) const override;
    SharedSMTRef
    mergeImplications(std::vector<SharedSMTRef> conditions) const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef renameDefineFuns(std::string suffix) const override;
};

class Query : public SMTExpr {
  public:
    Query(std::string queryName) : queryName(std::move(queryName)) {}
    std::string queryName;
    SExprRef toSExpr() const override;
};

auto makeBinOp(std::string opName, std::string arg1, std::string arg2)
    -> std::unique_ptr<Op>;
auto makeBinOp(std::string opName, SharedSMTRef arg1, SharedSMTRef arg2)
    -> std::unique_ptr<Op>;
auto makeUnaryOp(std::string opName, std::string arg) -> std::unique_ptr<Op>;
auto makeUnaryOp(std::string opName, SharedSMTRef arg) -> std::unique_ptr<Op>;
auto stringExpr(std::string name)
    -> std::unique_ptr<const Primitive<std::string>>;
auto makeOp(std::string opName, std::vector<std::string> args)
    -> std::unique_ptr<const Op>;

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
    SharedSMTRef instantiateArrays() const override;
};

class FunDef : public SMTExpr {
  public:
    FunDef(std::string funName, std::vector<SortedVar> args,
           std::string outType, SharedSMTRef body)
        : funName(std::move(funName)), args(std::move(args)),
          outType(std::move(outType)), body(std::move(body)) {}
    std::string funName;
    std::vector<SortedVar> args;
    std::string outType;
    SharedSMTRef body;
    SExprRef toSExpr() const override;
    SharedSMTRef instantiateArrays() const override;
    SharedSMTRef renameDefineFuns(std::string suffix) const override;
};

class Comment : public SMTExpr {
  public:
    Comment(std::string val) : val(std::move(val)) {}
    std::string val;
    SExprRef toSExpr() const override;
};

class VarDecl : public SMTExpr {
  public:
    VarDecl(std::string varName, std::string type)
        : varName(std::move(varName)), type(std::move(type)) {}
    std::string varName;
    std::string type;
    SExprRef toSExpr() const override;
};

auto nestLets(SharedSMTRef clause, std::vector<Assignment> defs)
    -> SharedSMTRef;
}

auto isArray(std::string) -> bool;

auto apIntToSMT(llvm::APInt i) -> smt::SharedSMTRef;
auto intToSMT(std::string i, unsigned bitWidth) -> smt::SharedSMTRef;

auto getSMTType(std::string var) -> std::string;
