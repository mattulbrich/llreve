#pragma once

#include <gmpxx.h>
#include <map>
#include <memory>
#include <set>
#include <vector>

struct ArrayVal {
    mpz_class background;
    std::map<mpz_class, mpz_class> vals;
};

struct ModelValues {
    std::map<std::string, ArrayVal> arrays;
    std::map<std::string, mpz_class> values;
};

struct SMTExpr {
    virtual std::set<std::string> references() const = 0;
    virtual mpz_class getVal() const;
    virtual ArrayVal getArrayVal() const;
    virtual mpz_class getIndex() const;
    virtual ~SMTExpr();
};

struct AsArray : public SMTExpr {
    std::string arg;
    AsArray(std::string arg) : arg(arg) {}
    std::set<std::string> references() const override;
};

struct String : public SMTExpr {
    std::string val;
    String(std::string val) : val(val) {}
    std::set<std::string> references() const override;
};

struct Int : public SMTExpr {
    mpz_class val;
    Int(mpz_class val) : val(val) {}
    std::set<std::string> references() const override;
    mpz_class getVal() const override;
    ArrayVal getArrayVal() const override;
};

struct Eq : public SMTExpr {
    std::shared_ptr<SMTExpr> left;
    std::shared_ptr<SMTExpr> right;
    Eq(std::shared_ptr<SMTExpr> left, std::shared_ptr<SMTExpr> right)
        : left(left), right(right) {}
    std::set<std::string> references() const override;
    mpz_class getIndex() const override;
};

struct ITE : public SMTExpr {
    std::shared_ptr<SMTExpr> cond;
    std::shared_ptr<SMTExpr> ifTrue;
    std::shared_ptr<SMTExpr> ifFalse;
    ITE(std::shared_ptr<SMTExpr> cond, std::shared_ptr<SMTExpr> ifTrue,
        std::shared_ptr<SMTExpr> ifFalse)
        : cond(cond), ifTrue(ifTrue), ifFalse(ifFalse) {}
    std::set<std::string> references() const override;
    ArrayVal getArrayVal() const override;
};

struct Identifier : public SMTExpr {
    std::string name;
    Identifier(std::string name) : name(name) {}
    std::set<std::string> references() const override;
};

enum class Type { Int, IntArray, IntFun };

struct TopLevelExpr {
    virtual ~TopLevelExpr();
    virtual std::set<std::string> references() const = 0;
    virtual Type type() const = 0;
    virtual std::string getName() const = 0;
    virtual mpz_class getVal() const = 0;
    virtual ArrayVal getArrayVal() const = 0;
};

using TypedArg = std::pair<std::string, Type>;

struct DefineFun : public TopLevelExpr {
    std::string name;
    std::vector<TypedArg> argTypes;
    Type returnType;
    std::shared_ptr<SMTExpr> definition;
    std::set<std::string> references() const override;
    Type type() const override;
    std::string getName() const override;
    mpz_class getVal() const override;
    ArrayVal getArrayVal() const override;
    DefineFun(std::string name, std::vector<TypedArg> argTypes, Type returnType,
              std::shared_ptr<SMTExpr> definition)
        : name(name), argTypes(argTypes), returnType(returnType),
          definition(definition) {}
};

struct Model {
    std::vector<std::shared_ptr<TopLevelExpr>> exprs;
    Model(std::vector<std::shared_ptr<TopLevelExpr>> exprs) : exprs(exprs) {}
};

ModelValues parseValues(Model model);

struct Result {
    virtual bool isSat() const = 0;
    virtual ~Result();
};

struct Unsat : public Result {
    Unsat() {}
    bool isSat() const override;
};

struct Sat : public Result {
    Model model;
    Sat(Model model) : model(model) {}
    bool isSat() const override;
};

std::shared_ptr<Result> parseResult(FILE *stream);
