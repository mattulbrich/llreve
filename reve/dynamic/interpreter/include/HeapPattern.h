#pragma once

#include "Compat.h"
#include "Interpreter.h"
#include "Permutation.h"
#include "SerializeTraces.h"

using HoleMap = std::map<size_t, mpz_class>;

enum class PatternType { Binary, Unary, HeapEquality, Range, ExprProp };

enum class ExprType {
    HeapAccess,
    Constant,
    Variable,
    Hole,
    Binary,
    Unary,
    HeapIndex,
    HeapValue
};

enum class ProgramIndex { First, Second };

// Used before a pattern is instantiated
struct VariablePlaceholder {
    bool operator==(const VariablePlaceholder & /* unused */) const {
        return true;
    }
};

mpz_class getHeapVal(HeapAddress addr, Heap heap);

template <typename T> struct RewrittenPattern;

template <typename T> struct HeapPattern {
    virtual size_t arguments() const = 0;
    virtual ~HeapPattern() = default;
    virtual PatternType getType() const = 0;
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>
    instantiate(const std::vector<smt::SortedVar> &variables,
                const VarMap<const llvm::Value *> &variableValues,
                const MonoPair<Heap> &heaps) const {
        size_t k = this->arguments();
        std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>
            matchingPatterns;
        // Find the llvm::Value*s corresponding to the variables
        // TODO the free vars map should simply use llvm::Value* to avoid this
        // search
        std::vector<const llvm::Value *> variablePointers;
        for (auto var : variables) {
            for (auto val : variableValues) {
                if (var.name == val.first->getName()) {
                    variablePointers.push_back(val.first);
                }
            }
        }
        /*
        std::cerr << "Variables:\n";
        for (auto var : variables) {
            std::cerr << var << ": "
                      << variableValues.at(var)->unsafeIntVal().get_str()
                      << "\n";
        }
        std::cerr << "Heap1:\n";
        for (auto heap : heaps.first) {
            std::cerr << heap.first.get_str() << ":"
                      << heap.second.val.get_str() << "\n";
        }
        std::cerr << "Heap2:\n";
        for (auto heap : heaps.second) {
            std::cerr << heap.first.get_str() << ":"
                      << heap.second.val.get_str() << "\n";
        }
        */
        if (k == 0) {
            auto pat = this->distributeArguments({});
            if (pat->matches(variableValues, heaps)) {
                matchingPatterns.push_back(pat);
            }
            return matchingPatterns;
        }
        for (const auto &vec :
             Range(Integer(mpz_class(0)),
                   Integer(mpz_class(variablePointers.size())) -
                       Integer(mpz_class(1)),
                   k)) {
            std::vector<const llvm::Value *> args(vec.size());
            for (size_t i = 0; i < args.size(); ++i) {
                args[i] = variablePointers[vec[i].asUnbounded().get_ui()];
            }
            auto pattern = this->distributeArguments(args);

            if (pattern->matches(variableValues, heaps)) {
                matchingPatterns.push_back(pattern);
            }
        }
        return matchingPatterns;
    }
    virtual std::shared_ptr<HeapPattern<const llvm::Value *>>
    distributeArguments(std::vector<const llvm::Value *> variables) const = 0;
    virtual bool matches(const VarMap<const llvm::Value *> &variables,
                         const MonoPair<Heap> &heaps,
                         const HoleMap &holes) const = 0;
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps) {
        const HoleMap holes;
        return this->matches(variables, heaps, holes);
    }
    virtual std::ostream &dump(std::ostream &os) const = 0;
    virtual bool equalTo(const HeapPattern<T> &other) const = 0;
    // Rewrite array accesses to conform to Eldarica's format
    virtual RewrittenPattern<T> rewriteHeap() const = 0;
    std::shared_ptr<HeapPattern<T>> instantiate() const;
    virtual std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const = 0;
    std::shared_ptr<HeapPattern<T>> negationNormalForm() const {
        return negationNormalForm(false);
    }
    virtual smt::SMTRef toSMT() const = 0;
};

enum class UnaryBooleanOp { Neg };
template <typename T> struct HeapExpr;
template <typename T>
using Constraints = std::vector<std::shared_ptr<HeapExpr<T>>>;

template <typename T> struct RewrittenPattern {
    MonoPair<Constraints<T>> constraints;
    std::shared_ptr<HeapPattern<T>> pat;
    RewrittenPattern(MonoPair<Constraints<T>> constraints,
                     std::shared_ptr<HeapPattern<T>> pat)
        : constraints(constraints), pat(pat) {}
    RewrittenPattern(std::shared_ptr<HeapPattern<T>> pat)
        : constraints(makeMonoPair<Constraints<T>>({}, {})), pat(pat) {}
};

template <typename T>
std::shared_ptr<HeapPattern<T>> HeapPattern<T>::instantiate() const {
    RewrittenPattern<T> newPat = rewriteHeap();
    return rewriteToImplication(newPat);
}

template <typename T>
std::shared_ptr<HeapPattern<T>>
rewriteToImplication(RewrittenPattern<T> rewrittenPattern);

enum class BinaryBooleanOp { And, Or, Impl };
enum class UnaryIntOp { Minus };
enum class BinaryIntOp { Mul, Add, Subtract };
enum class BinaryIntProp { LT, LE, EQ, GE, GT };

template <typename T> struct UnaryHeapPattern;
template <typename T> struct BinaryHeapPattern : public HeapPattern<T> {
    BinaryBooleanOp op;
    MonoPair<std::shared_ptr<HeapPattern<T>>> args;
    BinaryHeapPattern(BinaryBooleanOp op,
                      MonoPair<std::shared_ptr<HeapPattern<T>>> args)
        : op(op), args(args) {}
    RewrittenPattern<T> rewriteHeap() const override {
        // At this point we should be in negation normal form
        assert(op != BinaryBooleanOp::Impl);
        auto rewrittenPats = args.template map<RewrittenPattern<T>>(
            [](auto arg) { return arg->rewriteHeap(); });
        auto newPts = args.template map<std::shared_ptr<HeapPattern<T>>>(
            [](RewrittenPattern<T> pat) { return rewriteToImplication(pat); });
        return RewrittenPattern<T>(
            std::make_shared<BinaryHeapPattern<T>>(op, newPts));
    }
    PatternType getType() const override { return PatternType::Binary; }
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        std::vector<const llvm::Value *> argsFirst;
        std::vector<const llvm::Value *> argsSecond;
        auto mid =
            variables.begin() + static_cast<long>(args.first->arguments());
        argsFirst.insert(argsFirst.begin(), variables.begin(), mid);
        argsSecond.insert(argsSecond.begin(), mid, variables.end());
        return std::make_shared<BinaryHeapPattern<const llvm::Value *>>(
            op, makeMonoPair(args.first->distributeArguments(argsFirst),
                             args.second->distributeArguments(argsSecond)));
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps,
                 const HoleMap &holes) const override {
        MonoPair<bool> argMatches =
            args.template map<bool>([&variables, &heaps, &holes](auto pat) {
                return pat->matches(variables, heaps, holes);
            });
        switch (op) {
        case BinaryBooleanOp::And:
            return argMatches.first && argMatches.second;
        case BinaryBooleanOp::Or:
            return argMatches.first || argMatches.second;
        case BinaryBooleanOp::Impl:
            return !argMatches.first || argMatches.second;
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        args.first->dump(os);
        switch (op) {
        case BinaryBooleanOp::And:
            os << " ∧ ";
            break;
        case BinaryBooleanOp::Or:
            os << " ∨ ";
            break;
        case BinaryBooleanOp::Impl:
            os << " → ";
            break;
        }
        args.second->dump(os);
        os << ")";
        return os;
    }
    bool equalTo(const HeapPattern<T> &other) const override {
        if (other.getType() == PatternType::Binary) {
            auto binOther = static_cast<const BinaryHeapPattern<T> *>(&other);
            return op == binOther->op &&
                   args.first->equalTo(*binOther->args.first) &&
                   args.second->equalTo(*binOther->args.second);
        }
        return false;
    }
    std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const override {
        if (op == BinaryBooleanOp::Impl) {
            std::shared_ptr<HeapPattern<T>> firstArg =
                std::make_shared<UnaryHeapPattern<T>>(UnaryBooleanOp::Neg,
                                                      args.first);
            std::shared_ptr<HeapPattern<T>> secondArg = args.second;
            auto newArgs = makeMonoPair(firstArg, secondArg);
            return std::make_shared<BinaryHeapPattern<T>>(BinaryBooleanOp::Or,
                                                          newArgs)
                ->negationNormalForm(negate);
        }
        auto newArgs = args.template map<std::shared_ptr<HeapPattern<T>>>(
            [negate](std::shared_ptr<HeapPattern<T>> arg)
                -> std::shared_ptr<HeapPattern<T>> {
                    return arg->negationNormalForm(negate);
                });
        if (negate) {
            assert(op != BinaryBooleanOp::Impl);
            if (op == BinaryBooleanOp::And) {
                return std::make_shared<BinaryHeapPattern<T>>(
                    BinaryBooleanOp::Or, newArgs);
            } else {
                return std::make_shared<BinaryHeapPattern<T>>(
                    BinaryBooleanOp::And, newArgs);
            }
        } else {
            assert(op != BinaryBooleanOp::Impl);
            return std::make_shared<BinaryHeapPattern<T>>(op, newArgs);
        }
    }
    smt::SMTRef toSMT() const override {
        smt::SMTRef firstArg = args.first->toSMT();
        smt::SMTRef secondArg = args.second->toSMT();
        switch (op) {
        case BinaryBooleanOp::And:
            return smt::makeBinOp("and", std::move(firstArg),
                                  std::move(secondArg));
        case BinaryBooleanOp::Or:
            return smt::makeBinOp("or", std::move(firstArg),
                                  std::move(secondArg));
        case BinaryBooleanOp::Impl:
            return smt::makeBinOp("=>", std::move(firstArg),
                                  std::move(secondArg));
        }
    }
};

template <typename T> struct UnaryHeapPattern : public HeapPattern<T> {
    UnaryBooleanOp op;
    std::shared_ptr<HeapPattern<T>> arg;
    UnaryHeapPattern(UnaryBooleanOp op, std::shared_ptr<HeapPattern<T>> arg)
        : op(op), arg(arg) {}
    PatternType getType() const override { return PatternType::Unary; }
    size_t arguments() const override { return arg->arguments(); }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        return std::make_shared<UnaryHeapPattern<const llvm::Value *>>(
            op, arg->distributeArguments(variables));
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(¬";
        arg->dump(os);
        os << ")";
        return os;
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps,
                 const HoleMap &holes) const override {
        bool argMatches = arg->matches(variables, heaps, holes);
        switch (op) {
        case UnaryBooleanOp::Neg:
            return !argMatches;
        }
    }
    bool equalTo(const HeapPattern<T> &other) const override {
        if (other.getType() == PatternType::Unary) {
            auto unOther = static_cast<const UnaryHeapPattern<T> *>(&other);
            return op == unOther->op && arg->equalTo(*unOther->arg);
        }
        return false;
    }
    RewrittenPattern<T> rewriteHeap() const override {
        RewrittenPattern<T> rewrittenPat = arg->rewriteHeap();
        return RewrittenPattern<T>(
            rewrittenPat.constraints,
            std::make_shared<UnaryHeapPattern<T>>(op, rewrittenPat.pat));
    }
    std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const override {
        if (negate) {
            return arg;
        }
        return arg->negationNormalForm(true);
    }
    smt::SMTRef toSMT() const override {
        smt::SMTRef smtArg = arg->toSMT();
        switch (op) {
        case UnaryBooleanOp::Neg:
            return smt::makeUnaryOp("not", std::move(smtArg));
        }
    }
};

template <typename T> struct HeapExprProp;
template <typename T> struct HeapIndex;
template <typename T> struct HeapValue;

template <typename T> struct HeapEqual : public HeapPattern<T> {
    // All elements of the two heaps are equal
    HeapEqual() = default;
    size_t arguments() const override { return 0; }
    PatternType getType() const override { return PatternType::HeapEquality; }
    RewrittenPattern<T> rewriteHeap() const override {
        std::shared_ptr<HeapPattern<T>> premise =
            std::make_shared<HeapExprProp<T>>(
                BinaryIntProp::EQ,
                makeMonoPair(
                    std::make_shared<HeapIndex<T>>(ProgramIndex::First),
                    std::make_shared<HeapIndex<T>>(ProgramIndex::Second)));
        std::shared_ptr<HeapPattern<T>> conclusion =
            std::make_shared<HeapExprProp<T>>(
                BinaryIntProp::EQ,
                makeMonoPair(
                    std::make_shared<HeapValue<T>>(ProgramIndex::First),
                    std::make_shared<HeapValue<T>>(ProgramIndex::Second)));
        return RewrittenPattern<T>(std::make_shared<BinaryHeapPattern<T>>(
            BinaryBooleanOp::Impl, makeMonoPair(premise, conclusion)));
    }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> arguments) const override {
        assert(arguments.empty());
        unused(arguments);
        return std::make_shared<HeapEqual<const llvm::Value *>>();
    }
    bool matches(const VarMap<const llvm::Value *> & /* unused */,
                 const MonoPair<Heap> &heaps,
                 const HoleMap & /* unused */) const override {
        return heaps.first == heaps.second;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(Equal heaps)";
        return os;
    }
    smt::SMTRef toSMT() const override {
        std::vector<smt::SortedVar> args = {smt::SortedVar("heapIndex", "Int")};
        smt::SharedSMTRef expr =
            makeBinOp("=", smt::makeBinOp("select", "HEAP$1", "heapIndex"),
                      smt::makeBinOp("select", "HEAP$2", "heapIndex"));
        return std::make_unique<smt::Forall>(args, expr);
    }
    bool equalTo(const HeapPattern<T> &other) const override {
        return other.getType() == PatternType::HeapEquality;
    }
    std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const override {
        assert(!negate);
        return std::make_shared<HeapEqual<T>>();
    }
};

template <typename T> struct RewrittenExpr;

template <typename T> struct HeapExpr {
    virtual size_t arguments() const = 0;
    virtual ~HeapExpr() = default;
    virtual mpz_class eval(const VarMap<const llvm::Value *> &variables,
                           const MonoPair<Heap> &heaps,
                           const HoleMap &holes) const = 0;
    virtual std::shared_ptr<HeapExpr<const llvm::Value *>>
    distributeArguments(std::vector<const llvm::Value *> variables) const = 0;
    virtual std::ostream &dump(std::ostream &os) const = 0;
    virtual bool equalTo(const HeapExpr<T> &other) const = 0;
    virtual ExprType getType() const = 0;
    virtual RewrittenExpr<T> rewriteHeap() const = 0;
    virtual smt::SMTRef toSMT() const = 0;
};

template <typename T> struct RewrittenExpr {
    MonoPair<Constraints<T>> constraints;
    std::shared_ptr<HeapExpr<T>> pat;
    RewrittenExpr(MonoPair<Constraints<T>> constraints,
                  std::shared_ptr<HeapExpr<T>> pat)
        : constraints(constraints), pat(pat) {}
    RewrittenExpr(std::shared_ptr<HeapExpr<T>> pat)
        : constraints(makeMonoPair<Constraints<T>>({}, {})), pat(pat) {}
};

template <typename T>
MonoPair<Constraints<T>> mergeConstraints(MonoPair<RewrittenExpr<T>> pats) {
    MonoPair<Constraints<T>> result = pats.first.constraints;
    result.first.insert(result.first.end(),
                        pats.second.constraints.first.begin(),
                        pats.second.constraints.first.end());
    result.second.insert(result.second.end(),
                         pats.second.constraints.second.begin(),
                         pats.second.constraints.second.end());
    return result;
}

template <typename T> struct HeapIndex : public HeapExpr<T> {
    ProgramIndex index;
    HeapIndex(ProgramIndex index) : index(index) {}
    RewrittenExpr<T> rewriteHeap() const override {
        return RewrittenExpr<T>(std::make_shared<HeapIndex<T>>(index));
    }
    ExprType getType() const override { return ExprType::HeapIndex; }
    size_t arguments() const override { return 0; }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> /* unused */) const override {
        logError("Cannot distribute arguments on heap index\n");
        exit(1);
    }
    mpz_class eval(const VarMap<const llvm::Value *> & /* unused */,
                   const MonoPair<Heap> & /* unused */,
                   const HoleMap & /* unused */) const override {
        logError("Cannot evaluate heap index\n");
        exit(1);
    }
    std::ostream &dump(std::ostream &os) const override {
        switch (index) {
        case ProgramIndex::First:
            os << "i1";
            break;
        case ProgramIndex::Second:
            os << "i2";
            break;
        }
        return os;
    }
    bool equalTo(const HeapExpr<T> & /* unused */) const override {
        logError("Cannot compare heap index\n");
        exit(1);
    }
    smt::SMTRef toSMT() const override {
        switch (index) {
        case ProgramIndex::First:
            return smt::stringExpr("i1");
        case ProgramIndex::Second:
            return smt::stringExpr("i2");
        }
    }
};

template <typename T> struct HeapValue : public HeapExpr<T> {
    ProgramIndex index;
    HeapValue(ProgramIndex index) : index(index) {}
    RewrittenExpr<T> rewriteHeap() const override {
        return RewrittenExpr<T>(std::make_shared<HeapValue<T>>(index));
    }
    ExprType getType() const override { return ExprType::HeapValue; }
    size_t arguments() const override { return 0; }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> /* unused */) const override {
        logError("Cannot distribute arguments on heap value\n");
        exit(1);
    }
    mpz_class eval(const VarMap<const llvm::Value *> & /* unused */,
                   const MonoPair<Heap> & /* unused */,
                   const HoleMap & /* unused */) const override {
        logError("Cannot evaluate heap value\n");
        exit(1);
    }
    std::ostream &dump(std::ostream &os) const override {
        switch (index) {
        case ProgramIndex::First:
            os << "heap1";
            break;
        case ProgramIndex::Second:
            os << "heap2";
            break;
        }
        return os;
    }
    bool equalTo(const HeapExpr<T> & /* unused */) const override {
        logError("Cannot compare heap value\n");
        exit(1);
    }
    smt::SMTRef toSMT() const override {
        switch (index) {
        case ProgramIndex::First:
            return smt::stringExpr("heap1");
        case ProgramIndex::Second:
            return smt::stringExpr("heap2");
        }
    }
};

template <typename T> struct HeapAccess : public HeapExpr<T> {
    // Indicates which heap to look at
    ProgramIndex programIndex;
    // The variable to access the heap at
    std::shared_ptr<HeapExpr<T>> atVal;
    HeapAccess(ProgramIndex programIndex, std::shared_ptr<HeapExpr<T>> atVal)
        : programIndex(programIndex), atVal(atVal) {}
    RewrittenExpr<T> rewriteHeap() const override {
        MonoPair<Constraints<T>> constraints =
            makeMonoPair<Constraints<T>>({}, {});
        switch (programIndex) {
        case ProgramIndex::First:
            constraints.first.push_back(atVal);
            break;
        case ProgramIndex::Second:
            constraints.second.push_back(atVal);
            break;
        }
        return RewrittenExpr<T>(constraints,
                                std::make_shared<HeapValue<T>>(programIndex));
    }
    ExprType getType() const override { return ExprType::HeapAccess; }
    size_t arguments() const override { return atVal->arguments(); }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        return std::make_shared<HeapAccess<const llvm::Value *>>(
            programIndex, atVal->distributeArguments(variables));
    }
    mpz_class eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps,
                   const HoleMap &holes) const override {
        mpz_class atEval = atVal->eval(variables, heaps, holes);
        switch (programIndex) {
        case ProgramIndex::First:
            return getHeapVal(atEval, heaps.first);
        case ProgramIndex::Second:
            return getHeapVal(atEval, heaps.second);
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "heap$";
        switch (programIndex) {
        case ProgramIndex::First:
            os << "1";
            break;
        case ProgramIndex::Second:
            os << "2";
            break;
        }
        os << "[";
        atVal->dump(os);
        os << "]";
        return os;
    }
    bool equalTo(const HeapExpr<T> &other) const override {
        if (other.getType() == ExprType::HeapAccess) {
            auto accOther = static_cast<const HeapAccess<T> *>(&other);
            return programIndex == accOther->programIndex &&
                   atVal->equalTo(*accOther->atVal);
        }
        return false;
    }
    smt::SMTRef toSMT() const override {
        smt::SharedSMTRef heapName = smt::stringExpr(
            programIndex == ProgramIndex::First ? "HEAP$1" : "HEAP$2");
        smt::SharedSMTRef ref = atVal->toSMT();
        return makeBinOp("select", heapName, ref);
    }
};

template <typename T> struct Constant : public HeapExpr<T> {
    mpz_class value;
    Constant(mpz_class value) : value(value) {}
    ExprType getType() const override { return ExprType::Constant; }
    size_t arguments() const override { return 0; }
    RewrittenExpr<T> rewriteHeap() const override {
        return RewrittenExpr<T>(std::make_shared<Constant<T>>(value));
    }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> arguments) const override {
        assert(arguments.empty());
        unused(arguments);
        return std::make_shared<Constant<const llvm::Value *>>(value);
    }
    mpz_class eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> & /* unused */,
                   const HoleMap & /* unused */) const override {
        assert(variables.empty());
        unused(variables);
        return value;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << value.get_str();
        return os;
    }
    bool equalTo(const HeapExpr<T> &other) const override {
        if (other.getType() == ExprType::Constant) {
            auto constOther = static_cast<const Constant<T> *>(&other);
            return value == constOther->value;
        }
        return false;
    }
    smt::SMTRef toSMT() const override {
        return smt::stringExpr(value.get_str());
    }
};

template <typename T> struct Variable : public HeapExpr<T> {
    T varName;
    Variable(T varName) : varName(varName) {}
    RewrittenExpr<T> rewriteHeap() const override {
        return RewrittenExpr<T>(std::make_shared<Variable<T>>(varName));
    }
    ExprType getType() const override { return ExprType::Variable; }
    size_t arguments() const override { return 1; }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        assert(variables.size() == 1);
        return std::make_shared<Variable<const llvm::Value *>>(
            variables.front());
    }
    mpz_class eval(const VarMap<const llvm::Value *> & /* unused */,
                   const MonoPair<Heap> & /* unused */,
                   const HoleMap & /* unused */) const override {
        logError("Can only evaluate specialized version of variable\n");
        exit(1);
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "_";
        return os;
    }
    bool equalTo(const HeapExpr<T> &other) const override {
        if (other.getType() == ExprType::Variable) {
            auto varOther = static_cast<const Variable<T> *>(&other);
            return varName == varOther->varName;
        }
        return false;
    }
    smt::SMTRef toSMT() const override {
        logError("Can only convert specialized version of variable\n");
        return smt::stringExpr("ERROR");
    }
};

template <typename T> struct Hole : public HeapExpr<T> {
    // Ensuring that these indices are unique and match between the range
    // and
    // the corresponding pattern is up to the user
    size_t index;
    ExprType getType() const override { return ExprType::Hole; }
    size_t arguments() const override { return 0; }
    RewrittenExpr<T> rewriteHeap() const override {
        return RewrittenExpr<T>(std::make_shared<Hole<T>>(index));
    }
    Hole(size_t index) : index(index) {}
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        assert(variables.empty());
        unused(variables);
        return std::make_shared<Hole<const llvm::Value *>>(index);
    }
    mpz_class eval(const VarMap<const llvm::Value *> & /* unused */,
                   const MonoPair<Heap> & /* unused */,
                   const HoleMap &hole) const override {
        assert(hole.count(index) == 1);
        return hole.at(index);
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "i_";
        os << index;
        return os;
    }
    bool equalTo(const HeapExpr<T> &other) const override {
        if (other.getType() == ExprType::Hole) {
            auto holeOther = static_cast<const Hole<T> *>(&other);
            return index == holeOther->index;
        }
        return false;
    }
    smt::SMTRef toSMT() const override {
        return smt::stringExpr("boundVar_" + std::to_string(index));
    }
};

template <>
std::ostream &Variable<const llvm::Value *>::dump(std::ostream &os) const;
template <> smt::SMTRef Variable<const llvm::Value *>::toSMT() const;

template <>
mpz_class Variable<const llvm::Value *>::eval(
    const VarMap<const llvm::Value *> &variables, const MonoPair<Heap> &heaps,
    const HoleMap &holes) const;

template <typename T> struct BinaryIntExpr : public HeapExpr<T> {
    BinaryIntOp op;
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    BinaryIntExpr(BinaryIntOp op, MonoPair<std::shared_ptr<HeapExpr<T>>> args)
        : op(op), args(args) {}
    RewrittenExpr<T> rewriteHeap() const override {
        auto rewrittenPats = args.template map<RewrittenExpr<T>>(
            [](auto arg) -> RewrittenExpr<T> { arg->rewriteHeap(); });
        MonoPair<Constraints<T>> constrs = mergeConstraints(rewrittenPats);
        auto newArgs =
            makeMonoPair(rewrittenPats.first.pat, rewrittenPats.second.pat);
        return RewrittenExpr<T>(
            constrs, std::make_shared<BinaryIntExpr<T>>(op, newArgs));
    }
    ExprType getType() const override { return ExprType::Binary; }
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        auto mid = variables.begin() + args.first->arguments();
        std::vector<const llvm::Value *> firstArgs;
        firstArgs.insert(firstArgs.begin(), variables.begin(), mid);
        std::vector<const llvm::Value *> secondArgs;
        secondArgs.insert(secondArgs.begin(), mid, variables.end());
        return std::make_shared<BinaryIntExpr<const llvm::Value *>>(
            op, makeMonoPair(args.first->distributeArguments(firstArgs),
                             args.second->distributeArguments(secondArgs)));
    }
    mpz_class eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps,
                   const HoleMap &holes) const override {
        MonoPair<mpz_class> vals =
            args.template map<mpz_class>([&variables, &heaps, &holes](
                auto arg) { return arg->eval(variables, heaps, holes); });
        switch (op) {
        case BinaryIntOp::Mul:
            return vals.first * vals.second;
        case BinaryIntOp::Add:
            return vals.first + vals.second;
        case BinaryIntOp::Subtract:
            return vals.first - vals.second;
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        args.first->dump(os);
        switch (op) {
        case BinaryIntOp::Mul:
            os << " × ";
            break;
        case BinaryIntOp::Add:
            os << " + ";
            break;
        case BinaryIntOp::Subtract:
            os << " - ";
            break;
        }
        args.second->dump(os);
        os << ")";
        return os;
    }
    bool equalTo(const HeapExpr<T> &other) const override {
        if (other.getType() == ExprType::Binary) {
            auto binExpr = static_cast<const BinaryIntExpr<T> *>(&other);
            return op == binExpr->op &&
                   args.first->equalTo(*binExpr->args.first) &&
                   args.second->equalTo(*binExpr->args.second);
        }
        return false;
    }
    smt::SMTRef toSMT() const override {
        smt::SMTRef firstArg = args.first->toSMT();
        smt::SMTRef secondArg = args.second->toSMT();
        std::string opName;
        switch (op) {
        case BinaryIntOp::Add:
            opName = "+";
            break;
        case BinaryIntOp::Mul:
            opName = "*";
            break;
        case BinaryIntOp::Subtract:
            opName = "-";
            break;
        }
        return makeBinOp(opName, std::move(firstArg), std::move(secondArg));
    }
};

template <typename T> struct UnaryIntExpr : public HeapExpr<T> {
    UnaryIntOp op;
    std::shared_ptr<HeapExpr<T>> arg;
    size_t arguments() const override { return arg->arguments(); }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        os << "-";
        arg->dump(os);
        os << ")";
        return os;
    }
    mpz_class eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps,
                   const HoleMap &holes) const override {
        mpz_class argVal = arg->eval(variables, heaps, holes);
        switch (op) {
        case UnaryIntOp::Minus:
            return -argVal;
        }
    }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        return std::make_shared<UnaryIntExpr<const llvm::Value>>(
            op, arg->distributeArguments(variables));
    }
};

enum class RangeQuantifier { All, Any };

template <typename T> struct RangeProp : public HeapPattern<T> {
    RangeQuantifier quant;
    MonoPair<std::shared_ptr<HeapExpr<T>>> bounds;
    size_t index;
    // This pattern needs to have exactly one hole for the variable in the
    // range
    std::shared_ptr<HeapPattern<T>> pat;
    RangeProp(RangeQuantifier quant,
              MonoPair<std::shared_ptr<HeapExpr<T>>> bounds, size_t index,
              std::shared_ptr<HeapPattern<T>> pat)
        : quant(quant), bounds(bounds), index(index), pat(pat) {}
    RewrittenPattern<T> rewriteHeap() const override {
        auto rewrittenBounds = bounds.template map<RewrittenExpr<T>>(
            [](auto arg) -> RewrittenExpr<T> { arg->rewriteHeap(); });
        auto constrs = mergeConstraints(rewrittenBounds);
        auto newBounds =
            makeMonoPair(rewrittenBounds.first.pat, rewrittenBounds.second.pat);
        auto rewrittenPat = pat->rewriteHeap();
        constrs.first.insert(constrs.first.end(),
                             rewrittenPat.constraints.first.begin(),
                             rewrittenPat.constraints.first.end());
        constrs.second.insert(constrs.second.end(),
                              rewrittenPat.constraints.second.begin(),
                              rewrittenPat.constraints.second.end());
        return RewrittenPattern<T>(
            constrs, std::make_shared<RangeProp<T>>(quant, newBounds, index,
                                                    rewrittenPat.pat));
    }
    PatternType getType() const override { return PatternType::Range; }
    size_t arguments() const override {
        return bounds.first->arguments() + bounds.second->arguments() +
               pat->arguments();
    }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        auto mid1 =
            variables.begin() + static_cast<long>(bounds.first->arguments());
        auto mid2 = mid1 + static_cast<long>(bounds.second->arguments());
        std::vector<const llvm::Value *> firstArgs;
        firstArgs.insert(firstArgs.begin(), variables.begin(), mid1);
        std::vector<const llvm::Value *> secondArgs;
        secondArgs.insert(secondArgs.begin(), mid1, mid2);
        std::vector<const llvm::Value *> thirdArgs;
        thirdArgs.insert(thirdArgs.begin(), mid2, variables.end());
        return std::make_shared<RangeProp<const llvm::Value *>>(
            quant, makeMonoPair(bounds.first->distributeArguments(firstArgs),
                                bounds.second->distributeArguments(secondArgs)),
            index, pat->distributeArguments(thirdArgs));
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps,
                 const HoleMap &holes) const override {
        assert(holes.count(index) == 0);
        HoleMap newHoles = holes;
        MonoPair<mpz_class> boundVals = bounds.template map<mpz_class>(
            [&variables, &heaps,
             &newHoles](std::shared_ptr<HeapExpr<T>> arg) -> mpz_class {
                return arg->eval(variables, heaps, newHoles);
            });
        for (mpz_class i = boundVals.first; i <= boundVals.second; ++i) {
            newHoles[index] = i;
            bool result = pat->matches(variables, heaps, newHoles);
            if (result && quant == RangeQuantifier::Any) {
                return true;
            } else if (!result && quant == RangeQuantifier::All) {
                return false;
            }
        }
        switch (quant) {
        case RangeQuantifier::Any:
            return false;
        case RangeQuantifier::All:
            return true;
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        switch (quant) {
        case RangeQuantifier::Any:
            os << "∃";
            break;
        case RangeQuantifier::All:
            os << "∀";
            break;
        }
        std::string indexName = "i_" + std::to_string(index);
        os << indexName;
        os << ".";
        bounds.first->dump(os);
        os << indexName;
        bounds.second->dump(os);
        os << ", ";
        pat->dump(os);
        os << ")";
    }
    bool equalTo(const HeapPattern<T> &other) const override {
        if (other.getType() == PatternType::Range) {
            auto rangeOther = static_cast<const RangeProp<T> *>(&other);
            return quant == rangeOther->quant && index == rangeOther->index &&
                   bounds.first->equalTo(*rangeOther->bounds.first) &&
                   bounds.second->equalTo(*rangeOther->bounds.second) &&
                   pat->equalTo(*rangeOther->pat);
        }
        return false;
    }
    std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const override {
        RangeQuantifier newQuant = quant;
        if (negate) {
            newQuant = newQuant == RangeQuantifier::All ? RangeQuantifier::Any
                                                        : RangeQuantifier::All;
        }
        std::shared_ptr<HeapPattern<T>> newPat =
            pat->negationNormalForm(negate);
        return std::make_shared<RangeProp<T>>(newQuant, bounds, index, newPat);
    }
    smt::SMTRef toSMT() const override {

        std::vector<smt::SortedVar> args = {
            smt::SortedVar("boundVar_" + std::to_string(index), "Int")};
        smt::SharedSMTRef var =
            smt::stringExpr("boundVar_" + std::to_string(index));
        smt::SharedSMTRef arg1 = bounds.first->toSMT();
        smt::SharedSMTRef arg2 = bounds.second->toSMT();
        smt::SharedSMTRef rangeConstraint = makeBinOp(
            "and", makeBinOp("<=", arg1, var), makeBinOp("<=", var, arg2));
        smt::SharedSMTRef patRef = pat->toSMT();
        return std::make_unique<smt::Forall>(
            args, makeBinOp("=>", rangeConstraint, patRef));
    }
};

template <typename T> struct HeapExprProp : public HeapPattern<T> {
    BinaryIntProp op;
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    HeapExprProp(BinaryIntProp op, MonoPair<std::shared_ptr<HeapExpr<T>>> args)
        : op(op), args(args) {}
    RewrittenPattern<T> rewriteHeap() const override {
        MonoPair<RewrittenExpr<T>> rewrittenArgs =
            args.template map<RewrittenExpr<T>>(
                [](auto arg) -> RewrittenExpr<T> {
                    return arg->rewriteHeap();
                });
        auto constrs = mergeConstraints(rewrittenArgs);
        auto newArgs =
            makeMonoPair(rewrittenArgs.first.pat, rewrittenArgs.second.pat);
        return RewrittenPattern<T>(
            constrs, std::make_shared<HeapExprProp<T>>(op, newArgs));
    }
    PatternType getType() const override { return PatternType::ExprProp; }
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        auto mid =
            variables.begin() + static_cast<long>(args.first->arguments());
        std::vector<const llvm::Value *> firstArgs;
        firstArgs.insert(firstArgs.begin(), variables.begin(), mid);
        std::vector<const llvm::Value *> secondArgs;
        secondArgs.insert(secondArgs.begin(), mid, variables.end());
        return std::make_shared<HeapExprProp<const llvm::Value *>>(
            op, makeMonoPair(args.first->distributeArguments(firstArgs),
                             args.second->distributeArguments(secondArgs)));
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps,
                 const HoleMap &holes) const override {
        MonoPair<mpz_class> vals =
            args.template map<mpz_class>([&variables, &heaps, &holes](
                auto arg) { return arg->eval(variables, heaps, holes); });
        switch (op) {
        case BinaryIntProp::LT:
            return vals.first < vals.second;
        case BinaryIntProp::LE:
            return vals.first <= vals.second;
        case BinaryIntProp::EQ:
            return vals.first == vals.second;
        case BinaryIntProp::GE:
            return vals.first >= vals.second;
        case BinaryIntProp::GT:
            return vals.first > vals.second;
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        args.first->dump(os);
        switch (op) {
        case BinaryIntProp::LT:
            os << " < ";
            break;
        case BinaryIntProp::LE:
            os << " <= ";
            break;
        case BinaryIntProp::EQ:
            os << " = ";
            break;
        case BinaryIntProp::GE:
            os << " >= ";
            break;
        case BinaryIntProp::GT:
            os << " > ";
            break;
        }
        args.second->dump(os);
        os << ")";
        return os;
    }
    bool equalTo(const HeapPattern<T> &other) const override {
        if (other.getType() == PatternType::ExprProp) {
            auto exprOther = static_cast<const HeapExprProp<T> *>(&other);
            return op == exprOther->op &&
                   args.first->equalTo(*exprOther->args.first) &&
                   args.second->equalTo(*exprOther->args.second);
        }
        return false;
    }
    std::shared_ptr<HeapPattern<T>>
    negationNormalForm(bool negate) const override {
        if (negate) {
            return std::make_shared<UnaryHeapPattern<T>>(
                UnaryBooleanOp::Neg,
                std::make_shared<HeapExprProp<T>>(op, args));
        } else {
            return std::make_shared<HeapExprProp<T>>(op, args);
        }
    }
    smt::SMTRef toSMT() const override {
        std::string opName;
        switch (op) {
        case BinaryIntProp::LT:
            opName = "<";
            break;
        case BinaryIntProp::LE:
            opName = "<=";
            break;
        case BinaryIntProp::EQ:
            opName = "=";
            break;
        case BinaryIntProp::GE:
            opName = ">=";
            break;
        case BinaryIntProp::GT:
            opName = ">";
            break;
        }
        return makeBinOp(opName, args.first->toSMT(), args.second->toSMT());
    }
};

std::vector<std::shared_ptr<HeapPattern<VariablePlaceholder>>>
parsePatterns(FILE *stream);

template <typename T>
std::shared_ptr<HeapPattern<T>>
rewriteToImplication(RewrittenPattern<T> rewrittenPattern) {
    if (rewrittenPattern.constraints.first.size() > 1) {
        logError("Pattern cannot be rewritten for Eldarica\n");
        exit(1);
    }
    if (rewrittenPattern.constraints.second.size() > 1) {
        logError("Pattern cannot be rewritter for Eldarica\n");
        exit(1);
    }
    std::shared_ptr<HeapExpr<T>> index1 =
        std::make_shared<HeapIndex<T>>(ProgramIndex::First);
    std::shared_ptr<HeapExpr<T>> index2 =
        std::make_shared<HeapIndex<T>>(ProgramIndex::Second);
    if (rewrittenPattern.constraints.first.size() == 1 &&
        rewrittenPattern.constraints.second.size() == 1) {
        std::shared_ptr<HeapExpr<T>> constr1 =
            rewrittenPattern.constraints.first.front();
        std::shared_ptr<HeapPattern<T>> arg1 =
            std::make_shared<HeapExprProp<T>>(BinaryIntProp::EQ,
                                              makeMonoPair(index1, constr1));
        std::shared_ptr<HeapExpr<T>> constr2 =
            rewrittenPattern.constraints.second.front();
        std::shared_ptr<HeapPattern<T>> arg2 =
            std::make_shared<HeapExprProp<T>>(BinaryIntProp::EQ,
                                              makeMonoPair(index2, constr2));
        std::shared_ptr<HeapPattern<T>> constrs =
            std::make_shared<BinaryHeapPattern<T>>(BinaryBooleanOp::And,
                                                   makeMonoPair(arg1, arg2));
        return std::make_shared<BinaryHeapPattern<T>>(
            BinaryBooleanOp::Impl, makeMonoPair(constrs, rewrittenPattern.pat));
    }
    if (rewrittenPattern.constraints.first.size() == 1) {
        std::shared_ptr<HeapPattern<T>> arg1 =
            std::make_shared<HeapExprProp<T>>(
                BinaryIntProp::EQ,
                makeMonoPair(index1,
                             rewrittenPattern.constraints.first.front()));
        return std::make_shared<BinaryHeapPattern<T>>(
            BinaryBooleanOp::Impl, makeMonoPair(arg1, rewrittenPattern.pat));
    }
    if (rewrittenPattern.constraints.second.size() == 1) {
        std::shared_ptr<HeapPattern<T>> arg2 =
            std::make_shared<HeapExprProp<T>>(
                BinaryIntProp::EQ,
                makeMonoPair(index2,
                             rewrittenPattern.constraints.second.front()));
        return std::make_shared<BinaryHeapPattern<T>>(
            BinaryBooleanOp::Impl, makeMonoPair(arg2, rewrittenPattern.pat));
    }
    return rewrittenPattern.pat;
}
