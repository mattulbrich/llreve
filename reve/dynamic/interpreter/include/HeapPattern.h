#pragma once

#include "Permutation.h"
#include "Interpreter.h"

// Used before a pattern is instantiated
struct VariablePlaceholder {};

VarIntVal getHeapVal(HeapAddress addr, Heap heap);

template <typename T> struct HeapPattern {
    virtual size_t arguments() const = 0;
    virtual ~HeapPattern() = default;
    std::list<std::shared_ptr<HeapPattern<std::string>>>
    instantiate(std::vector<std::string> variables,
                VarMap<std::string> variableValues,
                MonoPair<Heap> heaps) const {
        size_t k = this->arguments();
        std::list<std::shared_ptr<HeapPattern<std::string>>> matchingPatterns;
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
        for (auto vec : kPermutations(variables, k)) {
            auto pattern = this->distributeArguments(vec);

            if (pattern->matches(variableValues, heaps)) {
                matchingPatterns.push_back(pattern);
            }
        }
        return matchingPatterns;
    }
    virtual std::shared_ptr<HeapPattern<std::string>>
    distributeArguments(std::vector<std::string> variables) const = 0;
    virtual bool matches(VarMap<std::string> variables,
                         MonoPair<Heap> heaps) const = 0;
    virtual std::ostream &dump(std::ostream &os) const = 0;
};

enum class UnaryBooleanOp { Neg };
enum class BinaryBooleanOp { And, Or };
enum class UnaryIntOp { Minus };
enum class BinaryIntOp { Mul, Add, Subtract };

template <typename T> struct BinaryHeapPattern : public HeapPattern<T> {
    BinaryBooleanOp op;
    MonoPair<std::shared_ptr<HeapPattern<T>>> args;
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapPattern<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        std::vector<std::string> argsFirst;
        std::vector<std::string> argsSecond;
        auto mid = variables.begin() + args.first->arguments();
        argsFirst.insert(argsFirst.begin(), variables.begin(), mid);
        argsSecond.insert(argsSecond.begin(), mid, variables.end());
        return std::make_shared<BinaryHeapPattern<std::string>>(
            op, makeMonoPair(args.first->distributeArguments(argsFirst),
                             args.second->distributeArguments(argsSecond)));
    }
    bool matches(VarMap<std::string> variables,
                 MonoPair<Heap> heaps) const override {
        MonoPair<bool> argMatches = args.template map<bool>(
            [&variables, &heaps](std::shared_ptr<HeapPattern<T>> pat) {
                return pat->matches(variables, heaps);
            });
        switch (op) {
        case BinaryBooleanOp::And:
            return argMatches.first && argMatches.second;
        case BinaryBooleanOp::Or:
            return argMatches.first || argMatches.second;
        }
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        args.first->dump(os);
        switch (op) {
        case BinaryBooleanOp::And:
            os << " /\\ ";
            break;
        case BinaryBooleanOp::Or:
            os << " \\/ ";
            break;
        }
        args.second->dump(os);
        os << ")";
        return os;
    }
};

template <typename T> struct UnaryHeapPattern : public HeapPattern<T> {
    UnaryBooleanOp op;
    std::shared_ptr<HeapPattern<T>> arg;
    size_t arguments() const override { return arg->arguments(); }
    std::ostream &dump(std::ostream &os) const override {
        os << "(~";
        arg->dump(os);
        os << ")";
        return os;
    }
};

template <typename T> struct HeapEqual : public HeapPattern<T> {
    // All elements of the two heaps are equal
    size_t arguments() const override { return 0; }
    std::shared_ptr<HeapPattern<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        assert(variables.size() == 0);
        return std::make_shared<HeapEqual<std::string>>();
    }
    bool matches(VarMap<std::string> /* unused */,
                 MonoPair<Heap> heaps) const override {
        return heaps.first == heaps.second;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(Equal heaps)";
        return os;
    }
};

template <typename T> struct HeapExpr {
    virtual size_t arguments() const = 0;
    virtual ~HeapExpr() = default;
    virtual VarIntVal eval(VarMap<std::string> variables,
                           MonoPair<Heap> heaps) const = 0;
    virtual std::shared_ptr<HeapExpr<std::string>>
    distributeArguments(std::vector<std::string> variables) const = 0;
    virtual std::ostream &dump(std::ostream &os) const = 0;
};

enum class ProgramIndex { First, Second };
template <typename T> struct HeapAccess : public HeapExpr<T> {
    // Indicates which heap to look at
    ProgramIndex programIndex;
    // The variable to access the heap at
    std::shared_ptr<HeapExpr<T>> atVal;
    HeapAccess(ProgramIndex programIndex, std::shared_ptr<HeapExpr<T>> atVal)
        : programIndex(programIndex), atVal(atVal) {}
    size_t arguments() const override { return atVal->arguments(); }
    std::shared_ptr<HeapExpr<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        return std::make_shared<HeapAccess<std::string>>(
            programIndex, atVal->distributeArguments(variables));
    }
    VarIntVal eval(VarMap<std::string> variables,
                   MonoPair<Heap> heaps) const override {
        VarIntVal atEval = atVal->eval(variables, heaps);
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
};

template <typename T> struct Constant : public HeapExpr<T> {
    VarIntVal value;
    size_t arguments() const override { return 0; }
    std::shared_ptr<HeapExpr<std::string>> distributeArguments(
        std::vector<std::string> /* unused */) const override {
        return std::make_shared<Constant<std::string>>(value);
    }
    VarIntVal eval(VarMap<std::string> /* unused */,
                   MonoPair<Heap> /* unused */) const override {
        return value;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << value.get_str();
        return os;
    }
};

template <typename T> struct Variable : public HeapExpr<T> {
    T varName;
    Variable(T varName) : varName(varName) {}
    size_t arguments() const override { return 1; }
    std::shared_ptr<HeapExpr<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        assert(variables.size() == 1);
        return std::make_shared<Variable<std::string>>(variables.front());
    }
    VarIntVal eval(VarMap<std::string> /* unused */,
                   MonoPair<Heap> /* unused */) const override {
        logError("Can only evaluate specialized version of variable\n");
        return 0;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "variable";
        return os;
    }
};

template <> std::ostream &Variable<std::string>::dump(std::ostream &os) const;

template <>
VarIntVal Variable<std::string>::eval(VarMap<std::string> variables,
                                      MonoPair<Heap> heaps) const;

template <typename T> struct BinaryIntExpr : public HeapExpr<T> {
    BinaryIntOp op;
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapExpr<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        auto mid = variables.begin() + args.first->arguments();
        return std::make_shared<BinaryIntExpr<std::string>>(
            op, makeMonoPair(
                    args.first->distributeArguments(variables.begin(), mid),
                    args.second->distributeArguments(mid, variables.end())));
    }
    VarIntVal eval(VarMap<std::string> variables,
                   MonoPair<Heap> heaps) const override {
        MonoPair<VarIntVal> vals = args.template map<VarIntVal>(
            [&variables, &heaps](std::shared_ptr<HeapExpr<T>> arg) {
                return arg->eval(variables, heaps);
            });
        switch (op) {
        case BinaryIntOp::Mul:
            return vals.first * vals.second;
        case BinaryIntOp::Add:
            return vals.first + vals.second;
        case BinaryIntOp::Subtract:
            return vals.first - vals.second;
        }
    }
    std::ostream &dump(std::ostream &os) {
        os << "(";
        args.first->dump(os);
        switch (op) {
        case BinaryIntOp::Mul:
            os << " * ";
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
};

template <typename T> struct UnaryIntExpr : public HeapExpr<T> {
    UnaryIntOp op;
    std::shared_ptr<HeapExpr<T>> arg;
    size_t arguments() const override { return arg->arguments(); }
};

template <typename T> struct HeapExprEq : public HeapPattern<T> {
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    HeapExprEq(MonoPair<std::shared_ptr<HeapExpr<T>>> args) : args(args) {}
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapPattern<std::string>>
    distributeArguments(std::vector<std::string> variables) const override {
        auto mid =
            variables.begin() + static_cast<long>(args.first->arguments());
        std::vector<std::string> firstArgs;
        firstArgs.insert(firstArgs.begin(), variables.begin(), mid);
        std::vector<std::string> secondArgs;
        secondArgs.insert(secondArgs.begin(), mid, variables.end());
        return std::make_shared<HeapExprEq<std::string>>(
            makeMonoPair(args.first->distributeArguments(firstArgs),
                         args.second->distributeArguments(secondArgs)));
    }
    bool matches(VarMap<std::string> variables,
                 MonoPair<Heap> heaps) const override {
        MonoPair<VarIntVal> vals = args.template map<VarIntVal>(
            [&variables, &heaps](std::shared_ptr<HeapExpr<T>> arg) {
                return arg->eval(variables, heaps);
            });
        return vals.first == vals.second;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        args.first->dump(os);
        os << " = ";
        args.second->dump(os);
        os << ")";
        return os;
    }
};
