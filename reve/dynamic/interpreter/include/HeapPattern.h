#pragma once

#include "Compat.h"
#include "Interpreter.h"
#include "Permutation.h"

// Used before a pattern is instantiated
struct VariablePlaceholder {};

VarIntVal getHeapVal(HeapAddress addr, Heap heap);

template <typename T> struct HeapPattern {
    virtual size_t arguments() const = 0;
    virtual ~HeapPattern() = default;
    std::list<std::shared_ptr<HeapPattern<const llvm::Value *>>>
    instantiate(std::vector<std::string> variables,
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
                if (var == val.first->getName()) {
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
        for (auto vec : kPermutations(variablePointers, k)) {
            auto pattern = this->distributeArguments(vec);

            if (pattern->matches(variableValues, heaps)) {
                matchingPatterns.push_back(pattern);
            }
        }
        return matchingPatterns;
    }
    virtual std::shared_ptr<HeapPattern<const llvm::Value *>>
    distributeArguments(std::vector<const llvm::Value *> variables) const = 0;
    virtual bool matches(const VarMap<const llvm::Value *> &variables,
                         const MonoPair<Heap> &heaps) const = 0;
    virtual std::ostream &dump(std::ostream &os) const = 0;
};

enum class UnaryBooleanOp { Neg };
enum class BinaryBooleanOp { And, Or, Impl };
enum class UnaryIntOp { Minus };
enum class BinaryIntOp { Mul, Add, Subtract };
enum class BinaryIntProp { LT, LE, EQ, GE, GT };

template <typename T> struct BinaryHeapPattern : public HeapPattern<T> {
    BinaryBooleanOp op;
    MonoPair<std::shared_ptr<HeapPattern<T>>> args;
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        std::vector<const llvm::Value *> argsFirst;
        std::vector<const llvm::Value *> argsSecond;
        auto mid = variables.begin() + args.first->arguments();
        argsFirst.insert(argsFirst.begin(), variables.begin(), mid);
        argsSecond.insert(argsSecond.begin(), mid, variables.end());
        return std::make_shared<BinaryHeapPattern<const llvm::Value *>>(
            op, makeMonoPair(args.first->distributeArguments(argsFirst),
                             args.second->distributeArguments(argsSecond)));
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps) const override {
        MonoPair<bool> argMatches = args.template map<bool>(
            [&variables, &heaps](std::shared_ptr<HeapPattern<T>> pat) {
                return pat->matches(variables, heaps);
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
            os << " /\\ ";
            break;
        case BinaryBooleanOp::Or:
            os << " \\/ ";
            break;
        case BinaryBooleanOp::Impl:
            os << " -> ";
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
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        return std::make_shared<UnaryHeapPattern<const llvm::Value *>>(
            op, arg->distributeArguments(variables));
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "(~";
        arg->dump(os);
        os << ")";
        return os;
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps) const override {
        bool argMatches = arg->matches(variables, heaps);
        switch (op) {
        case UnaryBooleanOp::Neg:
            return !argMatches;
        }
    }
};

template <typename T> struct HeapEqual : public HeapPattern<T> {
    // All elements of the two heaps are equal
    size_t arguments() const override { return 0; }
    std::shared_ptr<HeapPattern<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> arguments) const override {
        assert(arguments.empty());
        unused(arguments);
        return std::make_shared<HeapEqual<const llvm::Value *>>();
    }
    bool matches(const VarMap<const llvm::Value *> &variables,
                 const MonoPair<Heap> &heaps) const override {
        assert(variables.empty());
        unused(variables);
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
    virtual VarIntVal eval(const VarMap<const llvm::Value *> &variables,
                           const MonoPair<Heap> &heaps) const = 0;
    virtual std::shared_ptr<HeapExpr<const llvm::Value *>>
    distributeArguments(std::vector<const llvm::Value *> variables) const = 0;
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
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        return std::make_shared<HeapAccess<const llvm::Value *>>(
            programIndex, atVal->distributeArguments(variables));
    }
    VarIntVal eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps) const override {
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
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> arguments) const override {
        assert(arguments.empty());
        unused(arguments);
        return std::make_shared<Constant<const llvm::Value *>>(value);
    }
    VarIntVal eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> & /* unused */) const override {
        assert(variables.empty());
        unused(variables);
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
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        assert(variables.size() == 1);
        return std::make_shared<Variable<const llvm::Value *>>(
            variables.front());
    }
    VarIntVal eval(const VarMap<const llvm::Value *> & /* unused */,
                   const MonoPair<Heap> & /* unused */) const override {
        logError("Can only evaluate specialized version of variable\n");
        return 0;
    }
    std::ostream &dump(std::ostream &os) const override {
        os << "variable";
        return os;
    }
};

template <>
std::ostream &Variable<const llvm::Value *>::dump(std::ostream &os) const;

template <>
VarIntVal Variable<const llvm::Value *>::eval(
    const VarMap<const llvm::Value *> &variables,
    const MonoPair<Heap> &heaps) const;

template <typename T> struct BinaryIntExpr : public HeapExpr<T> {
    BinaryIntOp op;
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    size_t arguments() const override {
        return args.first->arguments() + args.second->arguments();
    }
    std::shared_ptr<HeapExpr<const llvm::Value *>> distributeArguments(
        std::vector<const llvm::Value *> variables) const override {
        auto mid = variables.begin() + args.first->arguments();
        return std::make_shared<BinaryIntExpr<const llvm::Value *>>(
            op, makeMonoPair(
                    args.first->distributeArguments(variables.begin(), mid),
                    args.second->distributeArguments(mid, variables.end())));
    }
    VarIntVal eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps) const override {
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
    std::ostream &dump(std::ostream &os) const override {
        os << "(";
        os << "-";
        arg->dump(os);
        os << ")";
        return os;
    }
    VarIntVal eval(const VarMap<const llvm::Value *> &variables,
                   const MonoPair<Heap> &heaps) const override {
        VarIntVal argVal = arg->eval(variables, heaps);
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

template <typename T> struct HeapExprProp : public HeapPattern<T> {
    BinaryIntProp op;
    MonoPair<std::shared_ptr<HeapExpr<T>>> args;
    HeapExprProp(BinaryIntProp op, MonoPair<std::shared_ptr<HeapExpr<T>>> args)
        : op(op), args(args) {}
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
                 const MonoPair<Heap> &heaps) const override {
        MonoPair<VarIntVal> vals = args.template map<VarIntVal>(
            [&variables, &heaps](std::shared_ptr<HeapExpr<T>> arg) {
                return arg->eval(variables, heaps);
            });
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
        case BinaryIntProp::LE:
            os << " < ";
            break;
        case BinaryIntProp::LT:
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
};
