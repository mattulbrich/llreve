#include "Pattern.h"

#include "Permutation.h"

using std::ostream;
using std::vector;
using std::string;
using std::list;
using std::map;
using std::set;
using std::shared_ptr;
using std::make_shared;
using std::static_pointer_cast;

using namespace pattern;

ostream &Expr::dump(ostream &os,
                    vector<shared_ptr<InstantiatedValue>> vec) const {
    return dump(os, vec.begin(), vec.end());
}

bool BinaryOp::matches(VecIter begin, VecIter end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    switch (op) {
    case Operation::Eq: {
        VecIter mid = begin + static_cast<long>(args.first->arguments());
        VarIntVal left = args.first->eval(begin, mid);
        VarIntVal right = args.second->eval(mid, end);
        return left == right;
    }
    case Operation::Add:
        logWarning("Matching on an addition is always true\n");
        return true;
    }
}

VarIntVal BinaryOp::eval(VecIter begin, VecIter end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    VecIter mid = begin + static_cast<long>(args.first->arguments());
    VarIntVal left = args.first->eval(begin, mid);
    VarIntVal right = args.second->eval(mid, end);
    switch (op) {
    case Operation::Eq:
        logWarning("Evaluating equality equality, converting to integer\n");
        return left == right;
    case Operation::Add:
        return left + right;
    }
}

size_t BinaryOp::arguments() const {
    return args.first->arguments() + args.second->arguments();
}

size_t BinaryOp::variables() const {
    return args.first->variables() + args.second->variables();
}

ostream &
BinaryOp::dump(ostream &os,
               vector<shared_ptr<InstantiatedValue>>::iterator begin,
               vector<shared_ptr<InstantiatedValue>>::iterator end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    vector<shared_ptr<InstantiatedValue>>::iterator mid =
        begin + static_cast<long>(args.first->arguments());
    os << "(";
    args.first->dump(os, begin, mid);
    switch (op) {
    case Operation::Eq:
        os << " = ";
        break;
    case Operation::Add:
        os << " + ";
        break;
    }
    args.second->dump(os, mid, end);
    os << ")";
    return os;
}

bool Value::matches(VecIter begin, VecIter end) const {
    assert(end - begin == 1);
    return true;
}

VarIntVal Value::eval(VecIter begin, VecIter end) const {
    assert(end - begin == 1);
    return *begin;
}

size_t Value::arguments() const { return 1; }

size_t Value::variables() const {
    switch (val) {
    case Placeholder::Variable:
        return 1;
    case Placeholder::Constant:
        return 0;
    }
}

ostream &
Value::dump(ostream &os, vector<shared_ptr<InstantiatedValue>>::iterator begin,
            vector<shared_ptr<InstantiatedValue>>::iterator end) const {
    assert(end - begin == 1);
    switch ((*begin)->getType()) {
    case Placeholder::Constant:
        assert(val == Placeholder::Constant);
        os << static_pointer_cast<Constant>(*begin)->val.get_str();
        break;
    case Placeholder::Variable:
        assert(val == Placeholder::Variable);
        os << static_pointer_cast<Variable>(*begin)->name;
        break;
    }
    return os;
}

list<vector<shared_ptr<InstantiatedValue>>>
BinaryOp::instantiate(vector<string> variables,
                      VarMap<string> variableValues) const {
    if (op == Operation::Add && this->variables() == arguments()) {
        list<vector<shared_ptr<InstantiatedValue>>> output;
        for (auto vec : kPermutations(variables, arguments())) {
            vector<shared_ptr<InstantiatedValue>> outputVec(vec.size());
            for (size_t i = 0; i < vec.size(); ++i) {
                outputVec.at(i) = make_shared<Variable>(vec.at(i));
            }
        }
        return output;
    } else {
        // Only an equality can instantiate constants without a value
        assert(op == Operation::Eq);
        // We expect exactly one constant

        if (args.first->variables() == args.first->arguments()) {
            assert(args.second->arguments() - args.second->variables() == 1 ||
                   args.second->arguments() == args.second->variables());
            // Either there is a constant on the right or there is no constant
            // at all. In both cases we go through each instantiation on the
            // left and take all instantiations on the right with the same
            // value.
            list<vector<shared_ptr<InstantiatedValue>>> output;

            for (auto vec : kPermutations(variables, args.first->variables())) {
                vector<VarIntVal> leftValues(vec.size());
                for (size_t i = 0; i < leftValues.size(); ++i) {
                    leftValues.at(i) =
                        variableValues.at(vec.at(i))->unsafeIntVal();
                }
                VarIntVal leftValue =
                    args.first->eval(leftValues.begin(), leftValues.end());
                // Variables are only allowed to appear either left or right
                set<string> leftVariables;
                leftVariables.insert(vec.begin(), vec.end());
                vector<string> rightVariables;
                for (auto var : variables) {
                    if (leftVariables.find(var) == leftVariables.end()) {
                        rightVariables.push_back(var);
                    }
                }
                list<vector<shared_ptr<InstantiatedValue>>> rightResult =
                    args.second->instantiateToValue(rightVariables,
                                                    variableValues, leftValue);
                for (auto right : rightResult) {
                    vector<shared_ptr<InstantiatedValue>> res;
                    for (auto var : vec) {
                        res.push_back(make_shared<Variable>(var));
                    }
                    res.insert(res.end(), right.begin(), right.end());
                    output.push_back(res);
                }
            }
            return output;
        } else {
            // The constant is on the left
            assert(arguments() - this->variables() == 1);
            assert(args.first->arguments() - args.first->variables() == 1);
            list<vector<shared_ptr<InstantiatedValue>>> output;

            for (auto vec :
                 kPermutations(variables, args.second->variables())) {
                vector<VarIntVal> rightValues(vec.size());
                for (size_t i = 0; i < rightValues.size(); ++i) {
                    rightValues.at(i) =
                        variableValues.at(vec.at(i))->unsafeIntVal();
                }
                VarIntVal rightValue =
                    args.second->eval(rightValues.begin(), rightValues.end());
                // Variables are only allowed to appear either left or right
                set<string> rightVariables;
                rightVariables.insert(vec.begin(), vec.end());
                vector<string> leftVariables;
                for (auto var : variables) {
                    if (rightVariables.find(var) == rightVariables.end()) {
                        leftVariables.push_back(var);
                    }
                }
                list<vector<shared_ptr<InstantiatedValue>>> leftResult =
                    args.first->instantiateToValue(leftVariables,
                                                   variableValues, rightValue);
                for (auto left : leftResult) {
                    vector<shared_ptr<InstantiatedValue>> res;
                    res.insert(res.end(), left.begin(), left.end());
                    for (auto var : vec) {
                        res.push_back(make_shared<Variable>(var));
                    }
                    output.push_back(res);
                }
            }
            return output;
        }
    }
}

list<vector<shared_ptr<InstantiatedValue>>>
BinaryOp::instantiateToValue(vector<string> variables,
                             VarMap<string> variableValues,
                             VarIntVal value) const {
    assert(arguments() - this->variables() == 1);
    assert(op == Operation::Add);
    if (args.first->variables() == args.first->arguments()) {
        return instantiateAddWithConstant(*args.first, *args.second, variables,
                                          variableValues, value, false);
    } else {
        return instantiateAddWithConstant(*args.second, *args.first, variables,
                                          variableValues, value, true);
    }
}

list<vector<shared_ptr<InstantiatedValue>>>
Value::instantiateToValue(vector<string> variables,
                          VarMap<string> variableValues,
                          VarIntVal value) const {
    switch (val) {
    case Placeholder::Constant: {
        return {{make_shared<Constant>(value)}};
    }
    case Placeholder::Variable: {
        list<vector<shared_ptr<InstantiatedValue>>> output;
        for (auto var : variables) {
            if (variableValues.at(var)->unsafeIntVal() == value) {
                output.push_back({make_shared<Variable>(var)});
            }
        }
        return output;
    }
    }
}

list<vector<shared_ptr<InstantiatedValue>>>
Value::instantiate(vector<string> variables, VarMap<string> /*unused*/) const {
    assert(val == Placeholder::Variable);
    list<vector<shared_ptr<InstantiatedValue>>> output;
    for (auto var : variables) {
        output.push_back({make_shared<Variable>(var)});
    }
    return output;
}

InstantiatedValue::~InstantiatedValue() = default;
Placeholder Constant::getType() const { return Placeholder::Constant; }
Placeholder Variable::getType() const { return Placeholder::Variable; }

VarIntVal Constant::getValue(VarMap<string> /*unused*/) const { return val; }
VarIntVal Variable::getValue(VarMap<string> varVals) const {
    auto ret = varVals.at(name);
    assert(ret->getType() == VarType::Int);
    return static_pointer_cast<VarInt>(ret)->val;
}

list<vector<shared_ptr<InstantiatedValue>>> pattern::instantiateAddWithConstant(
    const Expr &pat, const Expr &patWithConstant, vector<string> variables,
    VarMap<string> variableValues, VarIntVal value, bool patWithConstantFirst) {
    assert(pat.variables() == pat.arguments());
    assert(patWithConstant.arguments() - patWithConstant.variables() == 1);
    list<vector<shared_ptr<InstantiatedValue>>> output;

    for (auto variableInstantiation :
         kPermutations(variables, pat.variables())) {
        vector<VarIntVal> values(variableInstantiation.size());
        for (size_t i = 0; i < values.size(); ++i) {
            values.at(i) =
                variableValues.at(variableInstantiation.at(i))->unsafeIntVal();
        }
        VarIntVal targetValue = pat.eval(values.begin(), values.end());
        // Variables are only allowed to appear on one side
        set<string> usedVariables;
        usedVariables.insert(variableInstantiation.begin(),
                             variableInstantiation.end());
        vector<string> availableVariables;
        for (auto var : variables) {
            if (usedVariables.find(var) == usedVariables.end()) {
                availableVariables.push_back(var);
            }
        }
        list<vector<shared_ptr<InstantiatedValue>>> constantInstantiations =
            patWithConstant.instantiateToValue(
                availableVariables, variableValues, value - targetValue);
        for (auto constantInstantiation : constantInstantiations) {
            vector<shared_ptr<InstantiatedValue>> instantiation;
            if (patWithConstantFirst) {
                instantiation.insert(instantiation.end(),
                                     constantInstantiation.begin(),
                                     constantInstantiation.end());
            }
            for (auto var : variableInstantiation) {
                instantiation.push_back(make_shared<Variable>(var));
            }
            if (!patWithConstantFirst) {
                instantiation.insert(instantiation.end(),
                                     constantInstantiation.begin(),
                                     constantInstantiation.end());
            }

            output.push_back(instantiation);
        }
    }
    return output;
}
