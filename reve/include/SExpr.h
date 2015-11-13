#ifndef SEXPR_H
#define SEXPR_H

#include <algorithm>
#include <memory>
#include <ostream>
#include <vector>

namespace sexpr {

template <typename T> class SExpr {
  public:
    virtual void serialize(std::ostream &OS, size_t Indent) const = 0;
    virtual ~SExpr() = default;
    SExpr() = default;
    SExpr(const SExpr &SExpr) = default;
};

template <typename T> class Value : public SExpr<T> {
  public:
    explicit Value(T Val) : Val(std::move(Val)) {}
    void serialize(std::ostream &OS, size_t /*unused*/) const override {
        OS << Val;
    }
    T Val;
};

template <typename T> class Apply : public SExpr<T> {
  public:
    Apply(T Fun, std::vector<std::unique_ptr<const SExpr<T>>> Args)
        : Fun(std::move(Fun)), Args(std::move(Args)) {}
    void serialize(std::ostream &OS, size_t Indent) const override {
        OS << "(" << Fun;
        std::vector<std::string> AtomicOps = {
            "+", "-", "*", "<=", "<", ">", ">=", "=", "not", "distinct"};
        std::vector<std::string> ForceIndentOps = {"assert","and"};
        bool AtomicOp = std::find(AtomicOps.begin(), AtomicOps.end(), Fun) !=
                        AtomicOps.end();
        bool SimpleOp = Args.size() <= 1 &&
                        std::find(ForceIndentOps.begin(), ForceIndentOps.end(),
                                  Fun) == ForceIndentOps.end();
        bool Inv = Fun.substr(0, 3) == "INV";
        if (AtomicOp || SimpleOp || Inv) {
            for (auto &Arg : Args) {
                OS << " ";
                Arg->serialize(OS, Indent);
            }
        } else {
            for (auto &Arg : Args) {
                OS << std::endl;
                OS << std::string(Indent + 3, ' ');
                Arg->serialize(OS, Indent + 3);
            }
        }
        OS << ")";
    }
    T Fun;
    std::vector<std::unique_ptr<const SExpr<T>>> Args;
};

template <typename T> class List : public SExpr<T> {
  public:
    explicit List(std::vector<std::unique_ptr<const SExpr<T>>> Elements)
        : Elements(std::move(Elements)) {}
    void serialize(std::ostream &OS, size_t Indent) const override {
        OS << "(";
        auto It = Elements.begin();
        auto E = Elements.end();
        if (It != E) {
            (*It)->serialize(OS, Indent + 1);
            ++It;
            for (; It != E; ++It) {
                OS << std::endl;
                OS << std::string(Indent + 1, ' ');
                (*It)->serialize(OS, Indent + 1);
            }
        }
        OS << ")";
    }
    T Fun;
    std::vector<std::unique_ptr<const SExpr<T>>> Elements;
};

template <typename T> class Comment : public SExpr<T> {
public:
    explicit Comment(std::string Val) : Val(std::move(Val)) {}
    void serialize(std::ostream &OS, size_t /*unused*/) const override {
        OS << "; " << Val;
    }
    std::string Val;
};

template <typename T>
std::ostream &operator<<(std::ostream &OS, const SExpr<T> &Val) {
    Val.serialize(OS, 0);
    return OS;
}

} // namespace sexpr

#endif // SEXPR_H
