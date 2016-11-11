/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include <algorithm>
#include <memory>
#include <ostream>
#include <set>
#include <vector>

#include <llvm/ADT/StringSet.h>

namespace sexpr {

class SExpr;
using SExprRef = std::unique_ptr<const sexpr::SExpr>;

class SExpr {
  public:
    virtual void serialize(std::ostream &os, size_t indent,
                           bool pretty) const = 0;
    virtual ~SExpr() = default;
    SExpr() = default;
    SExpr(const SExpr &sExpr) = default;
};

class Value : public SExpr {
  public:
    std::string val;
    explicit Value(std::string val) : val(std::move(val)) {}
    void serialize(std::ostream &os, size_t /*unused*/,
                   bool /* unused */) const override;
};

using SExprVec = llvm::SmallVector<SExprRef, 3>;
class Apply : public SExpr {
  public:
    std::string fun;
    SExprVec args;
    const static llvm::StringSet<> atomicOps;
    const static llvm::StringSet<> forceIndentOps;
    Apply(std::string fun, SExprVec args)
        : fun(std::move(fun)), args(std::move(args)) {}
    void serialize(std::ostream &os, size_t indent, bool pretty) const override;
};

class List : public SExpr {
  public:
    explicit List(SExprVec elements) : elements(std::move(elements)) {}
    void serialize(std::ostream &os, size_t indent, bool pretty) const override;
    std::string fun;
    SExprVec elements;
};

class Comment : public SExpr {
  public:
    explicit Comment(std::string val) : val(std::move(val)) {}
    void serialize(std::ostream &os, size_t /*unused*/,
                   bool /* unused */) const override;
    std::string val;
};

std::ostream &operator<<(std::ostream &os, const SExpr &val);
} // namespace sexpr

sexpr::SExprRef sexprFromString(std::string value);
