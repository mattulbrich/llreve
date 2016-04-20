#pragma once

namespace commonpattern {
// A = B
const std::shared_ptr<const pattern::Expr> eqPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq,
        std::make_shared<pattern::Value>(pattern::Placeholder::Variable),
        std::make_shared<pattern::Value>(pattern::Placeholder::Variable));

// A + B = C
const std::shared_ptr<const pattern::Expr> additionPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq,
        std::make_shared<pattern::BinaryOp>(
            pattern::Operation::Add,
            std::make_shared<pattern::Value>(pattern::Placeholder::Variable),
            std::make_shared<pattern::Value>(pattern::Placeholder::Variable)),
        std::make_shared<pattern::Value>(pattern::Placeholder::Variable));

// A + b = C
const std::shared_ptr<const pattern::Expr> constantAdditionPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq,
        std::make_shared<pattern::BinaryOp>(
            pattern::Operation::Add,
            std::make_shared<pattern::Value>(pattern::Placeholder::Variable),
            std::make_shared<pattern::Value>(pattern::Placeholder::Constant)),
        std::make_shared<pattern::Value>(pattern::Placeholder::Variable));

// A + (b * C) = D
const std::shared_ptr<const pattern::Expr> linearEqPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq,
        std::make_shared<pattern::BinaryOp>(
            pattern::Operation::Add,
            std::make_shared<pattern::Value>(pattern::Placeholder::Variable),
            std::make_shared<pattern::BinaryOp>(
                pattern::Operation::Mul, std::make_shared<pattern::Value>(
                                             pattern::Placeholder::Constant),
                std::make_shared<pattern::Value>(
                    pattern::Placeholder::Variable))),
        std::make_shared<pattern::Value>(pattern::Placeholder::Variable));
}
