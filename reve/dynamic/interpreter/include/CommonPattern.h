#pragma once

namespace commonpattern {
// a = b
const std::shared_ptr<const pattern::Expr> eqPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq, std::make_shared<pattern::Value>(
                                    pattern::Placeholder::Variable),
        std::make_shared<pattern::Value>(
            pattern::Placeholder::Variable));

// a + b = c
const std::shared_ptr<const pattern::Expr> additionPat =
    std::make_shared<pattern::BinaryOp>(
        pattern::Operation::Eq, std::make_shared<pattern::BinaryOp>(
                                    pattern::Operation::Add,
                                    std::make_shared<pattern::Value>(
                                        pattern::Placeholder::Variable),
                                    std::make_shared<pattern::Value>(
                                        pattern::Placeholder::Variable)),
        std::make_shared<pattern::Value>(
            pattern::Placeholder::Variable));
}
