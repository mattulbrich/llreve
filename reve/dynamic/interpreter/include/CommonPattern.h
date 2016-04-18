#pragma once

namespace commonpattern {
// a = b
const std::shared_ptr<const pattern::Expr<VarIntVal>> eqPat =
    std::make_shared<pattern::BinaryOp<VarIntVal>>(
        pattern::Operation::Eq, std::make_shared<pattern::Value<VarIntVal>>(
                                    pattern::Placeholder::Variable),
        std::make_shared<pattern::Value<VarIntVal>>(
            pattern::Placeholder::Variable));

// a + b = c
const std::shared_ptr<const pattern::Expr<VarIntVal>> additionPat =
    std::make_shared<pattern::BinaryOp<VarIntVal>>(
        pattern::Operation::Eq, std::make_shared<pattern::BinaryOp<VarIntVal>>(
                                    pattern::Operation::Add,
                                    std::make_shared<pattern::Value<VarIntVal>>(
                                        pattern::Placeholder::Variable),
                                    std::make_shared<pattern::Value<VarIntVal>>(
                                        pattern::Placeholder::Variable)),
        std::make_shared<pattern::Value<VarIntVal>>(
            pattern::Placeholder::Variable));
}
