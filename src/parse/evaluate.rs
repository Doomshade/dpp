use crate::parse::parser::{BinaryOperator, Expression, Statement, UnaryOperator};
use std::marker::PhantomData;

pub struct Evaluator<'a> {
    pub none: PhantomData<&'a ()>,
}

#[derive(Debug)]
pub enum BoundExpression<'a> {
    PpValue(i32),
    BoobaValue(bool),
    YarnValue(String),
    IdentifierValue(&'a str),
    EmptyValue,
}

#[derive(Debug)]
pub enum BoundVariable<'a> {
    PpVariable(i32),
    BoobaVariable(bool),
    YarnVariable(&'a str),
}

#[derive(Debug)]
pub enum BoundFunctionCall<'a> {
    PpFunctionCall(i32),
    BoobaFunctionCall(bool),
    YarnFunctionCall(&'a str),
}

impl<'a> Evaluator<'a> {
    pub fn evaluate(&self, statement: &Statement) {
        let value = match statement {
            Statement::VariableDeclarationAndAssignment { expression, .. } => {
                self.evaluate_expr(expression)
            }
            Statement::PprintStatement { expression, .. } => {
                if let BoundExpression::YarnValue(yarn_expr) = self.evaluate_expr(expression) {
                    print!("{yarn_expr}");
                    BoundExpression::EmptyValue
                } else {
                    panic!("Invalid type for pprint statement")
                }
            }
            _ => todo!("Not yet implemented"),
        };
        println!("Evaluated: {value:?}");
    }

    // TODO: Rewrite this
    #[must_use]
    pub fn evaluate_expr(&self, expr: &Expression<'a>) -> BoundExpression<'a> {
        match expr {
            Expression::PpExpression { pp, .. } => BoundExpression::PpValue(*pp),
            Expression::BoobaExpression { booba, .. } => BoundExpression::BoobaValue(*booba),
            Expression::YarnExpression { yarn, .. } => {
                BoundExpression::YarnValue(String::from(*yarn))
            }
            Expression::UnaryExpression { operand, op, .. } => {
                let expr_value = self.evaluate_expr(operand);
                match op {
                    UnaryOperator::Not => {
                        if let BoundExpression::BoobaValue(booba) = expr_value {
                            BoundExpression::BoobaValue(!booba)
                        } else {
                            panic!("Invalid type for unary operator")
                        }
                    }
                    UnaryOperator::Negate => {
                        if let BoundExpression::PpValue(pp) = expr_value {
                            BoundExpression::PpValue(-pp)
                        } else {
                            panic!("Invalid type for unary operator")
                        }
                    }
                }
            }
            Expression::BinaryExpression { lhs, rhs, op, .. } => {
                let lhs_value = self.evaluate_expr(lhs);
                let rhs_value = self.evaluate_expr(rhs);
                match op {
                    BinaryOperator::Add => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::PpValue(lhs_pp + rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else if let BoundExpression::YarnValue(lhs_yarn) = lhs_value {
                            if let BoundExpression::YarnValue(rhs_yarn) = rhs_value {
                                BoundExpression::YarnValue(lhs_yarn + &rhs_yarn)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::Subtract => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::PpValue(lhs_pp - rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::Multiply => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::PpValue(lhs_pp * rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::Divide => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::PpValue(lhs_pp / rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::NotEqual => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp != rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else if let BoundExpression::BoobaValue(lhs_booba) = lhs_value {
                            if let BoundExpression::BoobaValue(rhs_booba) = rhs_value {
                                BoundExpression::BoobaValue(lhs_booba != rhs_booba)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::Equal => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp == rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else if let BoundExpression::BoobaValue(lhs_booba) = lhs_value {
                            if let BoundExpression::BoobaValue(rhs_booba) = rhs_value {
                                BoundExpression::BoobaValue(lhs_booba == rhs_booba)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::GreaterThan => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp > rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::GreaterThanOrEqual => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp >= rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::LessThan => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp < rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                    BinaryOperator::LessThanOrEqual => {
                        if let BoundExpression::PpValue(lhs_pp) = lhs_value {
                            if let BoundExpression::PpValue(rhs_pp) = rhs_value {
                                BoundExpression::BoobaValue(lhs_pp <= rhs_pp)
                            } else {
                                panic!("Invalid type for binary operator")
                            }
                        } else {
                            panic!("Invalid type for binary operator")
                        }
                    }
                }
            }
            Expression::IdentifierExpression { identifier, .. } => {
                BoundExpression::IdentifierValue(identifier.clone())
            }
            Expression::FunctionCall { .. } => {
                todo!("Implement function calls")
            }
            Expression::AssignmentExpression { expression, .. } => {
                // TODO: Assign the value.
                self.evaluate_expr(expression)
            }
            Expression::InvalidExpression => {
                panic!("Invalid expression")
            }
        }
    }
}
