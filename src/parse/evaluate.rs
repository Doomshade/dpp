use std::marker::PhantomData;

use crate::parse::parser::{DataType, Expression, UnaryOperator};

pub struct Evaluator<'a> {
    pub none: PhantomData<&'a ()>,
}

#[derive(Clone, Debug)]
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
    pub fn eval(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::PpExpression { .. } => DataType::Pp,
            Expression::PpExpression { .. } => DataType::P,
            Expression::BoobaExpression { .. } => DataType::Booba,
            Expression::YarnExpression { .. } => DataType::Yarn,
            Expression::UnaryExpression { operand, op, .. } => {
                let data_type = self.eval(operand);
                return match op {
                    UnaryOperator::Not => match data_type {
                        DataType::Booba => data_type,
                        _ => panic!("Invalid type for unary operator"),
                    },
                    UnaryOperator::Negate => match data_type {
                        DataType::Xxlpp | DataType::Pp | DataType::Spp | DataType::Xspp => {
                            data_type
                        }
                        _ => panic!("Invalid type for unary operator"),
                    },
                };
            }
            Expression::BinaryExpression { lhs, rhs, op, .. } => {
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);
                assert_eq!(
                    lhs_data_type, rhs_data_type,
                    "Invalid types for binary operator"
                );
                lhs_data_type
            }
            _ => DataType::Nopp,
        };
    }
}
