use std::marker::PhantomData;

use crate::parse::parser::{DataType, Expression, UnaryOperator};

pub struct Evaluator<'a> {
    pub none: PhantomData<&'a ()>,
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
                assert_eq!(lhs_data_type, rhs_data_type, "Data types do not match");
                // TODO: Check whether the binary operator is available for the given data type.
                lhs_data_type
            }
            _ => DataType::Nopp,
        };
    }
}
