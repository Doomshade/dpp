use crate::parse::analysis::{
    BoundExpression, BoundFunction, BoundStatement, BoundTranslationUnit, BoundVariableAssignment,
};
use crate::parse::parser::{BinaryOperator, NumberType};
use crate::parse::Optimizer;
use std::fmt::Write;

impl Optimizer {
    pub fn optimize_translation_unit(
        &mut self,
        mut translation_unit: BoundTranslationUnit,
    ) -> BoundTranslationUnit {
        translation_unit.global_variable_assignments = translation_unit
            .global_variable_assignments
            .into_iter()
            .map(|assignment| self.optimize_assignment(assignment))
            .collect::<Vec<BoundVariableAssignment>>();
        translation_unit.functions = translation_unit
            .functions
            .into_iter()
            .map(|function| self.optimize_function(function))
            .collect::<Vec<BoundFunction>>();
        translation_unit
    }

    fn optimize_function(&mut self, mut function: BoundFunction) -> BoundFunction {
        function.statements = function
            .statements
            .into_iter()
            .map(|statement| self.optimize_statement(statement))
            .collect::<Vec<BoundStatement>>();
        function
    }

    fn optimize_statement(&mut self, mut statement: BoundStatement) -> BoundStatement {
        let statement_str = format!("{statement:?}");
        let optimized_statement = match statement {
            BoundStatement::If {
                expression,
                statement,
            } => {
                let optimized_expression = self.optimize_expression(expression);
                if let BoundExpression::Booba(value) = optimized_expression {
                    return if value {
                        self.optimize_statement(*statement)
                    } else {
                        BoundStatement::Empty
                    };
                }

                BoundStatement::If {
                    statement: Box::new(self.optimize_statement(*statement)),
                    expression: optimized_expression,
                }
            }
            BoundStatement::Expression(expression) => {
                if let BoundExpression::FunctionCall { .. } = expression {
                    BoundStatement::Expression(self.optimize_expression(expression))
                } else {
                    BoundStatement::Empty
                }
            }
            BoundStatement::VariableAssignment(variable_assignment) => {
                BoundStatement::VariableAssignment(self.optimize_assignment(variable_assignment))
            }
            BoundStatement::Statements(statements) => {
                if statements.is_empty() {
                    BoundStatement::Empty
                } else {
                    BoundStatement::Statements(statements)
                }
            }
            _ => statement,
        };
        let optimized_statement_str = format!("{optimized_statement:?}");
        if statement_str != optimized_statement_str {
            self.optimizations.push(format!(
                "[INFO] Optimized\n   {statement_str}\n-> {optimized_statement_str}"
            ));
        }

        optimized_statement
    }

    fn optimize_assignment(
        &mut self,
        mut assignment: BoundVariableAssignment,
    ) -> BoundVariableAssignment {
        assignment.value = self.optimize_expression(assignment.value);
        assignment
    }

    fn optimize_expression(&mut self, mut expression: BoundExpression) -> BoundExpression {
        let expression_str = format!("{expression:?}");
        let optimized_expression = match expression {
            BoundExpression::Binary { lhs, rhs, op } => {
                let optimized_lhs = self.optimize_expression(*lhs);
                let optimized_rhs = self.optimize_expression(*rhs);

                use BinaryOperator as BinOp;
                match &op {
                    BinOp::Add | BinOp::Subtract => {
                        // Adding/subtracting 0 makes no sense.
                        let lhs_zero = Self::is_zero(&optimized_lhs);
                        let rhs_zero = Self::is_zero(&optimized_rhs);

                        if rhs_zero {
                            optimized_lhs
                        } else if lhs_zero {
                            optimized_rhs
                        } else {
                            BoundExpression::Binary {
                                lhs: Box::new(optimized_lhs),
                                op,
                                rhs: Box::new(optimized_rhs),
                            }
                        }
                    }
                    BinOp::And => {
                        // Any false value -> both are false.
                        let lhs = Self::booba_value(&optimized_lhs);
                        let rhs = Self::booba_value(&optimized_rhs);

                        if let Some(lhs) = lhs {
                            if let Some(rhs) = rhs {
                                if lhs && rhs {
                                    return BoundExpression::Booba(true);
                                } else if !lhs || !rhs {
                                    return BoundExpression::Booba(false);
                                }
                            }
                        }

                        BoundExpression::Binary {
                            lhs: Box::new(optimized_lhs),
                            op,
                            rhs: Box::new(optimized_rhs),
                        }
                    }
                    BinOp::Or => {
                        // Any false value -> both are false.
                        let lhs = Self::booba_value(&optimized_lhs);
                        let rhs = Self::booba_value(&optimized_rhs);

                        if let Some(lhs) = lhs {
                            if let Some(rhs) = rhs {
                                if lhs || rhs {
                                    return BoundExpression::Booba(true);
                                } else if !lhs && !rhs {
                                    return BoundExpression::Booba(false);
                                }
                            }
                        }
                        BoundExpression::Binary {
                            lhs: Box::new(optimized_lhs),
                            op,
                            rhs: Box::new(optimized_rhs),
                        }
                    }
                    BinOp::Multiply => {
                        // Multiplying by 0 makes no sense.
                        let lhs_zero = match &optimized_lhs {
                            BoundExpression::Number { value, number_type } => *value == 0,
                            _ => false,
                        };

                        let rhs_zero = match &optimized_rhs {
                            BoundExpression::Number { value, number_type } => *value == 0,
                            _ => false,
                        };

                        if lhs_zero || rhs_zero {
                            BoundExpression::Number {
                                value: 0,
                                number_type: NumberType::Pp,
                            }
                        } else {
                            BoundExpression::Binary {
                                lhs: Box::new(optimized_lhs),
                                op,
                                rhs: Box::new(optimized_rhs),
                            }
                        }
                    }
                    _ => BoundExpression::Binary {
                        lhs: Box::new(optimized_lhs),
                        op,
                        rhs: Box::new(optimized_rhs),
                    },
                }
            }
            BoundExpression::Variable(variable_position) => {
                self.referenced_variables.insert(variable_position.clone());
                BoundExpression::Variable(variable_position)
            }
            _ => expression,
        };
        let optimized_expression_str = format!("{optimized_expression:?}");
        if expression_str != optimized_expression_str {
            self.optimizations.push(format!(
                "[INFO] Optimized\n   {expression_str}\n-> {optimized_expression_str}"
            ));
        }

        optimized_expression
    }

    fn is_zero(expression: &BoundExpression) -> bool {
        match expression {
            BoundExpression::Number { value, .. } => *value == 0,
            _ => false,
        }
    }

    fn booba_value(expression: &BoundExpression) -> Option<bool> {
        match expression {
            BoundExpression::Booba(value) => Some(*value),
            _ => None,
        }
    }
}
