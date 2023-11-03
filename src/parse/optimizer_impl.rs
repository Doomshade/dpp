use crate::parse::analysis::{
    BoundCase, BoundExpression, BoundFunction, BoundStatement, BoundTranslationUnit,
    BoundVariableAssignment,
};
use crate::parse::parser::{BinaryOperator};
use crate::parse::Optimizer;

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
                    // Any other expression statement is pointless.
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
                    BoundStatement::Statements(
                        statements
                            .into_iter()
                            .map(|statement| self.optimize_statement(statement))
                            .collect::<Vec<BoundStatement>>(),
                    )
                }
            }
            BoundStatement::Switch { expression, cases } => {
                let expression = self.optimize_expression(expression);
                let cases = self.optimize_cases(&expression, cases);
                BoundStatement::Switch { expression, cases }
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
                    BinOp::Add | BinOp::Subtract | BinOp::Multiply => {
                        // Adding/subtracting 0 makes no sense.
                        if let Some(lhs_zero) = Self::is_zero(&optimized_lhs) {
                            if lhs_zero {
                                return match &op {
                                    BinOp::Add | BinOp::Subtract => optimized_rhs,
                                    BinOp::Multiply => BoundExpression::Number {
                                        value: 0,
                                        number_type: NumberType::Pp,
                                    },
                                    _ => unreachable!(),
                                };
                            }
                        }

                        if let Some(rhs_zero) = Self::is_zero(&optimized_rhs) {
                            if rhs_zero {
                                return match &op {
                                    BinOp::Add | BinOp::Subtract => optimized_lhs,
                                    BinOp::Multiply => BoundExpression::Number {
                                        value: 0,
                                        number_type: NumberType::Pp,
                                    },
                                    _ => unreachable!(),
                                };
                            }
                        }
                        BoundExpression::Binary {
                            lhs: Box::new(optimized_lhs),
                            op,
                            rhs: Box::new(optimized_rhs),
                        }
                    }
                    BinOp::And
                    | BinOp::Or
                    | BinOp::Equal
                    | BinOp::NotEqual
                    | BinOp::GreaterThan
                    | BinOp::GreaterThanOrEqual
                    | BinOp::LessThan
                    | BinOp::LessThanOrEqual => {
                        if let Some(lhs) = Self::booba_value(&optimized_lhs) {
                            if let Some(rhs) = Self::booba_value(&optimized_rhs) {
                                return match &op {
                                    BinOp::And => BoundExpression::Booba(lhs && rhs),
                                    BinOp::Or => BoundExpression::Booba(lhs || rhs),
                                    BinOp::Equal => BoundExpression::Booba(lhs == rhs),
                                    BinOp::NotEqual => BoundExpression::Booba(lhs != rhs),
                                    _ => unreachable!(),
                                };
                            }
                        }

                        if let BoundExpression::Number {
                            number_type: lhs_number_type,
                            value: lhs_value,
                        } = &optimized_lhs
                        {
                            if let BoundExpression::Number {
                                number_type: rhs_number_type,
                                value: rhs_value,
                            } = &optimized_rhs
                            {
                                return match &op {
                                    BinOp::Equal => {
                                        BoundExpression::Booba(*lhs_value == *rhs_value)
                                    }
                                    BinOp::NotEqual => {
                                        BoundExpression::Booba(*lhs_value != *rhs_value)
                                    }
                                    BinOp::GreaterThan => {
                                        BoundExpression::Booba(*lhs_value > *rhs_value)
                                    }
                                    BinOp::GreaterThanOrEqual => {
                                        BoundExpression::Booba(*lhs_value >= *rhs_value)
                                    }
                                    BinOp::LessThan => {
                                        BoundExpression::Booba(*lhs_value < *rhs_value)
                                    }
                                    BinOp::LessThanOrEqual => {
                                        BoundExpression::Booba(*lhs_value <= *rhs_value)
                                    }
                                    _ => unreachable!(),
                                };
                            }
                        }

                        BoundExpression::Binary {
                            lhs: Box::new(optimized_lhs),
                            op,
                            rhs: Box::new(optimized_rhs),
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

    fn optimize_cases(
        &mut self,
        expression: &BoundExpression,
        mut cases: Vec<BoundCase>,
    ) -> Vec<BoundCase> {
        // Check if it's a constant.
        match expression {
            BoundExpression::Number { value, number_type } => {}
            BoundExpression::P(_) => {}
            BoundExpression::Booba(_) => {}
            BoundExpression::Yarn(_) => {}
            BoundExpression::Unary { .. } => {}
            BoundExpression::Binary { .. } => {}
            BoundExpression::Variable(_) => {}
            BoundExpression::FunctionCall { .. } => {}
        }
        vec![]
    }

    fn is_zero(expression: &BoundExpression) -> Option<bool> {
        match expression {
            BoundExpression::Number { value, .. } => Some(*value == 0),
            _ => None,
        }
    }

    fn booba_value(expression: &BoundExpression) -> Option<bool> {
        match expression {
            BoundExpression::Booba(value) => Some(*value),
            _ => None,
        }
    }
}
