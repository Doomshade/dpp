use crate::parse::analysis::{
    BoundCase, BoundExpression, BoundFunction, BoundLiteralValue, BoundStatement,
    BoundTranslationUnit, BoundVariableAssignment,
};
use crate::parse::parser::BinaryOperator;
use crate::parse::Optimizer;
use itertools::Itertools;

impl Optimizer {
    pub fn optimize_translation_unit(
        &mut self,
        mut translation_unit: BoundTranslationUnit,
    ) -> BoundTranslationUnit {
        translation_unit.global_variable_assignments = translation_unit
            .global_variable_assignments
            .into_iter()
            .map(|assignment| self.optimize_statement(assignment))
            .collect_vec();
        translation_unit.functions = translation_unit
            .functions
            .into_iter()
            .map(|function| self.optimize_function(function))
            .collect_vec();
        translation_unit
    }

    fn optimize_function(&mut self, mut function: BoundFunction) -> BoundFunction {
        function.statements = function
            .statements
            .into_iter()
            .map(|statement| self.optimize_statement_with_debug(statement))
            .collect_vec();
        function
    }

    fn optimize_statement_with_debug(&mut self, statement: BoundStatement) -> BoundStatement {
        let statement_str = format!("{statement:?}");
        let optimized_statement = self.optimize_statement(statement);
        let optimized_statement_str = format!("{optimized_statement:?}");
        if statement_str != optimized_statement_str {
            self.optimizations.push(format!(
                "statement\n   {statement_str}\n-> {optimized_statement_str}"
            ));
        }

        optimized_statement
    }

    fn optimize_statement(&mut self, statement: BoundStatement) -> BoundStatement {
        match statement {
            BoundStatement::If {
                expression,
                statement,
            } => {
                let optimized_expression = self.optimize_expression_with_debug(expression);
                if let BoundExpression::Literal(value) = &optimized_expression {
                    match value {
                        BoundLiteralValue::Booba(booba_value) => {
                            return if *booba_value {
                                self.optimize_statement(*statement)
                            } else {
                                BoundStatement::Empty
                            };
                        }
                        _ => {}
                    }
                }

                BoundStatement::If {
                    statement: Box::new(self.optimize_statement(*statement)),
                    expression: optimized_expression,
                }
            }
            BoundStatement::Expression(expression) => {
                if let BoundExpression::FunctionCall { .. } = expression {
                    BoundStatement::Expression(self.optimize_expression_with_debug(expression))
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
                            .collect_vec(),
                    )
                }
            }
            BoundStatement::Switch { expression, cases } => {
                let expression = self.optimize_expression_with_debug(expression);
                let cases = self.optimize_cases(&expression, cases);
                // If after optimizations we have only one case we just return an if to that.
                if cases.len() == 1 {
                    let case = cases.into_iter().next().unwrap();
                    return BoundStatement::If {
                        expression: BoundExpression::Binary {
                            lhs: Box::new(expression),
                            op: BinaryOperator::Equal,
                            rhs: Box::new(case.expression),
                        },
                        statement: Box::new(BoundStatement::Statements(case.statements)),
                    };
                }
                BoundStatement::Switch { expression, cases }
            }
            BoundStatement::For {
                ident_expression,
                ident_position,
                length_expression,
                statement,
            } => {
                let statement = self.optimize_statement(*statement);
                // Check if there's any statement at all.
                if let BoundStatement::Empty = statement {
                    return BoundStatement::Empty;
                }
                let ident_expression =
                    ident_expression.map(|expr| self.optimize_expression_with_debug(expr));
                let length_expression = self.optimize_expression_with_debug(length_expression);

                BoundStatement::For {
                    ident_expression,
                    ident_position,
                    length_expression,
                    statement: Box::new(statement),
                }
            }
            _ => statement,
        }
    }

    fn optimize_assignment(
        &mut self,
        mut assignment: BoundVariableAssignment,
    ) -> BoundVariableAssignment {
        assignment.value = self.optimize_expression_with_debug(assignment.value);
        assignment
    }

    fn optimize_expression_with_debug(&mut self, expression: BoundExpression) -> BoundExpression {
        let expression_str = format!("{expression:?}");
        let optimized_expression = self.optimize_expression(expression);
        let optimized_expression_str = format!("{optimized_expression:?}");
        if expression_str != optimized_expression_str {
            self.optimizations.push(format!(
                "expression\n   {expression_str}\n-> {optimized_expression_str}"
            ));
        }
        optimized_expression
    }

    fn remove_zeroes(expression: &BoundExpression, op: &BinaryOperator) -> Option<BoundExpression> {
        if let Some(is_zero) = match expression {
            BoundExpression::Literal(value) => match value {
                BoundLiteralValue::Pp(value) => Some(*value == 0),
                BoundLiteralValue::Flaccid(a, b) => Some(*a == 0 && *b == 0),
                _ => None,
            },
            _ => None,
        } {
            if is_zero {
                return match op {
                    BinaryOperator::Multiply => {
                        Some(BoundExpression::Literal(BoundLiteralValue::Pp(0)))
                    }
                    BinaryOperator::Divide => {
                        eprintln!("Division by 0 detected :(");
                        Some(BoundExpression::Literal(BoundLiteralValue::Pp(0)))
                    }
                    _ => None,
                };
            }
        }
        None
    }

    fn join_constant_values(
        lhs: &BoundExpression,
        op: &BinaryOperator,
        rhs: &BoundExpression,
    ) -> Option<BoundExpression> {
        if let BoundExpression::Literal(lhs) = &lhs {
            if let BoundExpression::Literal(rhs) = &rhs {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                return match op {
                    BinaryOperator::Add => Some(BoundExpression::Literal(lhs + rhs)),
                    BinaryOperator::Subtract => Some(BoundExpression::Literal(lhs - rhs)),
                    BinaryOperator::Multiply => Some(BoundExpression::Literal(lhs * rhs)),
                    BinaryOperator::Divide => Some(BoundExpression::Literal(lhs / rhs)),
                    _ => None,
                };
            }
        }
        None
    }

    fn optimize_expression(&mut self, expression: BoundExpression) -> BoundExpression {
        match expression {
            BoundExpression::Binary { lhs, rhs, op } => {
                let optimized_lhs = self.optimize_expression(*lhs);
                let optimized_rhs = self.optimize_expression(*rhs);

                use BinaryOperator as BinOp;
                match &op {
                    BinOp::Add | BinOp::Subtract | BinOp::Multiply | BinOp::Divide => {
                        // Adding/subtracting 0 makes no sense.
                        if let Some(no_zeroes_expression) = Self::remove_zeroes(&optimized_lhs, &op)
                        {
                            return no_zeroes_expression;
                        }

                        if let Some(no_zeroes_expression) = Self::remove_zeroes(&optimized_rhs, &op)
                        {
                            return no_zeroes_expression;
                        }

                        if let Some(value) =
                            Self::join_constant_values(&optimized_lhs, &op, &optimized_rhs)
                        {
                            return value;
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
                                    BinOp::And => BoundExpression::Literal(
                                        BoundLiteralValue::Booba(lhs && rhs),
                                    ),
                                    BinOp::Or => BoundExpression::Literal(
                                        BoundLiteralValue::Booba(lhs || rhs),
                                    ),
                                    BinOp::Equal => BoundExpression::Literal(
                                        BoundLiteralValue::Booba(lhs == rhs),
                                    ),
                                    BinOp::NotEqual => BoundExpression::Literal(
                                        BoundLiteralValue::Booba(lhs != rhs),
                                    ),
                                    _ => unreachable!(),
                                };
                            }
                        }

                        if let BoundExpression::Literal(lhs_value) = &optimized_lhs {
                            if let BoundLiteralValue::Pp(lhs_value) = lhs_value {
                                if let BoundExpression::Literal(rhs_value) = &optimized_rhs {
                                    if let BoundLiteralValue::Pp(rhs_value) = rhs_value {
                                        return match &op {
                                            BinOp::Equal => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value == *rhs_value),
                                            ),
                                            BinOp::NotEqual => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value != *rhs_value),
                                            ),
                                            BinOp::GreaterThan => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value > *rhs_value),
                                            ),
                                            BinOp::GreaterThanOrEqual => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value >= *rhs_value),
                                            ),
                                            BinOp::LessThan => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value < *rhs_value),
                                            ),
                                            BinOp::LessThanOrEqual => BoundExpression::Literal(
                                                BoundLiteralValue::Booba(*lhs_value <= *rhs_value),
                                            ),
                                            _ => unreachable!(),
                                        };
                                    }
                                }
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
            BoundExpression::VariableDeclaration(variable_position) => {
                self.referenced_variables.insert(variable_position.clone());
                BoundExpression::VariableDeclaration(variable_position)
            }
            _ => expression,
        }
    }

    fn optimize_cases(
        &mut self,
        expression: &BoundExpression,
        mut cases: Vec<BoundCase>,
    ) -> Vec<BoundCase> {
        let mut expressions = Vec::new();
        cases = cases
            .into_iter()
            .map(|case| {
                BoundCase::new(
                    self.optimize_expression_with_debug(case.expression),
                    self.optimize_statements(case.statements),
                )
            })
            .filter(|case| {
                return if !expressions.contains(case.expression()) {
                    expressions.push(case.expression().clone());
                    true
                } else {
                    false
                };
            })
            .collect_vec();

        // Check if the switch is a constant and just make it an if statement.
        match expression {
            BoundExpression::Literal(value) => {
                if let Some(case) = cases.iter().find(|case| match case.expression() {
                    BoundExpression::Literal(case_value) => value == case_value,
                    _ => false,
                }) {
                    return vec![case.clone()];
                }
                cases
            }
            _ => cases,
        }
    }

    fn optimize_statements(&mut self, statements: Vec<BoundStatement>) -> Vec<BoundStatement> {
        statements
            .into_iter()
            .map(|statement| self.optimize_statement(statement))
            .collect_vec()
    }

    fn booba_value(expression: &BoundExpression) -> Option<bool> {
        match expression {
            BoundExpression::Literal(value) => match value {
                BoundLiteralValue::Booba(value) => Some(*value),
                _ => None,
            },
            _ => None,
        }
    }
}
