use crate::parse::analysis::{
    BoundExpression, BoundFunction, BoundStatement, BoundTranslationUnit, BoundVariableAssignment,
};
use crate::parse::parser::{BinaryOperator, NumberType};
use crate::parse::Optimizer;

impl Optimizer {
    pub fn optimize_translation_unit(
        mut self,
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
        match statement {
            BoundStatement::If {
                expression,
                statement,
            } => {
                let optimized_expression = self.optimize_expression(expression);
                let optimized_statement = self.optimize_statement(*statement);
                if let BoundExpression::Booba(value) = optimized_expression {
                    return if value {
                        optimized_statement
                    } else {
                        BoundStatement::Empty
                    };
                }
                BoundStatement::If {
                    statement: Box::new(optimized_statement),
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
        }
    }

    fn optimize_assignment(
        &mut self,
        mut assignment: BoundVariableAssignment,
    ) -> BoundVariableAssignment {
        assignment.value = self.optimize_expression(assignment.value);
        assignment
    }

    fn optimize_expression(&mut self, mut expression: BoundExpression) -> BoundExpression {
        match expression {
            BoundExpression::Binary { lhs, rhs, op } => {
                let opt_lhs = self.optimize_expression(*lhs);
                let opt_rhs = self.optimize_expression(*rhs);

                use BinaryOperator as BinOp;
                match &op {
                    BinOp::Add | BinOp::Subtract => {
                        // Adding/subtracting 0 makes no sense.
                        let lhs_zero = match &opt_lhs {
                            BoundExpression::Number { value, number_type } => *value == 0,
                            _ => false,
                        };

                        let rhs_zero = match &opt_rhs {
                            BoundExpression::Number { value, number_type } => *value == 0,
                            _ => false,
                        };
                        if rhs_zero {
                            opt_lhs
                        } else if lhs_zero {
                            opt_rhs
                        } else {
                            BoundExpression::Binary {
                                lhs: Box::new(opt_lhs),
                                op,
                                rhs: Box::new(opt_rhs),
                            }
                        }
                    }
                    BinOp::And => {
                        // Any false value -> both are false.
                        let lhs = match &opt_lhs {
                            BoundExpression::Booba(value) => Some(*value),
                            _ => None,
                        };

                        let rhs = match &opt_rhs {
                            BoundExpression::Booba(value) => Some(*value),
                            _ => None,
                        };

                        if let Some(lhs) = lhs {
                            if let Some(rhs) = rhs {
                                if !lhs || !rhs {
                                    return BoundExpression::Booba(false);
                                } else if lhs && rhs {
                                    return BoundExpression::Booba(true);
                                }
                            }
                        }

                        BoundExpression::Binary {
                            lhs: Box::new(opt_lhs),
                            op,
                            rhs: Box::new(opt_rhs),
                        }
                    }
                    BinOp::Or => {
                        // Any false value -> both are false.
                        let lhs_true = match &opt_lhs {
                            BoundExpression::Booba(value) => *value == true,
                            _ => false,
                        };

                        let rhs_true = match &opt_rhs {
                            BoundExpression::Booba(value) => *value == true,
                            _ => false,
                        };
                        if lhs_true || rhs_true {
                            BoundExpression::Booba(true)
                        } else {
                            BoundExpression::Binary {
                                lhs: Box::new(opt_lhs),
                                op,
                                rhs: Box::new(opt_rhs),
                            }
                        }
                    }
                    BinOp::Multiply => {
                        // Multiplying by 0 makes no sense.
                        let lhs_zero = match &opt_lhs {
                            BoundExpression::Number { value, number_type } => *value == 0,
                            _ => false,
                        };

                        let rhs_zero = match &opt_rhs {
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
                                lhs: Box::new(opt_lhs),
                                op,
                                rhs: Box::new(opt_rhs),
                            }
                        }
                    }
                    _ => BoundExpression::Binary {
                        lhs: Box::new(opt_lhs),
                        op,
                        rhs: Box::new(opt_rhs),
                    },
                }
            }
            BoundExpression::Variable(variable_position) => {
                self.referenced_variables.insert(variable_position.clone());
                BoundExpression::Variable(variable_position)
            }
            _ => expression,
        }
    }
}
