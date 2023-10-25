use dpp_macros::PosMacro;

use crate::parse::analysis::SymbolTable;
use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::parser::{Block, DataType, Number, Statement, TranslationUnit, UnaryOperator};
use crate::parse::{Expression, Function, SemanticAnalyzer};

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn analyze(
        mut self,
        translation_unit: &TranslationUnit<'a>,
    ) -> Result<SymbolTable<'a>, SyntaxError> {
        // Analyze global statements.
        translation_unit.functions().iter().for_each(|function| {
            if self
                .symbol_table()
                .has_global_function(function.identifier())
            {
                self.error_diag.borrow_mut().function_already_exists(
                    function.row(),
                    function.col(),
                    function.identifier(),
                );
            }
            self.symbol_table_mut()
                .push_global_function(function.clone())
        });

        translation_unit
            .global_statements()
            .iter()
            .for_each(|statement| self.analyze_global_statement(statement));
        self.error_diag.borrow().check_errors()?;

        // Analyze the parsed functions.
        translation_unit
            .functions()
            .iter()
            .for_each(|function| self.analyze_function(function));

        if !self.symbol_table().find_function("main").is_some() {
            self.error_diag.borrow_mut().no_main_method_found_error();
        }
        self.error_diag.borrow().check_errors()?;
        Ok(self.symbol_table)
    }

    fn analyze_function(&mut self, function: &Function<'a>) {
        self.begin_function(&function);
        self.analyze_block(function.block());
        if function.return_type() != &DataType::Nopp {
            // If it's anything other than Nopp, then we require the function to have
            // a return statement at the very end.
            let last_statement = function.block().statements().last();
            if let Some(Statement::Bye { .. }) = last_statement {
                // Do nothing.
            } else {
                self.error_diag.borrow_mut().missing_return_statement(
                    function.block().position().0,
                    function.block().position().1,
                );
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self
                    .symbol_table()
                    .find_local_variable_in_scope_stack(
                        variable.identifier(),
                        self.current_function,
                    )
                    .is_some()
                {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.analyze_expr(expression);
                    self.check_data_type(variable.data_type(), &data_type, &variable.position());
                }
                self.symbol_table_mut()
                    .push_global_variable(variable.clone());
            }
            _ => {}
        }
    }

    fn analyze_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable } => {
                if self
                    .symbol_table()
                    .find_local_variable_in_scope_stack(
                        variable.identifier(),
                        self.current_function,
                    )
                    .is_some()
                {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.analyze_expr(expression);
                    self.check_data_type(variable.data_type(), &data_type, &variable.position());
                }
                self.symbol_table_mut()
                    .push_local_variable(variable.clone());
                // dbg!(&expression);
            }
            Statement::Expression { expression, .. } => {
                self.analyze_expr(expression);
            }
            Statement::While {
                expression,
                statement,
                ..
            } => {
                let data_type = self.analyze_expr(expression);
                self.check_data_type(
                    &DataType::Booba,
                    &data_type,
                    &(expression.row(), expression.col()),
                );
                self.loop_stack += 1;
                self.analyze_statement(statement);
                self.loop_stack -= 1;
            }
            Statement::Loop { block, .. } => {
                self.loop_stack += 1;
                block
                    .statements()
                    .iter()
                    .for_each(|statement| self.analyze_statement(statement));
                self.loop_stack -= 1;
            }
            Statement::DoWhile {
                expression,
                block,
                position,
            } => {
                let data_type = self.analyze_expr(expression);
                self.check_data_type(&DataType::Booba, &data_type, position);
                self.loop_stack += 1;
                block
                    .statements()
                    .iter()
                    .for_each(|statement| self.analyze_statement(statement));
                self.loop_stack -= 1;
            }
            Statement::Break { position } => {
                if self.loop_stack == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_break_placement(position.0, position.1);
                }
            }
            Statement::Block { block, .. } => {
                self.analyze_block(block);
            }
            Statement::Bye { .. } => {}
            Statement::If {
                expression,
                statement,
                position,
            } => {
                let data_type = self.analyze_expr(expression);

                self.check_data_type(&DataType::Booba, &data_type, position);
                self.analyze_statement(statement);
            }
            Statement::IfElse {
                expression,
                statement,
                position,
                else_statement,
            } => {
                let data_type = self.analyze_expr(expression);

                self.check_data_type(&DataType::Booba, &data_type, position);
                self.analyze_statement(statement);
                self.analyze_statement(else_statement);
            }
            Statement::Assignment {
                identifier,
                expression,
                position,
            } => {
                let variable = self
                    .symbol_table()
                    .find_variable_in_scope_stack(identifier, self.current_function)
                    .expect("A variable")
                    .data_type()
                    .clone();
                self.check_data_type(&variable, &self.analyze_expr(expression), position);
            }
            Statement::Empty { .. } => {
                // Nothing :)
            }
            Statement::Switch {
                expression, cases, ..
            } => {
                let switch_data_type = self.analyze_expr(expression);
                if let Some(mismatched_data_type) = cases
                    .iter()
                    .map(|case| {
                        (
                            case.block().position(),
                            self.analyze_expr(case.expression()),
                        )
                    })
                    .find(|(_, data_type)| *data_type != switch_data_type)
                {
                    self.check_data_type(
                        &switch_data_type,
                        &mismatched_data_type.1,
                        &mismatched_data_type.0,
                    );
                }
            }
            Statement::For {
                index_ident,
                ident_expression,
                length_expression,
                statement,
                position,
            } => {
                if self
                    .symbol_table()
                    .find_local_variable_in_scope_stack(index_ident, self.current_function)
                    .is_some()
                {
                    self.error_diag.borrow_mut().variable_already_exists(
                        position.0,
                        position.1,
                        index_ident,
                    );
                }
                if let Some(ident_expression) = ident_expression {
                    self.check_data_type(
                        &DataType::Number(Number::Pp),
                        &self.analyze_expr(ident_expression),
                        &(ident_expression.row(), ident_expression.col()),
                    );
                }
                self.check_data_type(
                    &DataType::Number(Number::Pp),
                    &self.analyze_expr(length_expression),
                    &(length_expression.row(), length_expression.col()),
                );
                self.analyze_statement(statement);
            }
            _ => {
                self.error_diag.borrow_mut().not_implemented(
                    statement.row(),
                    statement.col(),
                    format!("{:?}", statement).as_str(),
                );
            }
        };
    }

    fn analyze_block(&mut self, block: &Block<'a>) {
        self.symbol_table.push_scope();
        block
            .statements()
            .iter()
            .for_each(|statement| self.analyze_statement(statement));
        self.symbol_table.pop_scope();
    }

    fn analyze_expr(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::Number { number_type, .. } => DataType::Number(number_type.clone()),
            Expression::P { .. } => DataType::P,
            Expression::Booba { .. } => DataType::Booba,
            Expression::Yarn { .. } => DataType::Yarn,
            Expression::Unary { operand, op, .. } => {
                let data_type = self.analyze_expr(operand);
                return match op {
                    UnaryOperator::Not => match data_type {
                        DataType::Booba => data_type,
                        _ => panic!("Invalid type for unary operator"),
                    },
                    UnaryOperator::Negate => match data_type {
                        DataType::Number(..) => data_type,
                        _ => panic!("Invalid type for unary operator"),
                    },
                };
            }
            Expression::Binary {
                lhs,
                rhs,
                op,
                position,
            } => {
                let lhs_data_type = self.analyze_expr(lhs);
                let rhs_data_type = self.analyze_expr(rhs);

                self.check_if_mixed_data_types(&lhs_data_type, &rhs_data_type, &position);
                // TODO: Check whether the binary operator is available for the given data type.
                use crate::parse::parser::BinaryOperator::*;
                match op {
                    Add | Subtract | Multiply | Divide => lhs_data_type,
                    NotEqual | Equal | GreaterThan | GreaterThanOrEqual | LessThan
                    | LessThanOrEqual => DataType::Booba,
                }
            }
            Expression::Identifier {
                identifier,
                position,
            } => {
                return if let Some(variable) = self
                    .symbol_table()
                    .find_variable_in_scope_stack(identifier, self.current_function)
                {
                    if variable.is_initialized() {
                        variable.data_type().clone()
                    } else {
                        self.error_diag
                            .borrow_mut()
                            .variable_not_initialized(position.0, position.1, identifier);
                        DataType::Nopp
                    }
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(position.0, position.1, identifier);
                    DataType::Nopp
                }
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                position,
            } => {
                return if let Some(function) = self.symbol_table().find_function(identifier) {
                    if function.parameters().len() != arguments.len() {
                        // Check the argument count.
                        self.error_diag.borrow_mut().invalid_number_of_arguments(
                            position.0,
                            position.1,
                            identifier,
                            function.parameters().len(),
                            arguments.len(),
                        );
                    } else {
                        // Check the argument data type.
                        if let Some(mismatched_arg) = arguments
                            .iter()
                            .zip(function.parameters().iter().map(|var| var.data_type()))
                            .find(|(a, b)| &self.analyze_expr(a) != *b)
                        {
                            let got = self.analyze_expr(mismatched_arg.0);
                            self.error_diag.borrow_mut().invalid_data_type(
                                mismatched_arg.0.row(),
                                mismatched_arg.0.col(),
                                mismatched_arg.1,
                                &got,
                            )
                        }
                    }
                    function.return_type().clone()
                } else {
                    self.error_diag
                        .borrow_mut()
                        .function_does_not_exist(position.0, position.1);
                    DataType::Nopp
                };
            }
            _ => DataType::Nopp,
        };
    }
}
