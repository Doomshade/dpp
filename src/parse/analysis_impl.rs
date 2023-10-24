use dpp_macros::PosMacro;

use crate::parse::analysis::SymbolTable;
use crate::parse::parser::{Block, DataType, TranslationUnit};
use crate::parse::{Expression, Function, Number, SemanticAnalyzer, Statement, UnaryOperator};

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn analyze(&mut self, translation_unit: &TranslationUnit<'a>) {
        // Analyze global statements.
        translation_unit
            .global_statements()
            .iter()
            .for_each(|statement| self.analyze_global_statement(statement));

        // Analyze the parsed functions.
        translation_unit
            .functions()
            .iter()
            .for_each(|function| self.analyze_function(function));

        if !self.symbol_table().find_function("main").is_some() {
            self.error_diag.borrow_mut().no_main_method_found_error();
        }
    }

    pub fn into_symbol_table(self) -> SymbolTable<'a> {
        self.symbol_table
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
                    .find_local_variable(variable.identifier(), self.current_function)
                    .is_some()
                {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.eval(expression);
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
                    .find_local_variable(variable.identifier(), self.current_function)
                    .is_some()
                {
                    self.error_diag.borrow_mut().variable_already_exists(
                        variable.position().0,
                        variable.position().1,
                        variable.identifier(),
                    );
                }

                if let Some(expression) = variable.value() {
                    let data_type = self.eval(expression);
                    self.check_data_type(variable.data_type(), &data_type, &variable.position());
                }
                self.symbol_table_mut()
                    .push_local_variable(variable.clone());
                // dbg!(&expression);
            }
            Statement::Expression { expression, .. } => {
                self.eval(expression);
            }
            Statement::While {
                expression,
                statement,
                position,
            } => {
                let data_type = self.eval(expression);
                self.check_data_type(
                    &DataType::Booba,
                    &data_type,
                    &(expression.row(), expression.col()),
                );
                self.loop_stack += 1;
                self.analyze_statement(statement);
                self.loop_stack -= 1;
            }
            Statement::Loop { block, position } => {
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
                let data_type = self.eval(expression);
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
                let data_type = self.eval(expression);

                self.check_data_type(&DataType::Booba, &data_type, position);
                self.analyze_statement(statement);
            }
            Statement::IfElse {
                expression,
                statement,
                position,
                else_statement,
            } => {
                let data_type = self.eval(expression);

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
                    .find_variable(identifier, self.current_function)
                    .expect("A variable")
                    .data_type()
                    .clone();
                self.check_data_type(&variable, &self.eval(expression), position);
            }
            Statement::Empty { .. } => {
                // Nothing :)
            }
            Statement::Switch {
                expression,
                cases,
                position,
            } => {
                let switch_data_type = self.eval(expression);
                if let Some(mismatched_data_type) = cases
                    .iter()
                    .map(|case| (case.block().position(), self.eval(case.expression())))
                    .find(|(position, data_type)| *data_type != switch_data_type)
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
                    .find_local_variable(index_ident, self.current_function)
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
                        &self.eval(ident_expression),
                        &(ident_expression.row(), ident_expression.col()),
                    );
                }
            }
            _ => {
                self.error_diag
                    .borrow_mut()
                    .not_implemented(format!("{:?}", statement).as_str());
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

    fn check_if_mixed_data_types(
        &self,
        expected_data_type: &DataType<'a>,
        got: &DataType<'a>,
        position: &(u32, u32),
    ) {
        if expected_data_type != got {
            self.error_diag.borrow_mut().mixed_data_types_error(
                position.0,
                position.1,
                expected_data_type,
                got,
            )
        }
    }

    fn check_data_type(
        &self,
        expected_data_type: &DataType<'a>,
        got: &DataType<'a>,
        position: &(u32, u32),
    ) {
        if expected_data_type != got {
            self.error_diag.borrow_mut().invalid_data_type(
                position.0,
                position.1,
                expected_data_type,
                got,
            )
        }
    }

    pub fn eval(&self, expr: &Expression<'a>) -> DataType<'a> {
        return match expr {
            Expression::Number { number_type, .. } => DataType::Number(number_type.clone()),
            Expression::P { .. } => DataType::P,
            Expression::Booba { .. } => DataType::Booba,
            Expression::Yarn { .. } => DataType::Yarn,
            Expression::Unary { operand, op, .. } => {
                let data_type = self.eval(operand);
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
                let lhs_data_type = self.eval(lhs);
                let rhs_data_type = self.eval(rhs);

                self.check_if_mixed_data_types(&lhs_data_type, &rhs_data_type, &position);
                // TODO: Check whether the binary operator is available for the given data type.
                use crate::parse::BinaryOperator::*;
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
                    .find_variable(identifier, self.current_function)
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
                            .find(|(a, b)| &self.eval(a) != *b)
                        {
                            let got = self.eval(mismatched_arg.0);
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

    fn begin_function(&mut self, function: &Function<'a>) {
        self.loop_stack = 0;
        self.current_function = Some(function.identifier());
        let mut ref_mut = self.symbol_table_mut();
        ref_mut.push_function(function.clone());
        ref_mut.push_scope();
        function
            .parameters()
            .iter()
            .for_each(|parameter| ref_mut.push_local_variable(parameter.clone()));
    }

    fn end_function(&mut self) {
        self.current_function = None;
        self.symbol_table_mut().pop_scope();
    }
}
