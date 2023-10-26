use dpp_macros::Pos;

use crate::parse::analysis::SymbolTable;
use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::parser::{
    Block, DataType, NumberType, Statement, TranslationUnit, UnaryOperator, Variable,
};
use crate::parse::{Expression, Function, SemanticAnalyzer};

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    pub fn analyze(
        mut self,
        translation_unit: &TranslationUnit<'a>,
    ) -> Result<SymbolTable<'a>, SyntaxError> {
        // Register the global functions.
        translation_unit.functions().iter().for_each(|function| {
            if self
                .symbol_table()
                .has_global_function(function.identifier())
            {
                self.error_diag
                    .borrow_mut()
                    .function_already_exists(function.position(), function.identifier());
            }
            self.symbol_table_mut()
                .push_global_function(function.clone())
        });

        // Analyze global statements.
        translation_unit
            .global_statements()
            .iter()
            .for_each(|statement| {
                self.analyze_global_statement(statement);
            });
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
                self.error_diag
                    .borrow_mut()
                    .missing_return_statement(function.block().position());
            }
        }
        self.end_function();
    }

    fn analyze_global_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable, .. } => {
                if self
                    .symbol_table()
                    .find_global_variable(variable.identifier())
                    .is_some()
                {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }

                if let Some(expression) = variable.value() {
                    self.check_data_type(
                        variable.data_type(),
                        self.analyze_expr(expression),
                        variable.position(),
                    );
                }
                self.symbol_table_mut()
                    .push_global_variable(variable.clone());
            }
            _ => {}
        };
    }

    fn analyze_statement(&mut self, statement: &Statement<'a>) {
        match &statement {
            Statement::VariableDeclaration { variable, .. } => {
                if self
                    .symbol_table()
                    .find_local_variable_in_scope_stack(
                        variable.identifier(),
                        self.current_function,
                    )
                    .is_some()
                {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }

                if let Some(expression) = variable.value() {
                    self.check_data_type(
                        variable.data_type(),
                        self.analyze_expr(expression),
                        variable.position(),
                    );
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
                self.check_data_type(&DataType::Booba, data_type, expression.position());
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
                self.check_data_type(&DataType::Booba, data_type, *position);
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
                        .invalid_break_placement(*position);
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

                self.check_data_type(&DataType::Booba, data_type, *position);
                self.analyze_statement(statement);
            }
            Statement::IfElse {
                expression,
                statement,
                position,
                else_statement,
            } => {
                let data_type = self.analyze_expr(expression);

                self.check_data_type(&DataType::Booba, data_type, *position);
                self.analyze_statement(statement);
                self.analyze_statement(else_statement);
            }
            Statement::Assignment {
                identifier,
                expression,
                position,
            } => {
                if let Some(variable) = self
                    .symbol_table()
                    .find_variable_in_scope_stack(identifier, self.current_function)
                {
                    self.check_data_type(
                        variable.data_type(),
                        self.analyze_expr(expression),
                        *position,
                    );
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);
                }
            }
            Statement::Empty { .. } => {
                // Nothing :)
            }
            Statement::Switch {
                expression, cases, ..
            } => {
                if let Some(switch_data_type) = self.analyze_expr(expression) {
                    if let Some(mismatched_data_type) = cases
                        .iter()
                        .map(|case| {
                            (
                                case.block().position(),
                                self.analyze_expr(case.expression()),
                            )
                        })
                        .find(|(_, data_type)| {
                            if let Some(data_type) = data_type {
                                data_type != &switch_data_type
                            } else {
                                false
                            }
                        })
                    {
                        self.check_data_type(
                            &switch_data_type,
                            mismatched_data_type.1,
                            mismatched_data_type.0,
                        );
                    }
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
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(*position, index_ident);
                }
                if let Some(ident_expression) = ident_expression {
                    self.check_data_type(
                        &DataType::Number(NumberType::Pp),
                        self.analyze_expr(ident_expression),
                        ident_expression.position(),
                    );
                }
                self.check_data_type(
                    &DataType::Number(NumberType::Pp),
                    self.analyze_expr(length_expression),
                    length_expression.position(),
                );

                self.symbol_table_mut().push_scope();
                let variable = Variable::new(
                    *position,
                    index_ident,
                    DataType::Number(NumberType::Pp),
                    ident_expression.clone(),
                    false,
                );
                self.symbol_table_mut().push_local_variable(variable);
                self.loop_stack += 1;
                self.analyze_statement(statement);
                self.loop_stack -= 1;
                self.symbol_table_mut().pop_scope();
            }
            _ => {
                self.error_diag
                    .borrow_mut()
                    .not_implemented(statement.position(), format!("{:?}", statement).as_str());
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

    fn analyze_expr(&self, expr: &Expression<'a>) -> Option<DataType<'a>> {
        return match expr {
            Expression::Number { number_type, .. } => Some(DataType::Number(number_type.clone())),
            Expression::P { .. } => Some(DataType::P),
            Expression::Booba { .. } => Some(DataType::Booba),
            Expression::Yarn { .. } => Some(DataType::Yarn),
            Expression::Unary {
                operand,
                op,
                position,
            } => {
                let data_type = self.analyze_expr(operand)?;
                return match op {
                    UnaryOperator::Not => match data_type {
                        DataType::Booba => Some(data_type),
                        _ => {
                            self.error_diag.borrow_mut().invalid_data_type(
                                *position,
                                &DataType::Booba,
                                &data_type,
                            );
                            Some(data_type)
                        }
                    },
                    UnaryOperator::Negate => match data_type {
                        DataType::Number(..) => Some(data_type),
                        _ => {
                            self.error_diag.borrow_mut().invalid_data_type(
                                *position,
                                &DataType::Number(NumberType::Pp),
                                &data_type,
                            );
                            Some(data_type)
                        }
                    },
                };
            }
            Expression::Binary {
                lhs,
                rhs,
                op,
                position,
            } => {
                let lhs_data_type = self.analyze_expr(lhs)?;
                let rhs_data_type = self.analyze_expr(rhs)?;

                self.check_if_mixed_data_types(&lhs_data_type, &rhs_data_type, *position);
                // TODO: Check whether the binary operator is available for the given data type.
                use crate::parse::parser::BinaryOperator::*;
                match op {
                    Add | Subtract | Multiply | Divide => Some(lhs_data_type),
                    NotEqual | Equal | GreaterThan | GreaterThanOrEqual | LessThan
                    | LessThanOrEqual | And | Or => Some(DataType::Booba),
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
                        Some(variable.data_type().clone())
                    } else {
                        self.error_diag
                            .borrow_mut()
                            .variable_not_initialized(*position, identifier);
                        Some(variable.data_type().clone())
                    }
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);
                    None
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
                            *position,
                            identifier,
                            function.parameters().len(),
                            arguments.len(),
                        );
                    } else {
                        // Check the argument data type.
                        if let Some(mismatched_arg) = arguments
                            .iter()
                            .zip(function.parameters().iter().map(|var| var.data_type()))
                            .find(|(a, b)| {
                                if let Some(expr) = self.analyze_expr(a) {
                                    expr != **b
                                } else {
                                    false
                                }
                            })
                        {
                            let got = self.analyze_expr(mismatched_arg.0)?;
                            self.error_diag.borrow_mut().invalid_data_type(
                                mismatched_arg.0.position(),
                                mismatched_arg.1,
                                &got,
                            )
                        }
                    }
                    Some(function.return_type().clone())
                } else {
                    self.error_diag
                        .borrow_mut()
                        .function_does_not_exist(*position, identifier);
                    None
                };
            }
            _ => None,
        };
    }
}
