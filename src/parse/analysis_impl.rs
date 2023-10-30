use dpp_macros::Pos;

use crate::parse::analysis::{
    BoundExpression, BoundFunction, BoundStatement, BoundTranslationUnit, BoundVariableAssignment,
    BoundVariablePosition,
};
use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::parser::{
    Block, DataType, NumberType, Statement, TranslationUnit, UnaryOperator, Variable,
};
use crate::parse::{Expression, Function, SemanticAnalyzer};

impl<'a, 'b> SemanticAnalyzer<'a, 'b> {
    /// # Summary
    ///
    /// Analyzes the translation unit and consumes self to produce a symbol table.
    ///
    /// # Arguments
    ///
    /// * `translation_unit`: the translation unit to analyze
    ///
    /// # Returns
    /// Result<SymbolTable, SyntaxError> - the symbol table if no errors were found
    pub fn analyze(
        mut self,
        translation_unit: &TranslationUnit<'a>,
    ) -> Result<BoundTranslationUnit, SyntaxError> {
        let bound_transl_unit = self.analyze_translation_unit(translation_unit);
        self.error_diag.borrow().check_errors()?;
        Ok(bound_transl_unit)
    }

    /// # Summary
    /// Analyzes the translation unit. First registers the function names, then analyzes the
    /// global statements, and lastly analyzes the functions.
    ///
    /// # Arguments
    ///
    /// * `translation_unit`: the translation unit to analyze
    fn analyze_translation_unit(
        &mut self,
        translation_unit: &TranslationUnit<'a>,
    ) -> BoundTranslationUnit {
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
            self.symbol_table_mut().push_global_function(function)
        });

        // Analyze global statements.
        let global_variables = translation_unit
            .global_statements()
            .iter()
            .map(|statement| self.analyze_global_statement(statement))
            .filter(|global_stat| global_stat.is_some())
            .map(|statement| statement.unwrap())
            .collect::<Vec<BoundVariableAssignment>>();

        // Analyze the parsed functions.
        let functions = translation_unit
            .functions()
            .iter()
            .map(|function| self.analyze_function(function))
            .collect::<Vec<BoundFunction>>();

        // TODO: Check the return type of the main function.
        // |function| {
        //                 if function.identifier() == "main" {
        //                     if function.return_type() != &DataType::Number(NumberType::Pp) {
        //                         self.error_diag.borrow_mut().invalid_return_type(
        //                             (0, 0),
        //                             "main",
        //                             &DataType::Number(NumberType::Pp),
        //                             function.return_type(),
        //                         );
        //                     }
        //                 }
        //             }
        let main_function_identifier;
        if let Some(main_function) = functions
            .iter()
            .find(|function| function.is_main_function())
        {
            if main_function.parameters().len() != 0 {
                self.error_diag.borrow_mut().invalid_number_of_arguments(
                    (0, 0),
                    "main",
                    0,
                    main_function.parameters().len(),
                );
            }
            main_function_identifier = main_function.identifier();
        } else {
            main_function_identifier = 0;
            self.error_diag.borrow_mut().no_main_method_found_error();
        }

        BoundTranslationUnit::new(
            functions,
            main_function_identifier,
            self.symbol_table().global_scope().stack_position(),
            global_variables,
        )
    }

    /// # Summary
    /// Analyzes the function. Pushes the function to the function stack, registers it as
    /// the currently analyzed function. Then analyzes the block and checks whether the last
    /// statement is a return statement provided this function has a return type other than Nopp.
    ///
    /// # Arguments
    ///
    /// * `function`: the function to analyze
    fn analyze_function(&mut self, function: &Function<'a>) -> BoundFunction {
        self.begin_function(&function);
        let mut current_size = 0;
        let parameters = function
            .parameters()
            .iter()
            .map(|v| {
                let size = self
                    .symbol_table()
                    .function_scope(function.identifier())
                    .unwrap()
                    .variable(v.identifier())
                    .unwrap()
                    .size_in_instructions();
                current_size += size;
                -(current_size as i32)
            })
            .map(|offset| BoundVariablePosition::new(0, offset))
            .collect::<Vec<BoundVariablePosition>>();

        let bound_statements = self.analyze_block(function.block());
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
        let sym_table = self.symbol_table();
        let function_scope = sym_table.function_scope(function.identifier()).unwrap();
        // Shift the stack pointer by activation record + declared variable count.

        let stack_position = function_scope.stack_position();

        let function_index = self.current_function_index;
        self.current_function_index += 1;
        BoundFunction::new(
            function_index,
            stack_position,
            function.identifier() == "main",
            function.return_type().size_in_instructions(),
            parameters,
            bound_statements,
        )
    }

    /// # Summary
    /// Analyzes the global statements. The only global statement that is currently supported is
    /// a variable declaration. This function differs very slightly from the analyze_statement -
    /// this function only supports the variable declaration statement and registers the variables
    /// in the global scope instead of the local scope.
    ///
    /// # Arguments
    ///
    /// * `statement`: the global statement to analyze
    fn analyze_global_statement(
        &mut self,
        statement: &Statement<'a>,
    ) -> Option<BoundVariableAssignment> {
        match &statement {
            Statement::VariableDeclaration { variable, .. } => {
                if self
                    .symbol_table()
                    .global_variable(variable.identifier())
                    .is_some()
                {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }

                self.symbol_table_mut().push_global_variable(variable);
                if let Some(expression) = variable.value() {
                    self.symbol_table_mut()
                        .set_variable_initialized(variable.identifier());
                    let (level, var_decl) = self.symbol_table().variable(variable.identifier());
                    let var_decl = var_decl.unwrap();
                    let offset = var_decl.stack_position();
                    return Some(BoundVariableAssignment::new(
                        BoundVariablePosition::new(level, offset as i32),
                        self.analyze_expr(
                            expression,
                            Some(variable.data_type()),
                            Some(variable.position()),
                        )
                        .1,
                    ));
                }
                None
            }
            _ => None,
        }
    }

    /// # Summary
    /// Analyzes the (local) statements.
    ///
    /// # Arguments
    ///
    /// * `statement`: the (local) statement to analyze
    fn analyze_statement(&mut self, statement: &Statement<'a>) -> BoundStatement {
        match &statement {
            Statement::VariableDeclaration { variable, .. } => {
                if self
                    .symbol_table()
                    .local_variable(variable.identifier())
                    .is_some()
                {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }

                self.symbol_table_mut().push_local_variable(variable, false);
                if let Some(expression) = variable.value() {
                    self.symbol_table_mut()
                        .set_variable_initialized(variable.identifier());
                    let (level, var_decl) = self.symbol_table().variable(variable.identifier());
                    let var_decl = var_decl.unwrap();
                    return BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                        BoundVariablePosition::new(level, var_decl.stack_position() as i32),
                        self.analyze_expr(
                            expression,
                            Some(variable.data_type()),
                            Some(variable.position()),
                        )
                        .1,
                    ));
                }
                BoundStatement::Empty
            }
            Statement::Expression { expression, .. } => {
                let bound_expression = self.analyze_expr(expression, None, None).1;
                BoundStatement::Expression(bound_expression)
            }
            Statement::While {
                expression,
                statement,
                ..
            } => {
                let expression = self
                    .analyze_expr(
                        expression,
                        Some(&DataType::Booba),
                        Some(expression.position()),
                    )
                    .1;
                self.loop_stack += 1;
                let bound_statement = self.analyze_statement(statement);
                self.loop_stack -= 1;
                BoundStatement::While {
                    expression,
                    statement: Box::new(bound_statement),
                }
            }
            Statement::Loop { statement, .. } => {
                self.loop_stack += 1;
                let statement = self.analyze_statement(statement);
                self.loop_stack -= 1;
                BoundStatement::Loop {
                    statement: Box::new(statement),
                }
            }
            Statement::DoWhile {
                expression,
                statement,
                position,
            } => {
                let expression = self
                    .analyze_expr(expression, Some(&DataType::Booba), Some(*position))
                    .1;
                self.loop_stack += 1;
                let statement = self.analyze_statement(statement);
                self.loop_stack -= 1;
                BoundStatement::DoWhile {
                    expression,
                    statement: Box::new(statement),
                }
            }
            Statement::Continue { position } => {
                if self.loop_stack == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_continue_placement(*position);
                }
                BoundStatement::Continue
            }
            Statement::Break { position } => {
                if self.loop_stack == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_break_placement(*position);
                }
                BoundStatement::Break
            }
            Statement::Block { block, .. } => {
                let statements = self.analyze_block(block);
                BoundStatement::Statements(statements)
            }
            Statement::Bye {
                expression,
                position,
            } => {
                if let Some(expression) = expression {
                    // TODO: Check return type of function.
                    let expression = self.analyze_expr(expression, None, None);
                    self.check_data_type(
                        self.symbol_table()
                            .function(self.current_function.unwrap())
                            .unwrap()
                            .return_type(),
                        expression.0.as_ref(),
                        *position,
                    );

                    let current_function = self
                        .symbol_table()
                        .function_scope(self.current_function.unwrap())
                        .unwrap();
                    let function_identifier = current_function.function_identifier();
                    let function_descriptor =
                        self.symbol_table().function(function_identifier).unwrap();
                    let parameters_size = function_descriptor.parameters_size();
                    let return_type_size = expression.0.unwrap().size_in_instructions();

                    return BoundStatement::Bye {
                        return_offset: -(return_type_size as i32) - parameters_size as i32,
                        expression: Some(expression.1),
                    };
                }
                BoundStatement::Bye {
                    return_offset: 0,
                    expression: None,
                }
            }
            Statement::If {
                expression,
                statement,
                position,
            } => {
                let expression =
                    self.analyze_expr(expression, Some(&DataType::Booba), Some(*position));
                let statement = self.analyze_statement(statement);
                BoundStatement::If {
                    expression: expression.1,
                    statement: Box::new(statement),
                }
            }
            Statement::IfElse {
                expression,
                statement,
                position,
                else_statement,
            } => {
                let expression =
                    self.analyze_expr(expression, Some(&DataType::Booba), Some(*position));
                let statement = self.analyze_statement(statement);
                let else_statement = self.analyze_statement(else_statement);
                BoundStatement::IfElse {
                    expression: expression.1,
                    statement: Box::new(statement),
                    else_statement: Box::new(else_statement),
                }
            }
            Statement::Assignment {
                identifier,
                expression,
                position,
            } => {
                let (level, var_decl) = self.symbol_table().variable(identifier);
                if let Some(variable) = var_decl {
                    let data_type = variable.data_type();
                    let expression =
                        self.analyze_expr(expression, Some(data_type), Some(*position));

                    let offset = variable.stack_position();
                    self.symbol_table_mut().set_variable_initialized(identifier);
                    BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                        BoundVariablePosition::new(level, offset as i32),
                        expression.1,
                    ))
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);
                    BoundStatement::Empty
                }
            }
            Statement::Empty { .. } => BoundStatement::Empty,
            Statement::Switch {
                expression, cases, ..
            } => {
                if let Some(switch_data_type) = self.calc_data_type(expression) {
                    if let Some(mismatched_data_type) = cases
                        .iter()
                        .map(|case| {
                            (
                                case.block().position(),
                                self.calc_data_type(case.expression()),
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
                            mismatched_data_type.1.as_ref(),
                            mismatched_data_type.0,
                        );
                    }

                    // TODO: This checks for the expression data type for no reason and will
                    // produce duplicate errors.
                    let expression = self.analyze_expr(expression, None, None);

                    // BoundStatement::Switch {expression, cases: self.analyze_cases}
                    return BoundStatement::Empty;
                }
                BoundStatement::Empty
            }
            Statement::For {
                index_ident,
                ident_expression,
                length_expression,
                statement,
                position,
            } => {
                if self.symbol_table().local_variable(index_ident).is_some() {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(*position, index_ident);
                }

                let bound_ident_expression;
                if let Some(ident_expression) = ident_expression {
                    bound_ident_expression = Some(self.analyze_expr(
                        ident_expression,
                        Some(&DataType::Number(NumberType::Pp)),
                        Some(ident_expression.position()),
                    ));
                } else {
                    bound_ident_expression = None;
                }

                let bound_length_expression = self.analyze_expr(
                    length_expression,
                    Some(&DataType::Number(NumberType::Pp)),
                    Some(length_expression.position()),
                );

                self.symbol_table_mut().push_scope();
                let index_variable = Variable::new(
                    *position,
                    index_ident,
                    DataType::Number(NumberType::Pp),
                    ident_expression.clone(),
                );
                self.symbol_table_mut()
                    .push_local_variable(&index_variable, false);

                let (level, var_decl) = self.symbol_table().variable(index_variable.identifier());
                let var_decl = var_decl.unwrap();
                let offset = var_decl.stack_position();

                self.loop_stack += 1;
                let bound_statement = self.analyze_statement(statement);
                self.loop_stack -= 1;
                self.symbol_table_mut().pop_scope();

                BoundStatement::For {
                    ident_position: BoundVariablePosition::new(level as usize, offset as i32),
                    ident_expression: bound_ident_expression.map(|exp| exp.1),
                    length_expression: bound_length_expression.1,
                    statement: Box::new(bound_statement),
                }
            }
            _ => {
                self.error_diag
                    .borrow_mut()
                    .not_implemented(statement.position(), format!("{:?}", statement).as_str());
                BoundStatement::Empty
            }
        }
    }

    /// # Summary
    /// Analyzes the block. Essentially just pushes a scope onto the stack and analyzes the
    /// statements inside the block. Once the block finishes the scope is popped off the stack.
    ///
    /// # Arguments
    ///
    /// * `block`: the block to analyze
    fn analyze_block(&mut self, block: &Block<'a>) -> Vec<BoundStatement> {
        self.symbol_table.push_scope();
        let bound_statements = block
            .statements()
            .iter()
            .map(|statement| self.analyze_statement(statement))
            .collect::<Vec<BoundStatement>>();
        self.symbol_table.pop_scope();
        bound_statements
    }

    /// # Summary
    /// Analyzes the expression. This function is the core of the semantic analyzer. It analyzes
    /// the expression and returns the data type of the expression. If the expression is invalid
    /// then it returns None. This function is recursive and will analyze the sub-expressions
    /// of the expression.
    ///
    /// # Arguments
    ///
    /// * `expression`: the expression to analyze
    /// # Returns
    /// Option<DataType> - the data type of the expression if it is valid, None otherwise
    fn calc_data_type(&self, expr: &Expression<'a>) -> Option<DataType<'a>> {
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
                let data_type = self.calc_data_type(operand)?;
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
                let lhs_data_type = self.calc_data_type(lhs)?;
                let rhs_data_type = self.calc_data_type(rhs)?;

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
                let (_, var_decl) = self.symbol_table().variable(identifier);
                return if let Some(variable) = var_decl {
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
                };
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                position,
            } => {
                return if let Some(function) = self.symbol_table().function(identifier) {
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
                                if let Some(expr) = self.calc_data_type(a) {
                                    expr != **b
                                } else {
                                    false
                                }
                            })
                        {
                            let got = self.calc_data_type(mismatched_arg.0)?;
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

    fn analyze_expr(
        &self,
        expression: &Expression<'a>,
        expected_data_type: Option<&DataType<'a>>,
        position: Option<(u32, u32)>,
    ) -> (Option<DataType<'a>>, BoundExpression) {
        let data_type = self.calc_data_type(expression);
        if let Some(expected_data_type) = expected_data_type {
            if let Some(position) = position {
                self.check_data_type(expected_data_type, data_type.as_ref(), position);
            }
        }

        (data_type, self.expr(expression))
    }

    fn expr(&self, expression: &Expression<'a>) -> BoundExpression {
        match expression {
            Expression::Number {
                number_type, value, ..
            } => BoundExpression::Number {
                number_type: number_type.clone(),
                value: *value,
            },
            Expression::P { value, .. } => BoundExpression::P(*value),
            Expression::Booba { value, .. } => BoundExpression::Booba(*value),
            Expression::Yarn { value, .. } => BoundExpression::Yarn(String::from(*value)),
            Expression::Unary { op, operand, .. } => BoundExpression::Unary {
                op: op.clone(),
                operand: Box::new(self.expr(operand)),
            },
            Expression::Binary { lhs, op, rhs, .. } => BoundExpression::Binary {
                lhs: Box::new(self.expr(lhs)),
                op: op.clone(),
                rhs: Box::new(self.expr(rhs)),
            },
            Expression::Identifier { identifier, .. } => {
                let (level, var_decl) = self.symbol_table().variable(*identifier);
                let var_decl = var_decl.unwrap();
                let offset = var_decl.stack_position();
                BoundExpression::Variable(BoundVariablePosition::new(level as usize, offset as i32))
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                ..
            } => {
                // TODO: Use identifier map.
                BoundExpression::FunctionCall {
                    level: 1,
                    identifier: 1,
                    return_type_size: 0,
                    arguments_size: 0,
                    arguments: arguments
                        .iter()
                        .map(|arg| self.expr(arg))
                        .collect::<Vec<BoundExpression>>(),
                }
            }
            Expression::Invalid { .. } => unreachable!(),
        }
    }
}
