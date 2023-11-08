use dpp_macros::Pos;
use itertools::Itertools;

use crate::parse::analysis::{
    BoundCase, BoundDataType, BoundExpression, BoundFunction, BoundLiteralValue, BoundStatement,
    BoundStructField, BoundTranslationUnit, BoundVariable, BoundVariableAssignment,
};
use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::parser::{
    Block, Case, DataType, LiteralValue, Modifier, Statement, TranslationUnit, UnaryOperator,
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
    /// Result<SymbolTable, `SyntaxError`> - the symbol table if no errors were found
    pub fn analyze(
        mut self,
        translation_unit: &'a TranslationUnit<'a>,
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
        translation_unit: &'a TranslationUnit<'a>,
    ) -> BoundTranslationUnit {
        // Register the global functions.
        translation_unit
            .struct_declarations()
            .iter()
            .for_each(|a_struct| {
                let maybe_struct = self.symbol_table().find_struct_definition(a_struct.ident());
                if maybe_struct.0 == 0 && maybe_struct.1.is_some() {
                    self.error_diag
                        .borrow_mut()
                        .struct_already_exists(a_struct.position(), a_struct.ident());
                } else {
                    let vec = a_struct
                        .fields()
                        .iter()
                        .map(|field| {
                            (
                                String::from(field.ident()),
                                self.to_bound_data_type(field.data_type(), field.position()),
                            )
                        })
                        .collect_vec();
                    self.symbol_table_mut().define_struct(a_struct.ident(), vec);
                }
            });
        translation_unit.functions().iter().for_each(|function| {
            if self
                .symbol_table()
                .find_function_definition(function.identifier())
                .is_some()
            {
                self.error_diag
                    .borrow_mut()
                    .function_already_exists(function.position(), function.identifier());
            } else {
                let return_type =
                    self.to_bound_data_type(function.return_type(), function.position());
                let parameters = self.to_bound_parameters(function.parameters());
                self.symbol_table_mut().define_function(
                    return_type,
                    function.identifier(),
                    parameters,
                );
            }
        });

        // Analyze global statements.
        let global_variables = translation_unit
            .global_statements()
            .iter()
            .map(|statement| self.analyze_statement(statement))
            .collect_vec();

        // Analyze the parsed functions.
        let functions = translation_unit
            .functions()
            .iter()
            .map(|function| self.analyze_function(function))
            .collect_vec();

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
            if !main_function.parameters().is_empty() {
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

        assert_eq!(
            self.symbol_table.current_scope_depth(),
            1,
            "There should only be the global scope."
        );

        BoundTranslationUnit::new(
            functions,
            main_function_identifier,
            self.symbol_table().current_scope().stack_position(),
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
        self.begin_function(function);
        let function_id = self.symbol_table().current_function().unwrap().id();
        let parameters = self.to_bound_parameters(function.parameters());
        let bound_statements = self.analyze_statements(function.statements());
        if function.return_type() != &DataType::Nopp {
            // If it's anything other than Nopp, then we require the function to have
            // a return statement at the very end.
            let last_statement = function.statements().last();
            if let Some(statement) = last_statement {
                if let Statement::Bye { .. } = statement {
                    // Do nothing.
                } else {
                    self.error_diag
                        .borrow_mut()
                        .missing_return_statement(function.position());
                }
            } else {
                self.error_diag
                    .borrow_mut()
                    .missing_return_statement(function.position());
            }
        }
        let stack_position = self
            .symbol_table()
            .current_function()
            .unwrap()
            .stack_frame_size();

        self.end_function();

        BoundFunction::new(
            function_id,
            stack_position,
            function.identifier() == "main",
            self.to_bound_data_type(function.return_type(), function.position())
                .size(),
            parameters,
            bound_statements,
        )
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
                if self.is_variable_in_scope(variable.identifier()) {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }
                let data_type = self.to_bound_data_type(variable.data_type(), variable.position());
                self.declare_variable(
                    variable.position(),
                    variable.modifiers().clone(),
                    data_type,
                    variable.identifier(),
                    false,
                );
                if let Some(expression) = variable.value() {
                    self.symbol_table_mut()
                        .initialize_variable(variable.identifier());
                    let (level, var_decl) = self
                        .symbol_table()
                        .find_variable_declaration(variable.identifier());
                    let var_decl = var_decl.unwrap();
                    let position = BoundVariable::new(
                        level,
                        var_decl.stack_position() as i32,
                        var_decl.data_type().clone(),
                        var_decl.has_modifier(Modifier::Const),
                    );
                    let data_type =
                        self.to_bound_data_type(variable.data_type(), variable.position());
                    let value = self
                        .analyze_expr(expression, Some(&data_type), Some(variable.position()))
                        .1;

                    return BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                        position, value,
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
                        Some(&BoundDataType::Booba),
                        Some(expression.position()),
                    )
                    .1;
                self.loop_depth += 1;
                let bound_statement = self.analyze_statement(statement);
                self.loop_depth -= 1;
                BoundStatement::While {
                    expression,
                    statement: Box::new(bound_statement),
                }
            }
            Statement::Loop { statement, .. } => {
                self.loop_depth += 1;
                let statement = self.analyze_statement(statement);
                self.loop_depth -= 1;
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
                    .analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position))
                    .1;
                self.loop_depth += 1;
                let statement = self.analyze_statement(statement);
                self.loop_depth -= 1;
                BoundStatement::DoWhile {
                    expression,
                    statement: Box::new(statement),
                }
            }
            Statement::Continue { position } => {
                if self.loop_depth == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_continue_placement(*position);
                }
                BoundStatement::Continue
            }
            Statement::Break { position } => {
                if self.loop_depth == 0 {
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
                    let function_descriptor = self.symbol_table().current_function().unwrap();

                    let return_type = function_descriptor.return_type();
                    let expression = self.analyze_expr(expression, None, None);
                    self.check_data_type(return_type, expression.0.as_ref(), *position);
                    let return_type_size = expression.0.map_or(0, |data_type| data_type.size());
                    return BoundStatement::Bye {
                        return_type_size,
                        expression: Some(expression.1),
                    };
                }

                BoundStatement::Bye {
                    return_type_size: 0,
                    expression: None,
                }
            }
            Statement::If {
                expression,
                statement,
                position,
            } => {
                let expression =
                    self.analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position));
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
                    self.analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position));
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
                let (level, var_decl) = self.symbol_table().find_variable_declaration(identifier);
                if let Some(variable) = var_decl {
                    let is_const = variable.has_modifier(Modifier::Const);
                    if is_const {
                        self.error_diag
                            .borrow_mut()
                            .cannot_assign_to_const_variable(*position, identifier);
                    }
                    let data_type = variable.data_type();
                    let expression =
                        self.analyze_expr(expression, Some(data_type), Some(*position));

                    let offset = variable.stack_position();
                    let data_type = variable.data_type().clone();
                    self.symbol_table_mut().initialize_variable(identifier);

                    let position = BoundVariable::new(level, offset as i32, data_type, is_const);
                    BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                        position,
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
                let expression = self.analyze_expr(expression, None, None);
                if let Some(switch_data_type) = expression.0 {
                    BoundStatement::Switch {
                        expression: expression.1,
                        cases: self.analyze_cases(cases, Some(&switch_data_type)),
                    }
                } else {
                    BoundStatement::Empty
                }
            }
            Statement::For {
                index_ident,
                ident_expression,
                length_expression,
                statement,
                position,
            } => {
                // Push a new scope and introduce the index variable.
                self.symbol_table_mut().push_scope();

                // Declare the variable as pp.
                let data_type = self.to_bound_data_type(&DataType::Pp, *position);
                self.declare_variable(*position, Vec::new(), data_type.clone(), index_ident, false);

                // Mark the variable as initialized immediately. We initialize it later on.
                self.symbol_table_mut().initialize_variable(index_ident);

                // Check that the ident expression is pp or none.
                let bound_ident_expression;
                if let Some(ident_expression) = ident_expression {
                    bound_ident_expression = Some(self.analyze_expr(
                        ident_expression,
                        Some(&data_type),
                        Some(ident_expression.position()),
                    ));
                } else {
                    bound_ident_expression = None;
                }

                // Check that the length expression is pp.
                let bound_length_expression = self.analyze_expr(
                    length_expression,
                    Some(&data_type),
                    Some(length_expression.position()),
                );

                // Get the descriptor of the variable and some metadata.
                let (level, var_decl) = self.symbol_table().find_variable_declaration(index_ident);
                let var_decl = var_decl.unwrap();
                let offset = var_decl.stack_position();
                let is_const = var_decl.has_modifier(Modifier::Const);

                // Increment the loop stack for break, continue, etc. statements and analyze the
                // statements.
                self.loop_depth += 1;
                let bound_statement = self.analyze_statement(statement);

                self.loop_depth -= 1;
                self.symbol_table_mut().pop_scope();

                BoundStatement::For {
                    ident_position: BoundVariable::new(level, offset as i32, data_type, is_const),
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

    fn analyze_cases(
        &mut self,
        cases: &Vec<Case<'a>>,
        expected_data_type: Option<&BoundDataType>,
    ) -> Vec<BoundCase> {
        cases
            .iter()
            .map(|case| {
                BoundCase::new(
                    self.analyze_expr(case.expression(), expected_data_type, Some(case.position()))
                        .1,
                    self.analyze_block(case.block()),
                )
            })
            .collect_vec()
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
        let bound_statements = self.analyze_statements(block.statements());
        self.symbol_table.pop_scope();
        bound_statements
    }

    fn analyze_statements(&mut self, statements: &Vec<Statement<'a>>) -> Vec<BoundStatement> {
        statements
            .iter()
            .map(|statement| self.analyze_statement(statement))
            .collect_vec()
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
    fn calc_data_type(&self, expr: &Expression<'a>) -> Option<BoundDataType> {
        return match expr {
            Expression::Literal { value, .. } => Some(match value {
                LiteralValue::Pp(_) => BoundDataType::Pp,
                LiteralValue::Flaccid(_, _) => BoundDataType::Flaccid,
                LiteralValue::AB(_, _) => BoundDataType::AB,
                LiteralValue::P(_) => BoundDataType::P,
                LiteralValue::Booba(_) => BoundDataType::Booba,
                LiteralValue::Yarn(_) => BoundDataType::Yarn,
                LiteralValue::Struct(name, fields) => BoundDataType::Struct(
                    String::from(*name),
                    fields
                        .iter()
                        .map(|field| {
                            self.to_bound_data_type(field.data_type(), field.position())
                                .size()
                        })
                        .sum(),
                ),
            }),
            Expression::Unary {
                operand,
                op,
                position,
            } => {
                let data_type = self.calc_data_type(operand)?;
                return match op {
                    UnaryOperator::Not => match data_type {
                        BoundDataType::Booba => Some(data_type),
                        _ => {
                            self.error_diag.borrow_mut().invalid_data_type(
                                *position,
                                &BoundDataType::Booba,
                                &data_type,
                            );
                            Some(data_type)
                        }
                    },
                    UnaryOperator::Negate => match data_type {
                        BoundDataType::Pp => Some(data_type),
                        BoundDataType::Flaccid => Some(data_type),
                        _ => {
                            self.error_diag.borrow_mut().invalid_data_type(
                                *position,
                                &BoundDataType::Pp,
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
                use crate::parse::parser::BinaryOperator::{
                    Add, And, Divide, Equal, GreaterThan, GreaterThanOrEqual, LessThan,
                    LessThanOrEqual, Multiply, NotEqual, Or, Subtract,
                };
                match op {
                    Add | Subtract | Multiply | Divide => Some(lhs_data_type),
                    NotEqual | Equal | GreaterThan | GreaterThanOrEqual | LessThan
                    | LessThanOrEqual | And | Or => Some(BoundDataType::Booba),
                }
            }
            Expression::Identifier { identifier, .. } => self
                .symbol_table()
                .find_variable_declaration(identifier)
                .1
                .map(|variable| variable.data_type().clone()),
            Expression::FunctionCall { identifier, .. } => self
                .symbol_table()
                .find_function_definition(identifier)
                .map(|function| function.return_type().clone()),
            Expression::Struct { .. } => None,
            // TODO: Add structs to symbol table.
            _ => None,
        };
    }

    fn analyze_expr(
        &self,
        expression: &Expression<'a>,
        expected_data_type: Option<&BoundDataType>,
        position: Option<(u32, u32)>,
    ) -> (Option<BoundDataType>, BoundExpression) {
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
            Expression::Literal { value, .. } => BoundExpression::Literal(match value {
                LiteralValue::Pp(pp) => BoundLiteralValue::Pp(*pp),
                LiteralValue::Flaccid(a, b) => BoundLiteralValue::Flaccid(*a, *b),
                LiteralValue::AB(a, b) => BoundLiteralValue::AB(*a, *b),
                LiteralValue::P(p) => BoundLiteralValue::P(*p),
                LiteralValue::Booba(booba) => BoundLiteralValue::Booba(*booba),
                LiteralValue::Yarn(yarn) => BoundLiteralValue::Yarn(String::from(*yarn)),
                LiteralValue::Struct(name, fields) => BoundLiteralValue::Struct(
                    String::from(*name),
                    fields
                        .iter()
                        .map(|field| {
                            BoundStructField::new(
                                field.modifiers().clone(),
                                self.to_bound_data_type(field.data_type(), field.position()),
                                String::from(field.ident()),
                            )
                        })
                        .collect_vec(),
                ),
            }),
            Expression::Unary { op, operand, .. } => BoundExpression::Unary {
                op: op.clone(),
                operand: Box::new(self.expr(operand)),
            },
            Expression::Binary { lhs, op, rhs, .. } => BoundExpression::Binary {
                lhs: Box::new(self.expr(lhs)),
                op: op.clone(),
                rhs: Box::new(self.expr(rhs)),
            },
            Expression::Identifier {
                position,
                identifier,
            } => {
                let (level, var_decl) = self.symbol_table().find_variable_declaration(identifier);
                if let Some(variable) = var_decl {
                    if !variable.is_initialized() {
                        self.error_diag
                            .borrow_mut()
                            .variable_not_initialized(*position, identifier);
                    }

                    BoundExpression::Variable(BoundVariable::new(
                        level,
                        variable.stack_position() as i32,
                        variable.data_type().clone(),
                        variable.has_modifier(Modifier::Const),
                    ))
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);
                    BoundExpression::Variable(BoundVariable::new(0, 0, BoundDataType::Pp, true))
                }
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                position,
            } => {
                let (id, return_type_size, arguments_size);
                if let Some(function) = self.symbol_table().find_function_definition(identifier) {
                    id = function.id();
                    return_type_size = function.return_type().size();
                    arguments_size = function.parameters_size()
                } else {
                    id = 0;
                    return_type_size = 0;
                    arguments_size = 0;

                    self.error_diag
                        .borrow_mut()
                        .function_does_not_exist(*position, identifier);
                }
                BoundExpression::FunctionCall {
                    level: 1,
                    identifier: id,
                    return_type_size,
                    arguments_size,
                    arguments: arguments.iter().map(|arg| self.expr(arg)).collect_vec(),
                }
            }
            Expression::Invalid { .. } => {
                unreachable!("Should have thrown syntax error after parsing")
            }
            Expression::Struct {
                position,
                definitions,
                identifier,
            } => {
                self.error_diag.borrow_mut().not_implemented(
                    *position,
                    format!(
                        "Struct definition analysis not implemented\
                     - struct \"{identifier}\" and \"{definitions:?}\""
                    )
                    .as_str(),
                );
                BoundExpression::Literal(BoundLiteralValue::Struct(
                    String::from(*identifier),
                    Vec::new(),
                ))
            }
        }
    }
}
