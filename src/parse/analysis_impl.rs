use dpp_macros::Pos;
use itertools::Itertools;

use crate::parse::analysis::{
    BoundCase, BoundDataType, BoundExpression, BoundFunction, BoundLiteralValue, BoundStatement,
    BoundStructField, BoundStructFieldAssignment, BoundTranslationUnit, BoundVariable,
    BoundVariableAssignment, BoundVariablePosition, StructDefinitionDescriptor,
    VariableDeclarationDescriptor,
};
use crate::parse::error_diagnosis::SyntaxError;
use crate::parse::parser::{
    BinaryOperator, Block, Case, DataType, LiteralValue, Modifier, Statement, TranslationUnit,
    UnaryOperator,
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
                    let mut current_offset = 0;
                    let vec = a_struct
                        .fields()
                        .iter()
                        .map(|field| {
                            let offset = current_offset;
                            let bound_data_type =
                                self.to_bound_data_type(field.data_type(), field.position());
                            current_offset += bound_data_type.size();
                            BoundStructField::new(
                                field.modifiers().clone(),
                                bound_data_type,
                                String::from(field.identifier()),
                                offset,
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
            }

            let return_type = self.to_bound_data_type(function.return_type(), function.position());
            let parameters = self.to_bound_parameters(function.parameters());
            self.symbol_table_mut()
                .define_function(return_type, function.identifier(), parameters);
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

        // Analyze the main function.
        let main_function_identifier = self.find_and_analyze_main_function(&functions).unwrap_or(0);

        // Make sure the only scope that's currently in the symbol table is the global scope.
        assert_eq!(
            self.symbol_table.current_scope_depth(),
            1,
            "There should only be the global scope."
        );
        let global_stack_frame_size = self.symbol_table().current_scope().stack_position();

        BoundTranslationUnit::new(
            functions,
            main_function_identifier,
            global_stack_frame_size,
            global_variables,
        )
    }

    fn find_and_analyze_main_function(&mut self, functions: &Vec<BoundFunction>) -> Option<usize> {
        if let Some(main_function) = functions
            .iter()
            .find(|function| function.is_main_function())
        {
            if !main_function.parameters().is_empty() {
                self.error_diag.borrow_mut().invalid_main_function(
                    format!(
                        "Expected 0 parameters, got {}",
                        main_function.parameters().len()
                    )
                    .as_str(),
                );
            }
            match main_function.return_type() {
                BoundDataType::Pp => {
                    // Do nothing.
                }
                _ => self
                    .error_diag
                    .borrow_mut()
                    .invalid_main_function("Invalid return type. Expected \"pp\"."),
            }

            Some(main_function.identifier())
        } else {
            self.error_diag.borrow_mut().no_main_method_found_error();
            None
        }
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
        // Push a function scope to symbol table. This will set the currently analyzed function
        // to this one.
        self.symbol_table_mut()
            .push_function_scope(function.identifier());

        // Push the parameters to the scope.
        for parameter in function.parameters() {
            let data_type = self.to_bound_data_type(parameter.data_type(), parameter.position());
            self.declare_variable(
                parameter.position(),
                parameter.modifiers().clone(),
                data_type,
                parameter.identifier(),
                true,
            );
        }

        // Get the generated id.
        let function_id = self.symbol_table().current_function().unwrap().id();

        // Map the parameters to bound variables.
        let parameters = self.to_bound_parameters(function.parameters());

        // Analyze the function's statements.
        let bound_statements = self.analyze_statements(function.statements());

        // Make sure the last statement is the bye statement.
        // This could be done better, but it's way easier to implement this.
        if function.return_type() != &DataType::Nopp {
            // If it's anything other than Nopp, then we require the function to have
            // a return statement at the very end.
            let last_statement = function.statements().last();
            if let Some(statement) = last_statement {
                match statement {
                    Statement::Bye { .. } => {
                        // Do nothing.
                    }
                    _ => self
                        .error_diag
                        .borrow_mut()
                        .missing_return_statement(function.position()),
                };
            } else {
                self.error_diag
                    .borrow_mut()
                    .missing_return_statement(function.position());
            }
        }

        // Get the current stack pointer after all statements. This is basically the stack frame
        // size.
        let stack_frame_size = self
            .symbol_table()
            .current_function()
            .unwrap()
            .stack_frame_size();

        // Pop the function scope off the symbol table.
        self.symbol_table_mut().pop_scope();

        BoundFunction::new(
            function_id,
            stack_frame_size,
            function.identifier() == "main",
            self.to_bound_data_type(function.return_type(), function.position()),
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
            Statement::VariableDeclaration {
                variable, value, ..
            } => {
                // Check if the variable already exists.
                if self.is_variable_in_scope(variable.identifier()) {
                    self.error_diag
                        .borrow_mut()
                        .variable_already_exists(variable.position(), variable.identifier());
                }

                // Get the bound data type of the variable and declare it.
                let data_type = self.to_bound_data_type(variable.data_type(), variable.position());
                self.declare_variable(
                    variable.position(),
                    variable.modifiers().clone(),
                    data_type.clone(),
                    variable.identifier(),
                    false,
                );

                // If it's also an assignment there will be an expression on rhs, i.e. the
                // "<var-decl> `=' <expr>" case.
                if let Some(expression) = value {
                    // Get the descriptor of the variable declaration.
                    let (level, var_decl) = self
                        .symbol_table()
                        .find_variable_declaration(variable.identifier());

                    // It SHOULD be safe to unwrap this as we just declared the variable.
                    let var_decl = var_decl.expect("The variable to be already declared");

                    // The variable will ALWAYS have a static position in memory -- on the stack.
                    let position = BoundVariable::with_static_position(
                        level,
                        var_decl.stack_position() as i32,
                        data_type.clone(),
                        var_decl.has_modifier(Modifier::Const),
                    );

                    // Make sure the value is in fact the right data type.
                    let value = self
                        .analyze_expr(expression, Some(&data_type), Some(variable.position()))
                        .1;

                    // This statement is now a variable assignment.
                    return BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                        position, value,
                    ));
                }

                // The variable declaration means nothing to the emitter - the emitter cares
                // about the stack size only and that was incremented when we declared the
                // variable earlier.
                BoundStatement::Empty
            }
            Statement::Expression { expression, .. } => {
                let bound_expression = self.analyze_expr(expression, None, None).1;
                // Anything other than a function call expression makes no sense to emit.
                match bound_expression {
                    BoundExpression::FunctionCall { .. } => {
                        BoundStatement::Expression(bound_expression)
                    }
                    _ => BoundStatement::Empty,
                }
            }
            Statement::While {
                expression,
                statement,
                ..
            } => {
                // Analyze the "expr" in "while(expr)" and make sure it's a boolean type.
                let expression = self
                    .analyze_expr(
                        expression,
                        Some(&BoundDataType::Booba),
                        Some(expression.position()),
                    )
                    .1;

                // Increment the loop depth and analyze other statements. This is for statements
                // such as continue and break. Afterwards decrement the loop depth.
                self.loop_depth += 1;
                let bound_statement = self.analyze_statement(statement);
                self.loop_depth -= 1;
                BoundStatement::While {
                    expression,
                    statement: Box::new(bound_statement),
                }
            }
            Statement::Loop { statement, .. } => {
                // Increment the loop depth and analyze other statements. This is for statements
                // such as continue and break. Afterwards decrement the loop depth.
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
                // Analyze the "expr" in "while(expr)" and make sure it's a boolean type.
                let expression = self
                    .analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position))
                    .1;

                // Increment the loop depth and analyze other statements. This is for statements
                // such as continue and break. Afterwards decrement the loop depth.
                self.loop_depth += 1;
                let statement = self.analyze_statement(statement);
                self.loop_depth -= 1;
                BoundStatement::DoWhile {
                    expression,
                    statement: Box::new(statement),
                }
            }
            Statement::Continue { position } => {
                // Make sure we are in some loop to continue in.
                if self.loop_depth == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_continue_placement(*position);
                }
                BoundStatement::Continue
            }
            Statement::Break { position } => {
                // Make sure we are in some loop to break in.
                if self.loop_depth == 0 {
                    self.error_diag
                        .borrow_mut()
                        .invalid_break_placement(*position);
                }
                BoundStatement::Break
            }
            Statement::Block { block, .. } => {
                // Block is just a vector of statements to the emitter.
                let statements = self.analyze_block(block);
                BoundStatement::Statements(statements)
            }
            Statement::Bye {
                expression,
                position,
            } => {
                let function_descriptor = self.symbol_table().current_function();
                if let Some(function_descriptor) = function_descriptor {
                    let return_type = function_descriptor.return_type();

                    // "Bye" can hold some expression if the return type of the function
                    // has anything other than nopp.
                    if let Some(expression) = expression {
                        let expression = self.analyze_expr(expression, None, None);
                        self.check_data_type(return_type, expression.0.as_ref(), *position);
                        let return_type_size = expression.0.map_or(0, |data_type| data_type.size());
                        return BoundStatement::Bye {
                            return_type_size,
                            expression: Some(expression.1),
                        };
                    }

                    // It must be a nopp if there is no expression on bye.
                    if BoundDataType::Nopp != *return_type {
                        self.error_diag.borrow_mut().invalid_data_type(
                            *position,
                            &BoundDataType::Nopp,
                            return_type,
                        );
                    }
                    BoundStatement::Bye {
                        return_type_size: 0,
                        expression: None,
                    }
                } else {
                    // We are not in a function -> the statement shouldn't be here.
                    self.error_diag
                        .borrow_mut()
                        .invalid_bye_placement(*position);
                    BoundStatement::Bye {
                        return_type_size: 0,
                        expression: None,
                    }
                }
            }
            Statement::If {
                expression,
                statement,
                position,
            } => {
                // Analyze the "expr" in "if(expr)" and make sure it's a boolean type.
                let expression =
                    self.analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position));

                // Then just analyze the statement that happens in the if statement.
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
                // IfElse is very similar to If.
                // Analyze the "expr" in "if(expr)" and make sure it's a boolean type.
                let expression =
                    self.analyze_expr(expression, Some(&BoundDataType::Booba), Some(*position));
                // Then just analyze the statement that happens in the if statement.
                let statement = self.analyze_statement(statement);

                // Finally, analyze the else statement.
                let else_statement = self.analyze_statement(else_statement);
                BoundStatement::IfElse {
                    expression: expression.1,
                    statement: Box::new(statement),
                    else_statement: Box::new(else_statement),
                }
            }
            Statement::Assignment {
                identifier,
                field_identifier,
                expression,
                array_index_expression,
                position,
            } => {
                // TODO: Implement indexing
                // Find the variable.
                let (level, var_decl) = self.symbol_table().find_variable_declaration(identifier);

                // If there is no variable there's nothing to analyze anymore.
                if var_decl.is_none() {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);
                    return BoundStatement::Empty;
                }
                let variable = var_decl.expect("A variable descriptor to be present.");

                // If the variable is declared const throw an error.
                if variable.has_modifier(Modifier::Const) {
                    self.error_diag
                        .borrow_mut()
                        .cannot_assign_to_const_variable(*position, identifier);
                }

                let data_type = variable.data_type();
                match data_type {
                    BoundDataType::Struct(struct_ident, _) => 's: {
                        // Special case for struct: we can access a field of the struct and
                        // assign something to it.
                        if field_identifier.is_none() {
                            break 's;
                        }

                        // We are indeed accessing a field.
                        let field_name =
                            field_identifier.expect("A field identifier to be present.");

                        // If we are accessing a field find the struct definition and make
                        // sure the field actually exists in it.
                        let (_, struct_def) =
                            self.symbol_table().find_struct_definition(struct_ident);

                        // If the struct does not exist
                        if struct_def.is_none() {
                            self.error_diag
                                .borrow_mut()
                                .struct_does_not_exist(*position, struct_ident);
                            return BoundStatement::Empty;
                        }

                        let struct_def = struct_def.expect("The struct definition to exist.");
                        let field = struct_def
                            .fields()
                            .iter()
                            .find(|field| field.ident() == field_name);
                        if field.is_none() {
                            self.error_diag.borrow_mut().struct_field_not_found(
                                *position,
                                struct_ident,
                                field_name,
                            );
                            return BoundStatement::Empty;
                        }

                        // The field exists, it's an assignment to a struct field.
                        let field = field.expect("The struct field to be present.");
                        let expression =
                            self.analyze_expr(expression, Some(field.data_type()), Some(*position));

                        if field.has_modifier(Modifier::Const) {
                            self.error_diag
                                .borrow_mut()
                                .cannot_assign_to_const_variable(*position, field_name);
                            return BoundStatement::Empty;
                        }

                        let offset = variable.stack_position() + field.offset();
                        let variable = BoundVariable::with_static_position(
                            level,
                            offset as i32,
                            field.data_type().clone(),
                            false,
                        );
                        return BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                            variable,
                            expression.1,
                        ));
                    }
                    BoundDataType::Array(inner, size) => 'arr: {
                        if array_index_expression.is_none() {
                            break 'arr;
                        }

                        // We are assigning to an array under some index.
                        let array_index_expression = array_index_expression
                            .as_ref()
                            .expect("The array index expression to be present.");

                        // Analyze the index expression. The data type must be pp.
                        let array_index_expression = self.analyze_expr(
                            array_index_expression,
                            Some(&BoundDataType::Pp),
                            Some(*position),
                        );

                        // Analyze the rhs expression. The data type must match the inner array
                        // data type.
                        let expression =
                            self.analyze_expr(expression, Some(inner), Some(*position));
                        let offset = variable.stack_position();

                        let variable = BoundVariable::with_dynamic_position(
                            level,
                            offset as i32,
                            array_index_expression.1,
                            *inner.clone(),
                            false,
                        );
                        return BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                            variable,
                            expression.1,
                        ));
                    }
                    _ => {}
                }

                // If there is an index expression present and the variable is not an array ->
                // throw an error.
                if array_index_expression.is_some() {
                    self.error_diag
                        .borrow_mut()
                        .variable_is_not_array(*position, *identifier);
                }

                // The variable is not a struct and we are accessing a field of it ->
                // throw an error.
                if let Some(field_identifier) = field_identifier {
                    self.error_diag.borrow_mut().variable_is_not_struct(
                        *position,
                        *identifier,
                        *field_identifier,
                    );
                }

                let expression = self.analyze_expr(expression, Some(data_type), Some(*position));
                let offset = variable.stack_position();
                let data_type = variable.data_type().clone();

                let variable =
                    BoundVariable::with_static_position(level, offset as i32, data_type, false);
                BoundStatement::VariableAssignment(BoundVariableAssignment::new(
                    variable,
                    expression.1,
                ))
            }
            Statement::Empty { .. } => BoundStatement::Empty, // Nothing to analyze here :)
            Statement::Switch {
                expression, cases, ..
            } => {
                // Analyze "expr" in "switch(expr)".
                // Calculate the data type of the expression and analyze each case. Make sure
                // the cases match the data type.
                let expression = self.analyze_expr(expression, None, None);
                if let Some(switch_data_type) = expression.0 {
                    BoundStatement::Switch {
                        expression: expression.1,
                        cases: self.analyze_cases(cases, Some(&switch_data_type)),
                    }
                } else {
                    // An error happened while analyzing the expression, no need to log anything
                    // here.
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
                // This is important because we would occupy the index variable that is
                // expected to be dropped once the for loop ends.
                self.symbol_table_mut().push_scope();

                // Declare the variable as pp.
                let data_type = self.to_bound_data_type(&DataType::Pp, *position);
                self.declare_variable(*position, Vec::new(), data_type.clone(), index_ident, false);

                // Check that the "ident expression" is pp or none in "for(ident_expression ...)".
                // If it's none the variable is treated as initialization to 0.
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

                // Get the descriptor of the variable.
                let (level, var_decl) = self.symbol_table().find_variable_declaration(index_ident);

                // This SHOULD be safe as we declared the variable earlier just now.
                let var_decl = var_decl.expect("The index variable already declared.");
                let offset = var_decl.stack_position();
                let is_const = var_decl.has_modifier(Modifier::Const);

                // Increment the loop stack for break, continue, etc. statements and analyze the
                // statements.
                self.loop_depth += 1;
                let bound_statement = self.analyze_statement(statement);
                self.loop_depth -= 1;

                // Pop the scope. This will drop the index variable.
                self.symbol_table_mut().pop_scope();

                let variable =
                    BoundVariable::with_static_position(level, offset as i32, data_type, is_const);
                BoundStatement::For {
                    variable,
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
        // Analyzing cases is simply analyzing their expression, comparing the data type to the
        // switch data type, and analyzing the blocks.
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
        // This is very important: each block is basically a new scope.
        self.symbol_table_mut().push_scope();
        let bound_statements = self.analyze_statements(block.statements());
        self.symbol_table_mut().pop_scope();
        bound_statements
    }

    fn analyze_statements(&mut self, statements: &Vec<Statement<'a>>) -> Vec<BoundStatement> {
        statements
            .iter()
            .map(|statement| self.analyze_statement(statement))
            .collect_vec()
    }

    fn analyze_expr(
        &self,
        expression: &Expression<'a>,
        expected_data_type: Option<&BoundDataType>,
        position: Option<(u32, u32)>,
    ) -> (Option<BoundDataType>, BoundExpression) {
        // Calculate the data type. If we expect some data type to be returned the expected data
        // type must be present. Then this function expects the position to be present as well.
        let data_type = self.calc_data_type(expression);
        if let Some(expected_data_type) = expected_data_type {
            let position = position.expect("The position of the expression to be present.");
            self.check_data_type(expected_data_type, data_type.as_ref(), position);
        }

        (data_type, self.expr(expression))
    }

    /// # Summary
    /// Analyzes the expression. This function is the core of the semantic analyzer. It analyzes
    /// the expression and returns the data type of the expression. If the expression is invalid
    /// then it returns None. This function is recursive and will analyze the sub-expressions
    /// of the expression.
    ///
    /// This function ONLY analyzes the data types. If the data type could not be calculated,
    /// `None` is returned. If the data type is incorrect it will add an error message, but STILL
    /// return the data type that was calculated as if nothing happened. This is for better error
    /// diagnostics.
    ///
    /// # Arguments
    ///
    /// * `expression`: the expression to analyze
    /// # Returns
    /// `Option<DataType>` - the data type of the expression if it is valid, None otherwise
    fn calc_data_type(&self, expr: &Expression<'a>) -> Option<BoundDataType> {
        return match expr {
            // A literal expression is basically the base case of this recursive call. WE just
            // map it to the data type the literal value presents.
            Expression::Literal { value, .. } => Some(match value {
                LiteralValue::Pp(_) => BoundDataType::Pp,
                LiteralValue::Flaccid(_, _) => BoundDataType::Flaccid,
                LiteralValue::AB(_, _) => BoundDataType::AB,
                LiteralValue::P(_) => BoundDataType::P,
                LiteralValue::Booba(_) => BoundDataType::Booba,
                LiteralValue::Yarn(_) => BoundDataType::Yarn,
                _ => todo!("SIGH"),
            }),
            Expression::Unary {
                operand,
                op,
                position,
            } => {
                let data_type = self.calc_data_type(operand)?;
                return match op {
                    // Not is "!".
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
                    // Negate is "-".
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

                // For binary expressions we don't allow mixing.
                self.check_if_mixed_data_types(&lhs_data_type, &rhs_data_type, *position);
                // TODO: Check whether the binary operator is available for the given data type.
                use crate::parse::parser::BinaryOperator::{
                    Add, And, Divide, Equal, GreaterThan, GreaterThanOrEqual, LessThan,
                    LessThanOrEqual, Multiply, NotEqual, Or, Subtract,
                };

                // Now we need to decide the data type. Any arithmetic expression should return
                // the expression either on the lhs or rhs (it shouldn't matter). Any boolean
                // expression, such as comparison, should return the booba data type.
                match op {
                    Add | Subtract | Multiply | Divide => Some(lhs_data_type),
                    NotEqual | Equal | GreaterThan | GreaterThanOrEqual | LessThan
                    | LessThanOrEqual | And | Or => Some(BoundDataType::Booba),
                }
            }
            Expression::Identifier { identifier, .. } => {
                // For identifier expression we just need to make sure the identifier exists.
                // Just find the variable declaration and, if present, map the result to its data
                // type.
                // Return None if it doesn't exist as we can't determine the data type.
                self.symbol_table()
                    .find_variable_declaration(identifier)
                    .1
                    .map(|variable| variable.data_type().clone())
            }
            Expression::FunctionCall { identifier, .. } => {
                // For function calls we just need to make sure the called function exists.
                // Just find the function declaration and, if present, map the result to its
                // return type.
                // Return None if it doesn't exist as we can't determine the data type.
                self.symbol_table()
                    .find_function_definition(identifier)
                    .map(|function| function.return_type().clone())
            }
            Expression::Struct { identifier, .. } => {
                // For struct we need to find the definition.
                let struct_def = self.symbol_table().find_struct_definition(*identifier);
                if let Some(struct_def) = struct_def.1 {
                    Some(BoundDataType::Struct(
                        String::from(*identifier),
                        struct_def.size(),
                    ))
                } else {
                    Some(BoundDataType::Struct(String::from(*identifier), 0))
                }
            }
            Expression::StructFieldAccess { identifiers, .. } => {
                // The first identifier is the struct identifier. It must be present.
                let struct_identifier = identifiers
                    .get(0)
                    .expect("The struct identifier to be present.");

                // TODO: There is only one field identifier for now. One field must
                // be present.
                let field_identifier = identifiers
                    .get(1)
                    .expect("The field identifier to be present.");

                // Get the variable declaration and type the data type to struct.
                let var_decl = self
                    .symbol_table()
                    .find_variable_declaration(struct_identifier);
                if let Some(var_decl) = var_decl.1 {
                    if let BoundDataType::Struct(ident, _) = var_decl.data_type() {
                        // Find the struct declaration.
                        let struct_decl = self.symbol_table().find_struct_definition(ident);
                        if let Some(struct_decl) = struct_decl.1 {
                            // Find the struct field and return its data type.
                            if let Some(field) = struct_decl
                                .fields()
                                .iter()
                                .find(|field| field.ident() == *field_identifier)
                            {
                                return Some(field.data_type().clone());
                            }
                        }
                    }
                }

                // If anything goes wrong we aren't able to determine the data type, so just
                // return None.
                None
            }
            Expression::ArrayAccess { identifier, .. } => {
                // Find the variable. If present
                self.symbol_table()
                    .find_variable_declaration(identifier)
                    .1
                    .map(|variable| {
                        // Get the inner data type of the array.
                        // I.e. pp[5] -> a; a[0] should return pp instead of array.
                        if let BoundDataType::Array(inner, _) = variable.data_type() {
                            return *inner.clone();
                        }

                        // If it's not array just return the data type.
                        variable.data_type().clone()
                    })
            }
            _ => todo!("Calculate data type for {expr:?}"),
        };
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
                _ => panic!("lol"),
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
                // Find the variable declaration and its relative level.
                let (level, var_decl) = self.symbol_table().find_variable_declaration(identifier);
                // The variable will always have a static position.
                if let Some(variable) = var_decl {
                    BoundExpression::Variable(BoundVariable::with_static_position(
                        level,
                        variable.stack_position() as i32,
                        variable.data_type().clone(),
                        variable.has_modifier(Modifier::Const),
                    ))
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, identifier);

                    BoundExpression::Variable(BoundVariable::with_static_position(
                        0,
                        0,
                        BoundDataType::Pp,
                        true,
                    ))
                }
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                position,
            } => {
                if let Some(function) = self.symbol_table().find_function_definition(identifier) {
                    let id = function.id();
                    let return_type_size = function.return_type().size();
                    let parameters_size = function.parameters_size();

                    // Make sure the function call has the right amount of arguments.
                    if function.parameters().len() != arguments.len() {
                        self.error_diag.borrow_mut().invalid_number_of_arguments(
                            *position,
                            *identifier,
                            parameters_size,
                            arguments.len(),
                        );
                    }

                    // Make sure the arguments have correct data type.
                    let arguments = arguments
                        .iter()
                        .zip(function.parameters())
                        .map(|(arg, param)| {
                            self.analyze_expr(arg, Some(param.data_type()), Some(arg.position()))
                                .1
                        })
                        .collect_vec();

                    BoundExpression::FunctionCall {
                        level: 1,
                        identifier: id,
                        return_type_size,
                        arguments_size: parameters_size,
                        arguments,
                    }
                } else {
                    self.error_diag
                        .borrow_mut()
                        .function_does_not_exist(*position, identifier);

                    BoundExpression::FunctionCall {
                        level: 1,
                        identifier: 0,
                        return_type_size: 0,
                        arguments_size: 0,
                        arguments: Vec::new(),
                    }
                }
            }
            Expression::Invalid { .. } => {
                unreachable!("Should have thrown syntax error after parsing")
            }
            Expression::Struct {
                position,
                field_assignments,
                identifier,
            } => {
                let struct_def = self.symbol_table().find_struct_definition(*identifier).1;

                return if let Some(struct_def) = struct_def {
                    // If the definition is present make sure we get the right amount of fields.
                    let expected_len = struct_def.fields().len();
                    let got_len = field_assignments.len();
                    if expected_len != got_len {
                        self.error_diag
                            .borrow_mut()
                            .struct_declaration_invalid_field_amount(
                                expression.position(),
                                identifier,
                                expected_len,
                                got_len,
                            )
                    }

                    // Zip the field assignments in the expression and the defined fields in the
                    // struct and analyze the expressions.
                    let fields = field_assignments
                        .iter()
                        .zip(struct_def.fields())
                        .map(|(field_assignment, field)| {
                            let bound_expr = self.analyze_expr(
                                field_assignment.expression(),
                                Some(field.data_type()),
                                Some(field_assignment.position()),
                            );
                            BoundStructFieldAssignment::new(bound_expr.1)
                        })
                        .collect_vec();

                    BoundExpression::Struct(fields)
                } else {
                    self.error_diag
                        .borrow_mut()
                        .struct_does_not_exist(*position, *identifier);
                    BoundExpression::Struct(Vec::new())
                };
            }
            Expression::StructFieldAccess {
                position,
                identifiers,
            } => {
                let default_value = BoundExpression::StructFieldAccess(
                    BoundVariable::with_static_position(0, 0, BoundDataType::Nopp, false),
                );

                let struct_identifier = identifiers
                    .get(0)
                    .expect("The struct identifier to be present.");
                let field_identifier = identifiers
                    .get(1)
                    .expect("The field identifier to be present.");

                let variable_descr = self
                    .symbol_table()
                    .find_variable_declaration(*struct_identifier);
                let level = variable_descr.0;

                // Find the variable, then type the data type to struct. Find the field and
                // return its data type.
                if variable_descr.1.is_none() {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, struct_identifier);
                    return default_value;
                }

                let variable_descr = variable_descr
                    .1
                    .expect("The variable descriptor to be present.");
                match variable_descr.data_type() {
                    BoundDataType::Struct(ident, _) => {
                        let struct_descr = self.symbol_table().find_struct_definition(ident);
                        if struct_descr.1.is_none() {
                            self.error_diag
                                .borrow_mut()
                                .struct_does_not_exist(*position, struct_identifier);
                            return default_value;
                        }

                        let struct_descr = struct_descr
                            .1
                            .expect("The struct descriptor to be present.");
                        let field = struct_descr
                            .fields()
                            .iter()
                            .find(|field| field.ident() == *field_identifier);
                        if field.is_none() {
                            self.error_diag.borrow_mut().struct_field_not_found(
                                *position,
                                *struct_identifier,
                                *field_identifier,
                            );
                            return default_value;
                        }

                        let field = field.expect("The field to be present.");
                        let stack_pos = variable_descr.stack_position();
                        let field_off = field.offset();
                        return BoundExpression::StructFieldAccess(
                            BoundVariable::with_static_position(
                                level,
                                (stack_pos + field_off) as i32,
                                field.data_type().clone(),
                                false,
                            ),
                        );
                    }
                    _ => self.error_diag.borrow_mut().invalid_data_type(
                        *position,
                        &BoundDataType::Struct(String::from(*struct_identifier), 0),
                        variable_descr.data_type(),
                    ),
                }

                default_value
            }
            Expression::ArrayAccess {
                position,
                identifier,
                array_index_expression,
            } => {
                let (level, var_decl) = self.symbol_table().find_variable_declaration(identifier);
                let (_, bound_index_expr) = self.analyze_expr(
                    array_index_expression,
                    Some(&BoundDataType::Pp),
                    Some(*position),
                );

                if let Some(var_descr) = var_decl {
                    if let BoundDataType::Array(inner, size) = var_descr.data_type() {
                        return BoundExpression::ArrayAccess(
                            BoundVariable::with_dynamic_position(
                                level,
                                var_descr.stack_position() as i32,
                                bound_index_expr,
                                *inner.clone(),
                                false,
                            ),
                            *size,
                        );
                    } else {
                        self.error_diag.borrow_mut().invalid_data_type(
                            *position,
                            &BoundDataType::Array(Box::new(BoundDataType::Nopp), 0),
                            var_descr.data_type(),
                        )
                    }
                } else {
                    self.error_diag
                        .borrow_mut()
                        .variable_not_found(*position, *identifier);
                }
                BoundExpression::ArrayAccess(
                    BoundVariable::with_static_position(0, 0, BoundDataType::Nopp, false),
                    0,
                )
            }
        }
    }
}
