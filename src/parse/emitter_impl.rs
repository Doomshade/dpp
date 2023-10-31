use dpp_macros::Pos;

use crate::parse::analysis::{
    BoundExpression, BoundFunction, BoundStatement, BoundTranslationUnit, BoundVariableAssignment,
};
use crate::parse::emitter::{Address, DebugKeyword, Instruction, OperationType};
use crate::parse::parser::{BinaryOperator, UnaryOperator};
use crate::parse::Emitter;

impl<'a, 'b> Emitter<'a, 'b> {
    /// # Summary
    /// Emits the translation unit.
    ///
    /// # Arguments
    ///
    /// * `translation_unit`: the translation unit
    pub(crate) fn emit_translation_unit(&mut self, translation_unit: &BoundTranslationUnit) {
        self.emit_global_scope(translation_unit);
        self.emit_main_call(translation_unit.main_function_identifier());
        self.emit_functions(translation_unit);
    }

    fn emit_global_scope(&mut self, translation_unit: &BoundTranslationUnit) {
        self.create_stack_frame(translation_unit.global_stack_frame_size());
        self.emit_global_variables(translation_unit);
    }

    fn emit_global_variables(&mut self, translation_unit: &BoundTranslationUnit) {
        translation_unit
            .global_variable_assignments()
            .iter()
            .for_each(|stmt| self.emit_variable_assignment(stmt));
    }

    fn emit_functions(&mut self, translation_unit: &BoundTranslationUnit) {
        translation_unit
            .functions()
            .iter()
            .for_each(|func| self.emit_function(func))
    }

    /// # Summary
    /// Emits the function.
    ///
    /// # Arguments
    ///
    /// * `function`: the function
    fn emit_function(&mut self, function: &BoundFunction) {
        self.emit_label(Self::create_function_label(function.identifier()));

        // Shift the stack pointer by activation record + declared variable count.
        self.create_stack_frame(function.stack_frame_size());

        // Load arguments.
        let mut store_offset = 3;
        function.parameters().iter().for_each(|var| {
            self.load_variable(var);
            self.store(0, store_offset);
            store_offset += 1;
        });
        function
            .statements()
            .iter()
            .for_each(|statement| self.emit_statement(statement, None, None));

        // We aren't forcing the return statement if it's nopp, so we'll emit it ourselves.
        if function.return_size() == 0 {
            self.emit_instruction(Instruction::Return);
        }

        self.emit_debug_info(DebugKeyword::StackA);
    }

    fn emit_variable_assignment(&mut self, variable: &BoundVariableAssignment) {
        self.emit_expression(variable.value());
        self.store_variable(variable.position());
    }

    /// # Summary
    /// Emits the statement. The label arguments are used for Continue and Break statements,
    /// respectively. The initial call to this will very likely have None for both arguments. For
    /// example the For statement will call this with start and end labels -- the comparison
    /// label and the end of the for loop label.
    ///
    /// # Arguments
    ///
    /// * `statement`: the statement to emit
    /// * `start_label`: the start label of the statement
    /// * `end_label`: the end label of the statement
    ///
    fn emit_statement(
        &mut self,
        statement: &BoundStatement,
        start_label: Option<String>,
        end_label: Option<String>,
    ) {
        match statement {
            BoundStatement::Expression { 0: expression, .. } => {
                self.emit_expression(expression);
            }
            BoundStatement::VariableAssignment { 0: variable, .. } => {
                self.emit_variable_assignment(variable);
            }
            BoundStatement::Bye {
                expression,
                return_offset,
            } => {
                if let Some(expression) = expression {
                    self.emit_expression(expression);
                    self.store(0, *return_offset);
                }
                self.emit_instruction(Instruction::Return);
            }
            BoundStatement::While {
                expression,
                statement,
                ..
            } => {
                let start = self.create_control_label();
                let end = self.create_control_label();

                self.emit_label(start.clone());
                self.emit_expression(expression);
                self.emit_jmc(Address::Label(end.clone()));
                self.emit_statement(statement, Some(start.clone()), Some(end.clone()));
                self.emit_jump(Address::Label(start));
                self.emit_label(end);
            }
            BoundStatement::For {
                ident_position,
                ident_expression,
                length_expression,
                statement,
            } => {
                let cmp_label = self.create_control_label();
                let end = self.create_control_label();

                // Create a new variable for the for loop and store its value.
                if let Some(expression) = ident_expression {
                    self.emit_expression(expression);
                } else {
                    self.emit_literal(0);
                }
                self.store_variable(ident_position);

                // Compare the variable with the length.
                self.emit_label(cmp_label.clone());
                self.load_variable(ident_position);
                self.emit_expression(length_expression);
                self.emit_operation(OperationType::LessThan);
                self.emit_jmc(Address::Label(end.clone()));

                // Emit the for statement.
                self.emit_statement(statement, Some(cmp_label.clone()), Some(end.clone()));

                // Increment i.
                self.load_variable(ident_position);
                self.emit_literal(1);
                self.emit_operation(OperationType::Add);
                self.store_variable(ident_position);
                self.emit_jump(Address::Label(cmp_label.clone()));
                self.emit_label(end.clone());
            }

            BoundStatement::Empty { .. } => {
                // Emit nothing I guess :)
            }
            BoundStatement::If {
                expression,
                statement,
            } => {
                let end = self.create_control_label();

                self.emit_expression(expression);
                self.emit_jmc(Address::Label(end.clone()));
                self.emit_statement(statement, start_label, end_label);
                self.emit_label(end);
            }
            BoundStatement::IfElse {
                expression,
                statement,
                else_statement,
                ..
            } => {
                let end_if = self.create_control_label();
                let else_block_label = self.create_control_label();

                self.emit_expression(expression);
                self.emit_jmc(Address::Label(else_block_label.clone()));
                self.emit_statement(statement, start_label.clone(), end_label.clone());
                self.emit_jump(Address::Label(end_if.clone()));
                self.emit_label(else_block_label);
                self.emit_statement(else_statement, start_label, end_label);
                self.emit_label(end_if);
            }
            BoundStatement::Continue { .. } => {
                self.emit_jump(Address::Label(start_label.unwrap().to_string()));
            }
            BoundStatement::Break { .. } => {
                self.emit_jump(Address::Label(end_label.unwrap().to_string()));
            }
            BoundStatement::Statements(statements) => {
                statements.iter().for_each(|statement| {
                    self.emit_statement(statement, start_label.clone(), end_label.clone())
                });
            }
            _ => self
                .error_diag
                .borrow_mut()
                .not_implemented((0, 0), format!("statement {:?}", statement).as_str()),
        };
    }

    /// # Summary
    /// Emits the expression.
    ///
    /// # Arguments
    ///
    /// * `expression`: the expression
    fn emit_expression(&mut self, expression: &BoundExpression) {
        match expression {
            BoundExpression::Number { value, .. } => {
                self.emit_literal(*value);
            }
            BoundExpression::P { 0: p, .. } => {
                self.emit_literal(*p as i32);
            }
            BoundExpression::Booba { 0: booba, .. } => {
                self.emit_literal(i32::from(*booba));
            }
            BoundExpression::Yarn { 0: yarn, .. } => {
                self.emit_literal(yarn.len() as i32);
                // Self::pack_yarn(yarn)
                //     .into_iter()
                //     .for_each(|four_packed_chars| self.emit_literal(four_packed_chars));
            }
            BoundExpression::Binary { lhs, rhs, op, .. } => {
                // Ok so this is a little complicated, but bear with me:
                // We need to check what kind of binary operator we have.
                // If it's a boolean operator we need to treat it VERY differently.
                // We emit the lhs and compare it with true value.
                //     AND: if any value is false, we jump to short-circuit code and emit false
                //     OR : if any value is true, we jump to short-circuit code and emit true
                //     AND: if no value is false we jump to the end of the expression and emit true
                //     OR : if no value is true we jump to the end of the expression and emit false
                // In essence what happens:
                // yem && yem && nom && yem && yem && yem
                // this is parsed as
                // (((((yem && yem) && nom) && yem) && yem) && yem)
                //      ^^^    ^^^
                // So we first compare these two and then the result with "nom".
                // 1. compare value at the top of the stack. emit true, ok, continue, emit rhs
                // 2. compare value at the top of the stack. emit true, ok, continue, emit rhs
                // 3. compare value at the top of the stack. emit false, OOF, jump to short-circuit
                // code and ***emit false***
                // 4. compare value at the top of the stack. emit false, OOF, jump to short-circuit
                // code and emit false
                // 5. ...
                // 6. ...
                // IMPORTANT: the last value is false because of the short-circuit!
                //
                // Similar thing happens to OR, except we emit false instead of true and short
                // circuit on true.
                use BinaryOperator as BinOp;
                use OperationType as Op;
                self.emit_expression(lhs);
                let after_expr_label;
                let short_circuit_label;
                match op {
                    BinOp::And | BinOp::Or => {
                        short_circuit_label = Some(self.create_control_label());
                        after_expr_label = Some(self.create_control_label());
                        self.emit_binary_boolean_expression(
                            op,
                            short_circuit_label.clone().unwrap().as_str(),
                        );
                    }
                    _ => {
                        after_expr_label = None;
                        short_circuit_label = None;
                    }
                }
                self.emit_expression(rhs);
                match op {
                    BinOp::Add => self.emit_operation(Op::Add),
                    BinOp::Subtract => self.emit_operation(Op::Subtract),
                    BinOp::Multiply => self.emit_operation(Op::Multiply),
                    BinOp::Equal => self.emit_operation(Op::Equal),
                    BinOp::GreaterThan => self.emit_operation(Op::GreaterThan),
                    BinOp::NotEqual => self.emit_operation(Op::NotEqual),
                    BinOp::LessThanOrEqual => self.emit_operation(Op::LessThanOrEqualTo),
                    BinOp::GreaterThanOrEqual => self.emit_operation(Op::GreaterThanOrEqualTo),
                    BinOp::Divide => self.emit_operation(Op::Divide),
                    BinOp::LessThan => self.emit_operation(Op::LessThan),
                    BinOp::And | BinOp::Or => {
                        self.emit_binary_boolean_expression(
                            op,
                            short_circuit_label.clone().unwrap().as_str(),
                        );
                    }
                };

                // If we reached at the end of the expression we DID not short-circuit (see below).
                // If we don't short-circuit AND it means the value is true.
                // If we don't short-circuit OR it means the value is false.
                if after_expr_label.is_some() {
                    match op {
                        BinaryOperator::And => self.emit_booba(true),
                        BinaryOperator::Or => self.emit_booba(false),
                        _ => {}
                    };

                    // Jump to the END of the expression because below this is the short
                    // circuiting code.
                    self.emit_jump(Address::Label(after_expr_label.clone().unwrap()));
                }

                // If we short-circuit the boolean expression we need to emit the value of the
                // expression. For AND short-circuiting it means we found a false value. For OR it
                // means we found a true value.
                //
                // If we short-circuit AND it means the value is false.
                // If we short-circuit OR it means the value is true.
                if let Some(label) = short_circuit_label {
                    self.emit_label(label);
                    match op {
                        BinaryOperator::And => self.emit_booba(false),
                        BinaryOperator::Or => self.emit_booba(true),
                        _ => {}
                    };
                }

                // We jump here if the expression is not short-circuited.
                if let Some(label) = after_expr_label {
                    self.emit_label(label);
                }
            }
            BoundExpression::Variable { 0: position, .. } => {
                self.load_variable(position);
            }
            BoundExpression::FunctionCall {
                level,
                arguments,
                arguments_size,
                identifier,
                return_type_size,
            } => {
                self.emit_function_call(
                    *level,
                    arguments,
                    *arguments_size,
                    *identifier,
                    *return_type_size,
                );
            }
            BoundExpression::Unary { op, operand, .. } => {
                self.emit_expression(operand);
                match op {
                    UnaryOperator::Not => {
                        self.emit_booba(true);
                        self.emit_operation(OperationType::NotEqual);
                    }
                    UnaryOperator::Negate => self.emit_operation(OperationType::Negate),
                }
            }
            _ => todo!("Not implemented {expression:?}"),
        }
    }

    /// # Summary
    /// Helper function that emits a booba value.
    ///
    /// # Arguments
    ///
    /// * `value`: the booba value
    fn emit_booba(&mut self, value: bool) {
        self.emit_expression(&BoundExpression::Booba(value));
    }

    /// # Summary
    /// Emits the binary boolean expression. If the expression on top of stack is false and the
    /// operator is AND or if it's true and the operator is OR we jump to the short circuit label.
    ///
    /// # Arguments
    ///
    /// * `binop`: the binary operator -- can either be AND or OR
    /// * `short_circuit_label`: the short circuit label
    fn emit_binary_boolean_expression(
        &mut self,
        binop: &BinaryOperator,
        short_circuit_label: &str,
    ) {
        match binop {
            BinaryOperator::And => {
                // Compare the value to true.
                self.emit_booba(true);
                self.emit_operation(OperationType::Equal);

                // Need to create a value for JMC instruction for AND.
                self.emit_booba(true);
                self.emit_operation(OperationType::Equal);

                // If the value is FALSE stop executing the rest of the expression.
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(short_circuit_label.to_string()),
                });
            }
            BinaryOperator::Or => {
                // Compare the value to true.
                self.emit_booba(true);
                self.emit_operation(OperationType::Equal);

                // Need to create a value for JMC instruction for OR.
                self.emit_booba(true);
                self.emit_operation(OperationType::NotEqual);

                // If the value is TRUE stop executing the rest of the expression.
                self.emit_jmc(Address::Label(short_circuit_label.to_string()));
            }
            _ => {
                unreachable!();
            }
        }
    }

    /// # Summary
    /// Emits a function call. This will reserve space on the stack for the return value and
    /// store the arguments on the stack. Afterwards, the function is called. The called function
    /// then stores the result value (if any) in the reserved space. Lastly, the arguments are
    /// popped off the stack.
    ///
    /// # Arguments
    ///
    /// * `arguments`: the arguments
    /// * `identifier`: the function identifier
    fn emit_function_call(
        &mut self,
        level: usize,
        arguments: &Vec<BoundExpression>,
        arguments_size: usize,
        identifier: usize,
        return_type_size: usize,
    ) {
        // Allocate extra space on the stack for the return value.
        self.emit_int(return_type_size as i32);

        // Emit arguments.
        for argument in arguments {
            self.emit_expression(argument);
        }

        // Call the function.
        self.emit_call(
            level,
            Address::Label(Self::create_function_label(identifier)),
        );

        // Pop the arguments.
        self.emit_int(-(arguments_size as i32));
    }

    /// # Summary
    /// Emits the function call to the main function. It also emits the JMP 0 0 instruction to
    /// exit the program once the main function is done.
    fn emit_main_call(&mut self, main_function_identifier: usize) {
        self.echo("Calling main function.");
        let main_function_call = BoundExpression::FunctionCall {
            arguments_size: 0,
            identifier: main_function_identifier,
            return_type_size: 1,
            level: 0,
            arguments: Vec::new(),
        };
        self.emit_expression(&main_function_call);

        // The last instruction is return -- indicating exit.
        self.echo("Program returned with return value:");
        self.emit_debug_info(DebugKeyword::StackN { amount: 1 });
        self.emit_instruction(Instruction::Return);
    }

    fn pack_yarn(yarn: &str) -> Vec<i32> {
        let mut vec: Vec<i32> = Vec::with_capacity((yarn.len() / 4) + 1);
        for chunk in yarn.as_bytes().chunks(4) {
            let packed_chars = match chunk.len() {
                1 => i32::from(chunk[0]),
                2 => i32::from(chunk[1]) << 8 | i32::from(chunk[0]),
                3 => i32::from(chunk[2]) << 16 | i32::from(chunk[1]) << 8 | i32::from(chunk[0]),
                4 => {
                    i32::from(chunk[3]) << 24
                        | i32::from(chunk[2]) << 16
                        | i32::from(chunk[1]) << 8
                        | i32::from(chunk[0])
                }
                _ => unreachable!(),
            };
            // println!("{:#010x}", &packed_chars);

            vec.push(packed_chars);
        }
        vec
    }
}
