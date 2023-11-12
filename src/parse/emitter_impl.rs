use dpp_macros::Pos;
use std::env::var;

use crate::parse::analysis::{
    BoundExpression, BoundFunction, BoundLiteralValue, BoundStatement, BoundTranslationUnit,
    BoundVariable, BoundVariableAssignment, BoundVariablePosition, Scope,
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

    fn load_variable(&mut self, variable: &BoundVariable) {
        match variable.position() {
            BoundVariablePosition::Static(level, offset) => {
                self.load(*level, *offset, variable.size())
            }
            BoundVariablePosition::Dynamic(level, base_offset, relative_offset) => {
                for i in 0..variable.size() {
                    self.emit_value(&BoundLiteralValue::Pp(*level as i32));
                    self.emit_relative_offset(
                        *base_offset,
                        relative_offset,
                        variable.data_type().size(),
                    );
                    self.emit_value(&BoundLiteralValue::Pp(i as i32));
                    self.emit_operation(OperationType::Add);
                    self.emit_instruction(Instruction::Pld);
                }
            }
        }
    }

    fn store_variable(&mut self, variable: &BoundVariable) {
        match variable.position() {
            BoundVariablePosition::Static(level, offset) => {
                self.store(*level, *offset, variable.size())
            }
            BoundVariablePosition::Dynamic(level, base_offset, relative_offset) => {
                for i in (0..variable.size()).rev() {
                    self.emit_value(&BoundLiteralValue::Pp(*level as i32));
                    self.emit_relative_offset(
                        *base_offset,
                        relative_offset,
                        variable.data_type().size(),
                    );
                    self.emit_value(&BoundLiteralValue::Pp(i as i32));
                    self.emit_operation(OperationType::Add);

                    self.emit_instruction(Instruction::Sta);
                }
            }
        }
    }

    fn emit_relative_offset(
        &mut self,
        base_offset: i32,
        relative_offset: &BoundExpression,
        data_type_size: usize,
    ) {
        // For example a variable on offset 4 named "a", data type of size 2
        // and we need to retrieve a[1 + 2].
        //
        // base_offset: 4
        // relative offset: 1 + 2
        // data type size: 2
        //
        // offset = base_offset + relative_offset * data_type_size
        // offset = 4 + (1 + 2) * 2
        // offset = 4 + 3 * 2
        // offset = 10
        // X = 0 10
        // [ | | | |a| | | | | |X|...]
        self.emit_value(&BoundLiteralValue::Pp(base_offset));

        self.emit_expression(relative_offset);
        self.emit_value(&BoundLiteralValue::Pp(data_type_size as i32));
        self.emit_operation(OperationType::Multiply);
        self.emit_operation(OperationType::Add);
    }

    fn emit_global_scope(&mut self, translation_unit: &BoundTranslationUnit) {
        self.create_stack_frame(translation_unit.global_stack_frame_size());
        self.emit_global_variables(translation_unit);
    }

    fn emit_global_variables(&mut self, translation_unit: &BoundTranslationUnit) {
        translation_unit
            .global_variable_assignments()
            .iter()
            .for_each(|stmt| self.emit_statement(stmt, None, None));
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
        self.create_stack_frame(function.stack_frame_size());
        // We expect the arguments to be loaded on stack by the callee, no need to load them.

        // Emit the statements.
        function
            .statements()
            .iter()
            .for_each(|statement| self.emit_statement(statement, None, None));

        // We aren't forcing the function to have a return statement if it's nopp, so we'll emit it
        // ourselves.
        if function.return_size() == 0 {
            self.emit_instruction(Instruction::Return);
        }
    }

    fn emit_variable_assignment(&mut self, assignment: &BoundVariableAssignment) {
        self.emit_expression(assignment.value());
        self.store_variable(assignment.variable());
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
                return_type_size,
            } => {
                if let Some(expression) = expression {
                    self.emit_expression(expression);
                    self.store(0, -(*return_type_size as i32), *return_type_size);
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
                variable: ident_position,
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
                    self.emit_value(&BoundLiteralValue::Pp(0));
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
                self.emit_value(&BoundLiteralValue::Pp(1));
                self.emit_operation(OperationType::Add);
                self.store_variable(ident_position);

                self.emit_jump(Address::Label(cmp_label.clone()));
                self.emit_label(end.clone());
            }

            BoundStatement::Empty => {
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
            BoundStatement::Continue => {
                self.emit_jump(Address::Label(start_label.unwrap().to_string()));
            }
            BoundStatement::Break => {
                self.emit_jump(Address::Label(end_label.unwrap().to_string()));
            }
            BoundStatement::Statements(statements) => {
                for statement in statements.iter() {
                    self.emit_statement(statement, start_label.clone(), end_label.clone())
                }
            }
            BoundStatement::Switch { expression, cases } => {
                let switch_end_label = self.create_control_label();
                for case in cases.iter() {
                    let end_case = self.create_control_label();

                    // Compare the case statement with the expression.
                    self.emit_expression(expression);
                    self.emit_expression(case.expression());
                    self.emit_operation(OperationType::Equal);

                    // If it's not ok, jump to the next case which is after statement.
                    self.emit_jmc(Address::Label(end_case.clone()));
                    case.statements()
                        .iter()
                        .for_each(|statement| self.emit_statement(statement, None, None));
                    self.emit_jump(Address::Label(switch_end_label.clone()));
                    self.emit_label(end_case.clone());
                }
                self.emit_label(switch_end_label);
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
            BoundExpression::Literal(value) => self.emit_value(value),
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
                    BinOp::And => {
                        self.emit_operation(Op::Multiply);

                        // Clamp the boolean expression.
                        self.emit_value(&BoundLiteralValue::Pp(0));
                        self.emit_operation(Op::NotEqual);
                    }
                    BinOp::Or => {
                        self.emit_operation(Op::Add);

                        // Clamp the boolean expression.
                        self.emit_value(&BoundLiteralValue::Pp(0));
                        self.emit_operation(Op::NotEqual);
                    }
                };
            }
            BoundExpression::Variable(variable) => {
                self.load_variable(variable);
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
            BoundExpression::Struct(fields) => {
                for field in fields {
                    self.emit_expression(field.expression());
                }
            }
            BoundExpression::StructFieldAccess(variable) => {
                self.load_variable(variable);
            }
            BoundExpression::ArrayAccess(variable, array_size) => {
                if let BoundVariablePosition::Dynamic(level, base_offset, dynamic_offset) =
                    variable.position()
                {
                    self.emit_variable_level(variable.position());

                    self.emit_expression(dynamic_offset);
                    // TODO: Could add a check here for IOOB.
                    self.emit_value(&BoundLiteralValue::Pp(variable.data_type().size() as i32));
                    self.emit_operation(OperationType::Multiply);
                    self.emit_variable_offset(variable.position());
                    self.emit_operation(OperationType::Add);
                    self.emit_instruction(Instruction::Pld);
                }
            }
            _ => todo!("Not implemented {expression:?}"),
        }
    }

    fn emit_variable_level(&mut self, position: &BoundVariablePosition) {
        match position {
            BoundVariablePosition::Dynamic(level, _, _) => {
                self.emit_value(&BoundLiteralValue::Pp(*level as i32))
            }
            _ => panic!("Expected a dynamic variable position."),
        }
    }

    fn emit_variable_offset(&mut self, position: &BoundVariablePosition) {
        match position {
            BoundVariablePosition::Dynamic(_, base_offset, dynamic_offset) => {
                self.emit_expression(dynamic_offset);
            }
            _ => panic!("Expected a dynamic variable position."),
        }
    }

    /// # Summary
    /// Helper function that emits a booba value.
    ///
    /// # Arguments
    ///
    /// * `value`: the booba value
    fn emit_booba(&mut self, value: bool) {
        self.emit_expression(&BoundExpression::Literal(BoundLiteralValue::Booba(value)));
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
        // With no arguments make space for the return type size only.
        // With arguments: Increment the SP by activation record size and return type size. Emit
        // the arguments there - after CAL 1 X the arguments will be the first variables after
        // the activation record. Afterwards decrement the SP to right after the return type size.
        if arguments_size == 0 {
            if return_type_size != 0 {
                self.emit_int(return_type_size as i32);
            }
        } else {
            self.emit_int((return_type_size + Scope::ACTIVATION_RECORD_SIZE) as i32);
            for argument in arguments {
                self.emit_expression(argument);
            }
            self.emit_int(-((arguments_size + Scope::ACTIVATION_RECORD_SIZE) as i32));
        }

        // Call the function.
        self.emit_call(
            level,
            Address::Label(Self::create_function_label(identifier)),
        );
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
