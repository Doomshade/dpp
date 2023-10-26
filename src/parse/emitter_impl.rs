use std::fs;
use std::io;
use std::io::Write;

use dpp_macros::Pos;

use crate::parse::analysis::FunctionScope;
use crate::parse::compiler;
use crate::parse::emitter::{Address, DebugKeyword, Instruction, OperationType};
use crate::parse::parser::{
    BinaryOperator, Block, DataType, Statement, TranslationUnit, UnaryOperator,
};
use crate::parse::{Emitter, Expression, Function, Variable};

impl<'a, 'b> Emitter<'a, 'b> {
    pub fn emit_all(
        &mut self,
        writer: &mut io::BufWriter<fs::File>,
        translation_unit: &TranslationUnit<'a>,
    ) -> io::Result<()> {
        self.emit_translation_unit(translation_unit);

        // First emit the base
        writer.write_all(b"LIT 0 1\n")?;
        for instruction in &self.code {
            match instruction {
                Instruction::Load { level, offset } => {
                    writer.write_all(format!("LOD {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Store { level, offset } => {
                    writer.write_all(format!("STO {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Literal { value } => {
                    writer.write_all(format!("LIT 0 {value}\r\n").as_bytes())?;
                }
                Instruction::Jump { address } => {
                    let str = format!("JMP 0 {address}\r\n");
                    writer.write_all(str.as_bytes())?;
                }
                Instruction::Jmc { address } => {
                    writer.write_all(format!("JMC 0 {address}\r\n").as_bytes())?;
                }
                Instruction::Call { level, address } => {
                    writer.write_all(format!("CAL {level} {address}\r\n").as_bytes())?;
                }
                Instruction::Operation { operation } => {
                    writer.write_all(format!("OPR 0 {}\r\n", *operation as u32).as_bytes())?;
                }
                Instruction::Return => {
                    writer.write_all(b"RET 0 0\r\n")?;
                }
                Instruction::Int { size } => {
                    writer.write_all(format!("INT 0 {size}\r\n").as_bytes())?;
                }
                Instruction::Dbg { debug_keyword } => {
                    if compiler::DEBUG {
                        match debug_keyword {
                            DebugKeyword::Registers => {
                                writer.write_all(b"&REGS\r\n")?;
                            }
                            DebugKeyword::Stack => {
                                writer.write_all(b"&STK\r\n")?;
                            }
                            DebugKeyword::StackA => {
                                writer.write_all(b"&STKA\r\n")?;
                            }
                            DebugKeyword::StackRg { start, end } => {
                                writer.write_all(format!("&STKRG {start} {end}\r\n").as_bytes())?;
                            }
                            DebugKeyword::StackN { amount } => {
                                writer.write_all(format!("&STKN {amount}\r\n").as_bytes())?;
                            }
                            DebugKeyword::Echo { message } => {
                                writer.write_all(format!("&ECHO {message}\r\n").as_bytes())?;
                            }
                        }
                    }
                }
                Instruction::Label(label) => {
                    writer.write_all(format!("\n@{label} ").as_bytes())?;
                }
            }
        }
        Ok(())
    }

    fn emit_translation_unit(&mut self, translation_unit: &TranslationUnit<'a>) {
        self.emit_int(
            translation_unit
                .global_statements()
                .iter()
                .fold(0, |mut acc, stat| {
                    match stat {
                        Statement::VariableDeclaration { variable, .. } => {
                            acc += variable.size_in_instructions();
                        }
                        _ => panic!("Invalid global statement"),
                    }
                    return acc;
                }) as i32,
        );
        translation_unit
            .global_statements()
            .iter()
            .for_each(|stmt| self.emit_statement(stmt, None, None));
        self.emit_debug_info(DebugKeyword::Stack);
        self.emit_main_call();
        translation_unit
            .functions()
            .iter()
            .for_each(|func| self.emit_function(func))
    }

    fn emit_function(&mut self, function: &Function<'a>) {
        self.current_function = Some(function.identifier());
        self.emit_function_label(function.identifier());

        let sym_table = self.symbol_table();
        let function_scope = sym_table.function_scope(function.identifier()).unwrap();
        // Shift the stack pointer by activation record + declared variable count.
        self.emit_int(
            (FunctionScope::ACTIVATION_RECORD_SIZE + function_scope.variable_count()) as i32,
        );

        // Load arguments.
        let args = function.parameters();
        if !args.is_empty() {
            self.echo(format!("Loading {} arguments", args.len()).as_str());
            self.emit_load_arguments(&args);
            self.echo(format!("{} arguments loaded", args.len()).as_str());
        }
        self.emit_block(function.block());
        if function.return_type() == &DataType::Nopp {
            self.emit_instruction(Instruction::Return);
        }

        self.emit_debug_info(DebugKeyword::StackA);
    }

    fn emit_load_arguments(&mut self, arguments: &Vec<Variable<'a>>) {
        // Load the parameters into the stack from the callee function.
        // The parameters are on the stack in FIFO order like so: [n, n + 1, n + 2, ...].
        // To load them we have to get the total size of parameters and subtract it
        // each time we load a parameter.
        // for example:
        // ```FUNc foo(argc: pp, argv:pp) {
        // ...
        // }
        // foo(1, 2);```
        // The parameters are loaded as follows:
        // The total size is 1 (pp) + 1 (pp) = 2.
        // The LOD function only loads 32 bits, so for anything bigger
        // than that we need to LOD again.
        // NOTE: We have to load with an offset because we pass in some things on stack
        // like the depth.
        let total_size = arguments
            .iter()
            .fold(0, |acc, parameter| acc + parameter.size_in_instructions());
        let mut curr_offset = total_size as i32;
        for parameter in arguments.iter().rev() {
            let size = parameter.size_in_instructions();
            self.load(0, -curr_offset, size);
            curr_offset += size as i32;
            self.echo(format!("Loaded argument {}", parameter.identifier()).as_str());
        }
    }

    fn emit_block(&mut self, block: &Block<'a>) {
        block
            .statements()
            .iter()
            .for_each(|statement| self.emit_statement(statement, None, None));
    }

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
        statement: &Statement<'a>,
        start_label: Option<&str>,
        end_label: Option<&str>,
    ) {
        match statement {
            Statement::Expression { expression, .. } => {
                self.emit_expression(expression);
                if let Expression::FunctionCall { identifier, .. } = expression {
                    // Pop the return  value off the stack because it's not assigned to anything.
                    let return_type_size;
                    {
                        let symbol_table = self.symbol_table();
                        let function = symbol_table.find_function(identifier).expect("A function");
                        return_type_size = function.return_type().size_in_instructions();
                    }
                    if return_type_size > 0 {
                        self.emit_int(-(return_type_size as i32));
                        self.echo(
                            format!(
                                "Dropped returned value of {} ({} bytes)",
                                identifier,
                                return_type_size * 4
                            )
                            .as_str(),
                        );
                        self.emit_debug_info(DebugKeyword::StackA);
                    }
                }
            }
            Statement::VariableDeclaration { variable, .. } => {
                if let Some(expression) = variable.value() {
                    self.echo(format!("Initializing variable {}", variable.identifier()).as_str());
                    self.emit_expression(expression);
                    let (level, var_loc) = self.symbol_table().get_variable_level_and_offset(
                        variable.identifier(),
                        self.current_function,
                    );
                    self.store(level, var_loc as i32, 1);

                    self.echo(format!("Variable {} initialized", variable.identifier()).as_str());
                }
            }
            Statement::Bye { expression, .. } => {
                let parameters_size;
                {
                    let symbol_table = self.symbol_table();
                    let current_function = symbol_table
                        .function_scope(self.current_function.unwrap())
                        .unwrap();
                    let function_identifier = current_function.function_identifier();
                    let function = symbol_table.find_function(function_identifier).unwrap();
                    parameters_size = function.parameters_size();
                }
                if let Some(expression) = expression {
                    self.emit_expression(expression);
                    self.echo(format!("Returning {}", expression).as_str());
                    // TODO: The return value offset should consider the size of the return value.
                    self.store(0, -1 - parameters_size as i32, 1);
                }
                self.emit_instruction(Instruction::Return);
                // Don't emit RET. The function `emit_function` will handle this
                // because in case of main function we want to JMP 0 0 instead of RET 0 0.
            }
            Statement::While {
                expression,
                statement,
                ..
            } => {
                self.push_scope();
                let start = self.create_label("while_s");
                let end = self.create_label("while_e");

                self.emit_label(start.as_str());
                self.emit_expression(expression);
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(end.clone()),
                });
                self.emit_statement(statement, Some(start.as_str()), Some(end.as_str()));
                self.pop_scope();
                self.emit_instruction(Instruction::Jump {
                    address: Address::Label(start),
                });
                self.emit_finishing_label(end.as_str());
            }
            Statement::For {
                index_ident,
                ident_expression,
                length_expression,
                statement,
                ..
            } => {
                let cmp_label = self.create_label("for_cmp");
                let end = self.create_label("for_end");
                let (level, var_loc) = self
                    .symbol_table()
                    .get_variable_level_and_offset(index_ident, self.current_function);

                // Create a new variable for the for loop and store its value.
                if let Some(expression) = ident_expression {
                    self.emit_expression(expression);
                } else {
                    self.emit_literal(0);
                }
                self.store(level, var_loc as i32, 1);

                // Compare the variable with the length.
                self.emit_label(cmp_label.as_str());
                self.load(level, var_loc as i32, 1);
                self.emit_expression(length_expression);
                self.emit_operation(OperationType::LessThan);
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(end.clone()),
                });

                self.emit_statement(statement, Some(cmp_label.as_str()), Some(end.as_str()));

                // Increment i.
                self.load(level, var_loc as i32, 1);
                self.emit_literal(1);
                self.emit_operation(OperationType::Add);
                self.store(level, var_loc as i32, 1);
                self.emit_jump(Address::Label(cmp_label.clone()));
                self.emit_label(end.as_str());
            }

            Statement::Empty { .. } => {
                // Emit nothing I guess :)
            }
            Statement::Block { block, .. } => {
                self.push_scope();
                block
                    .statements()
                    .iter()
                    .for_each(|statement| self.emit_statement(statement, start_label, end_label));
                self.pop_scope();
            }
            Statement::If {
                expression,
                statement,
                ..
            } => {
                self.push_scope();
                let end = self.create_label("if_e");

                self.emit_expression(expression);
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(end.clone()),
                });
                self.emit_statement(statement, start_label, end_label);
                self.pop_scope();
                self.emit_finishing_label(end.as_str());
            }
            Statement::IfElse {
                expression,
                statement,
                else_statement,
                ..
            } => {
                self.push_scope();
                let end_if = self.create_label("if_e");
                let else_block = self.create_label("else");

                self.emit_expression(expression);
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(else_block.clone()),
                });
                self.emit_statement(statement, start_label, end_label);
                self.pop_scope();
                self.emit_instruction(Instruction::Jump {
                    address: Address::Label(end_if.clone()),
                });
                self.emit_finishing_label(else_block.as_str());
                self.emit_statement(else_statement, start_label, end_label);
                self.emit_finishing_label(end_if.as_str());
            }
            Statement::Assignment {
                identifier,
                expression,
                ..
            } => {
                let (level, var_loc) = self
                    .symbol_table()
                    .get_variable_level_and_offset(identifier, self.current_function);
                self.emit_expression(expression);
                self.store(level, var_loc as i32, 1);
            }
            Statement::Continue { .. } => {
                self.echo("Jumping to the start of the loop (continue)");
                self.emit_jump(Address::Label(start_label.unwrap().to_string()));
            }
            Statement::Break { .. } => {
                self.echo("Breaking out of loop");
                self.emit_jump(Address::Label(end_label.unwrap().to_string()));
            }
            _ => self.error_diag.borrow_mut().not_implemented(
                statement.position(),
                format!("statement {:?}", statement).as_str(),
            ),
        };
    }

    fn emit_expression(&mut self, expression: &Expression<'a>) {
        match expression {
            Expression::Number { value, .. } => {
                self.emit_literal(*value);
            }
            Expression::P { value: p, .. } => {
                self.emit_literal(*p as i32);
            }
            Expression::Booba { value, .. } => {
                self.emit_literal(i32::from(*value));
            }
            Expression::Yarn { value: yarn, .. } => {
                self.emit_literal(yarn.len() as i32);
                Self::pack_yarn(yarn)
                    .into_iter()
                    .for_each(|four_packed_chars| self.emit_literal(four_packed_chars));
            }
            Expression::Binary { lhs, rhs, op, .. } => {
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
                        short_circuit_label = Some(self.create_label("short_crct"));
                        after_expr_label = Some(self.create_label("after_bool_expr"));
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
                    self.echo(format!("Reached short-circuit label for {:?}", op).as_str());
                    self.emit_label(label.as_str());
                    match op {
                        BinaryOperator::And => self.emit_booba(false),
                        BinaryOperator::Or => self.emit_booba(true),
                        _ => {}
                    };
                }

                // We jump here if the expression is not short-circuited.
                if let Some(label) = after_expr_label {
                    self.emit_label(label.as_str());
                }
            }
            Expression::Identifier { identifier, .. } => {
                let (level, var_loc) = self
                    .symbol_table()
                    .get_variable_level_and_offset(identifier, self.current_function);
                self.load(level, var_loc as i32, 1);
                self.echo(format!("Loaded {}", identifier).as_str());
                self.emit_debug_info(DebugKeyword::StackN { amount: 1 });
            }
            Expression::FunctionCall {
                arguments,
                identifier,
                ..
            } => {
                self.emit_function_call(arguments, identifier);
            }
            Expression::Unary { op, operand, .. } => {
                self.emit_expression(operand);
                match op {
                    UnaryOperator::Not => {
                        self.emit_expression(&Expression::Booba {
                            position: (0, 0),
                            value: true,
                        });
                        self.emit_operation(OperationType::NotEqual);
                    }
                    UnaryOperator::Negate => self.emit_operation(OperationType::Negate),
                }
            }
            _ => todo!("Not implemented {expression}"),
        }
    }

    fn emit_booba(&mut self, value: bool) {
        self.emit_expression(&Expression::Booba {
            position: (0, 0),
            value,
        });
    }

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

                // Need to duplicate the value on top of the stack because Jmc consumes
                // the boolean value and we need to store it.
                self.emit_booba(true);
                self.emit_operation(OperationType::Equal);
                self.echo("Duplicated value for AND");

                // If the value is FALSE stop executing the rest of the expression.
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(short_circuit_label.to_string()),
                });
            }
            BinaryOperator::Or => {
                // Compare the value to true.
                self.emit_booba(true);
                self.emit_operation(OperationType::Equal);

                // Need to duplicate the value on top of the stack because Jmc consumes
                // the boolean value and we need to store it.
                self.emit_booba(true);
                self.emit_operation(OperationType::NotEqual);
                self.echo("Duplicated value for OR");

                // If the value is TRUE stop executing the rest of the expression.
                self.emit_instruction(Instruction::Jmc {
                    address: Address::Label(short_circuit_label.to_string()),
                });
            }
            _ => {
                panic!("Invalid boolean expression");
            }
        }
    }

    fn emit_function_call(&mut self, arguments: &Vec<Expression<'a>>, identifier: &str) {
        // Size in instructions.
        let return_type_size;
        let arguments_size;
        if identifier == "main" {
            // Doing this only because the IntelliJ Idea plugin considers this an error :(
            let (r, a) = self.main_function_descriptor();
            return_type_size = r;
            arguments_size = a;
        } else {
            let symbol_table = self.symbol_table();
            let function = symbol_table
                .find_function(identifier)
                .expect("Function to exist");
            return_type_size = function.return_type().size_in_instructions();
            arguments_size = function.parameters_size();
        }

        // If the function has a return type we need to allocate
        // extra space on the stack for the thing it returns.
        if return_type_size > 0 {
            self.emit_instruction(Instruction::Int {
                size: return_type_size as i32,
            });
            self.echo(
                format!(
                    "Reserved {} bytes for return value of {}",
                    return_type_size * 4,
                    identifier
                )
                .as_str(),
            );
            self.emit_debug_info(DebugKeyword::Stack);
        }

        // Emit arguments AFTER the return type.
        if arguments.len() > 0 {
            self.echo(format!("Initializing {} arguments", arguments.len()).as_str());
            for argument in arguments {
                self.emit_expression(argument);
                self.echo(format!("Initialized {}", argument).as_str());
            }
            self.echo(format!("{} argument(s) initialized", arguments.len()).as_str());
        }

        // Call the function finally.
        self.echo(format!("Calling {}", identifier).as_str());
        self.emit_call_with_level(1, Address::Label(String::from(identifier)));

        // Pop the arguments off the stack.
        if arguments_size > 0 {
            self.echo(format!("Popping {arguments_size} argument(s) for {identifier}").as_str());
            self.emit_instruction(Instruction::Int {
                size: -(arguments_size as i32),
            });
        }
    }

    fn emit_main_call(&mut self) {
        self.echo("Calling main function.");
        let main_function_call = Expression::FunctionCall {
            identifier: "main",
            arguments: Vec::new(),
            position: (0, 0),
        };
        self.emit_expression(&main_function_call);

        // The last instruction will be the JMP to 0 - indicating exit.
        self.echo("Program returned with return value:");
        self.emit_debug_info(DebugKeyword::StackN { amount: 1 });
        self.emit_jump(Address::Absolute(0));
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
