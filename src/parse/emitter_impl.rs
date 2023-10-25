use std::fs::File;
use std::io::{BufWriter, Write};
use std::rc::Rc;

use crate::parse::analysis::{FunctionScope, SymbolTable};
use crate::parse::compiler;
use crate::parse::emitter::{Address, DebugKeyword, Instruction, Operation};
use crate::parse::parser::{BinaryOperator, Block, DataType, Statement, TranslationUnit};
use crate::parse::{Emitter, Expression, Function, Variable};

impl<'a> Emitter<'a> {
    pub fn new(symbol_table: Rc<SymbolTable<'a>>) -> Self {
        Self {
            code: Vec::new(),
            labels: std::collections::HashMap::new(),
            control_statement_count: 0,
            symbol_table,
            function_scope_depth: std::collections::HashMap::new(),
            current_function: None,
        }
    }

    pub fn emit_all(
        &mut self,
        writer: &mut BufWriter<File>,
        translation_unit: &TranslationUnit<'a>,
    ) -> std::io::Result<()> {
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
                        Statement::VariableDeclaration { variable } => {
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
            .for_each(|stmt| self.emit_statement(stmt));
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

    fn emit_block(&mut self, block: &Block<'a>) {
        block
            .statements()
            .iter()
            .for_each(|statement| self.emit_statement(statement));
    }

    pub fn emit_jump(&mut self, address: Address) {
        self.emit_instruction(Instruction::Jump { address });
    }

    pub fn emit_debug_info(&mut self, debug_keyword: DebugKeyword) {
        self.emit_instruction(Instruction::Dbg { debug_keyword });
    }

    pub fn echo(&mut self, message: &str) {
        self.emit_debug_info(DebugKeyword::Echo {
            message: String::from(message),
        });
    }

    fn symbol_table(&self) -> &SymbolTable<'a> {
        &self.symbol_table
    }

    pub fn emit_expression(&mut self, expression: &Expression<'a>) {
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
                self.emit_expression(lhs);
                self.emit_expression(rhs);
                use BinaryOperator::*;
                match op {
                    Add => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Add,
                        });
                    }
                    Subtract => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Subtract,
                        });
                    }
                    Multiply => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Multiply,
                        });
                    }
                    Equal => self.emit_instruction(Instruction::Operation {
                        operation: Operation::Equal,
                    }),
                    GreaterThan => self.emit_instruction(Instruction::Operation {
                        operation: Operation::GreaterThan,
                    }),
                    _ => todo!("Binary operator {:?}", op),
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
            _ => todo!("Not implemented"),
        }
    }

    fn main_function_descriptor(&self) -> (usize, usize) {
        (1, 0)
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

    pub fn emit_main_call(&mut self) {
        self.echo("Calling main function.");
        let main_function_call = Expression::FunctionCall {
            identifier: "main",
            arguments: Vec::new(),
            position: (0, 0),
        };
        self.emit_expression(&main_function_call);

        // The last instruction will be the JMP to 0 - indicating exit.
        self.echo("Program returned with return value:");
        self.emit_debug_info(DebugKeyword::StackN { amount: 4 });
        self.emit_jump(Address::Absolute(0));
    }

    fn emit_call_with_level(&mut self, level: u32, address: Address) {
        self.emit_instruction(Instruction::Call { level, address });
    }

    pub fn emit_literal(&mut self, value: i32) {
        self.emit_instruction(Instruction::Literal { value })
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
            println!("{:#010x}", &packed_chars);

            vec.push(packed_chars);
        }
        vec
    }

    pub fn emit_load_arguments(&mut self, arguments: &Vec<Variable<'a>>) {
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

    fn load(&mut self, level: u32, offset: i32, count: usize) {
        for i in 0..count {
            self.emit_instruction(Instruction::Load {
                level,
                offset: offset + i as i32,
            });
        }
    }

    pub fn store(&mut self, level: u32, offset: i32, count: usize) {
        for i in 0..count {
            self.emit_instruction(Instruction::Store {
                level,
                offset: offset + i as i32,
            });
        }
    }

    fn create_label(&mut self, label: &str) -> String {
        let control_label;
        if compiler::DEBUG {
            control_label = format!("0{label}_{}", self.control_statement_count);
        } else {
            control_label = format!("{}", self.control_statement_count);
        }
        self.control_statement_count += 1;
        control_label
    }

    pub fn emit_function_label(&mut self, label: &str) {
        self.emit_label(label);
    }

    fn emit_finishing_label(&mut self, label: &str) {
        self.emit_label(label);

        // Need to emit an empty instruction because of a situation like
        // @while_end_0
        // @if_start_1 LOD ...
        // The PL0 interpret cannot interpret two labels properly..
        self.emit_int(0);
    }

    fn emit_label(&mut self, label: &str) {
        self.labels
            .insert(label.to_string(), self.code.len() as u32);
        self.emit_instruction(Instruction::Label(String::from(label)));
    }

    pub fn emit_int(&mut self, size: i32) {
        self.emit_instruction(Instruction::Int { size })
    }

    fn emit_instruction(&mut self, instruction: Instruction) {
        self.code.push(instruction);
    }

    pub fn emit_statement(&mut self, statement: &Statement<'a>) {
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
                    dbg!(&function);
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
                self.emit_statement(statement);
                self.pop_scope();
                self.emit_instruction(Instruction::Jump {
                    address: Address::Label(start),
                });
                self.emit_finishing_label(end.as_str());
            }
            Statement::Empty { .. } => {
                // Emit nothing I guess :)
            }

            Statement::Block { block, .. } => {
                self.push_scope();
                block
                    .statements()
                    .iter()
                    .for_each(|statement| self.emit_statement(statement));
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
                self.emit_statement(statement);
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
                self.emit_statement(statement);
                self.pop_scope();
                self.emit_instruction(Instruction::Jump {
                    address: Address::Label(end_if.clone()),
                });
                self.emit_finishing_label(else_block.as_str());
                self.emit_statement(else_statement);
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
            _ => println!("Not yet implemented: Emitting statement: {:#?}", statement),
        };
    }

    fn push_scope(&mut self) {
        let current_function_ident = self.current_function.unwrap();
        self.function_scope_depth.insert(
            current_function_ident,
            self.function_scope_depth
                .get(current_function_ident)
                .unwrap_or(&0)
                + 1,
        );
    }

    fn pop_scope(&mut self) {
        let current_function_ident = self.current_function.unwrap();
        self.function_scope_depth.insert(
            current_function_ident,
            self.function_scope_depth
                .get(current_function_ident)
                .unwrap()
                - 1,
        );
    }
}
