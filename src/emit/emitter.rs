use core::fmt;
use std::collections::HashMap;
use std::io;
use std::io::{BufWriter, Write};

use crate::parse::analysis::{BoundBlock, BoundFunction};
use crate::parse::parser::{BinaryOperator, Expression, Statement};

#[derive(Debug)]
pub enum Instruction {
    /// Push the literal value arg onto the stack.
    LIT {
        value: i32,
    },
    /// Return from a subroutine. This instruction uses the stack frame (or block mark) from the current invocation of the subroutine to clear the stack of all data local to the current subroutine, restore the base register, and restore the program counter. Like all operations which require no arguments, it uses the op code OPR, with a second argument (here zero) indicating which of the zero-argument operations to perform.
    OPR {
        operation: Operation,
    },
    /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
    LOD {
        level: u32,
        offset: i32,
    },
    /// Store the value currently at the top of the stack to the memory cell identified by level and offset, popping the value off the stack in the process.
    STO {
        level: u32,
        offset: i32,
    },
    /// Call the subroutine at location address, which is level nesting levels different from the nesting level of the currently executing code. This instruction pushes a stack frame (or block mark) onto the stack, storing
    ///
    ///     the base address for variables, level blocks down on the stack (so that variables in outer blocks can be referred to and modified)
    ///     the current base address (so that it can be restored when the subroutine returns)
    ///     the current program counter (so that it can be restored when the subroutine returns)
    CAL {
        level: u32,
        address: u32,
    },
    RET,
    INT {
        size: u32,
    },
    /// Jump to the instruction at address.
    JMP {
        address: u32,
    },
    /// Pop the current value from the top of the stack. If it's 0 (false), jump to the instruction at address. Otherwise, continue with the current location of the program counter.
    JMC {
        address: u32,
    },
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
        // or, alternatively:
        // fmt::Debug::fmt(self, f)
    }
}

#[derive(Debug)]
pub enum Operation {
    Return = 0,
    /// Negate the value on the top of the stack (i.e. multiply by -1).
    Negate = 1,
    /// Add the two values at the top of the stack and replace them with their sum.
    Add = 2,
    /// Subtract the value at the top of the stack from the value below it; replace the diminuend and the subtrahend with their difference.
    Subtract = 3,
    /// Multiply the two values at the top of the stack and replace them with their product.
    Multiply = 4,
    /// Perform integer division on the two values at the top of the stack. The value on top of the stack becomes the divisor, the value below it the dividend. Replace the two values with their integer quotient.
    Divide = 5,
    Mod = 6,
    /// Test the value at the top of the stack to see if it's odd or not.
    Odd = 7,
    /// Test the two values at the top of the stack to see if they are equal or not.
    Equal = 8,
    /// Test the two values at the top of the stack to see if they are unequal or not.
    NotEqual = 9,
    /// Test the two values x and y at the top of the stack to see if x is less than y or not.
    LessThan = 10,
    /// Test the two values x and y at the top of the stack to see if x is greater than y or not.
    GreaterThanOrEqualTo = 11,
    /// Test the two values x and y at the top of the stack to see if x is greater than or equal to y, or not.
    GreaterThan = 12,
    /// Test the two values x and y at the top of the stack to see if x is less than or equal to y, or not.
    LessThanOrEqualTo = 13,
}

pub enum DebugKeyword {
    REGS,
    STK,
    STKA,
    STKRG { start: u32, end: u32 },
    STKN { amount: u32 },
    ECHO { message: &'static str },
}

pub struct Emitter<T>
where
    T: Write,
{
    writer: BufWriter<T>,
    should_emit: bool,
    code: Vec<Instruction>,
    function_labels: HashMap<String, u32>,
    scopes: Vec<HashMap<String, u32>>,
}

impl<T: Write> Emitter<T> {
    pub fn new(writer: BufWriter<T>) -> Self {
        Self {
            writer,
            should_emit: true,
            code: Vec::new(),
            function_labels: HashMap::new(),
            scopes: Vec::new(),
        }
    }

    pub fn stop_emitting(&mut self) {
        {
            let stop_emitting = 69;
        }
        let stop_emitting = 5;
        self.should_emit = false;
    }

    pub fn emit_debug_info(&mut self, debug: DebugKeyword) -> io::Result<()> {
        if !self.should_emit {
            return Ok(());
        }
        match debug {
            DebugKeyword::REGS => {
                self.writer.write(b"&REGS\r\n")?;
            }
            DebugKeyword::STK => {
                self.writer.write(b"&STK\r\n")?;
            }
            DebugKeyword::STKA => {
                self.writer.write(b"&STKA\r\n")?;
            }
            DebugKeyword::STKRG { start, end } => {
                self.writer
                    .write(format!("&STKRG {start} {end}\r\n").as_bytes())?;
            }
            DebugKeyword::STKN { amount } => {
                self.writer
                    .write(format!("&STKN {amount}\r\n").as_bytes())?;
            }
            DebugKeyword::ECHO { message } => {
                self.writer
                    .write(format!("&ECHO {message}\r\n").as_bytes())?;
            }
        };

        Ok(())
    }

    pub fn emit_expression<'a>(&mut self, expression: &Expression<'a>) {
        if !self.should_emit {
            return;
        }
        match expression {
            Expression::PpExpression { pp, .. } => {
                self.emit_instruction(Instruction::LIT { value: *pp });
            }
            Expression::PExpression { p, .. } => {
                self.emit_instruction(Instruction::LIT { value: *p as i32 });
            }
            Expression::BoobaExpression { booba, .. } => {
                self.emit_instruction(Instruction::LIT {
                    value: *booba as i32,
                });
            }
            Expression::YarnExpression { yarn, .. } => {
                self.emit_instruction(Instruction::LIT {
                    value: yarn.len() as i32,
                });
                let vec = Self::pack_yarn(yarn);
                for four_packed_chars in vec {
                    self.emit_instruction(Instruction::LIT {
                        value: four_packed_chars,
                    });
                }
            }
            Expression::UnaryExpression { .. } => {}
            Expression::BinaryExpression { lhs, rhs, op, .. } => {
                self.emit_expression(lhs);
                self.emit_expression(rhs);
                match op {
                    BinaryOperator::Add => {
                        self.emit_instruction(Instruction::OPR {
                            operation: Operation::Add,
                        });
                    }
                    BinaryOperator::Subtract => {
                        self.emit_instruction(Instruction::OPR {
                            operation: Operation::Subtract,
                        });
                    }
                    BinaryOperator::Multiply => {
                        self.emit_instruction(Instruction::OPR {
                            operation: Operation::Multiply,
                        });
                    }
                    BinaryOperator::Divide => {}
                    BinaryOperator::NotEqual => {}
                    BinaryOperator::Equal => {}
                    BinaryOperator::GreaterThan => {}
                    BinaryOperator::GreaterThanOrEqual => {}
                    BinaryOperator::LessThan => {}
                    BinaryOperator::LessThanOrEqual => {}
                }
            }
            Expression::IdentifierExpression { identifier, .. } => {
                let var_loc = self
                    .get_variable_location(identifier)
                    .expect(format!("Unknown variable {identifier}").as_str());
                self.emit_instruction(Instruction::LOD {
                    level: 0,
                    offset: var_loc as i32 - self.code.len() as i32,
                });
            }
            Expression::FunctionCall {
                identifier,
                arguments,
                ..
            } => {
                // TODO: Handle the error
                let function_label = self.function_labels.get(&identifier.to_string()).unwrap();
                for argument in arguments {
                    self.emit_expression(argument);
                }
            }
            Expression::AssignmentExpression { .. } => {}
            Expression::InvalidExpression => {}
        }
    }

    fn get_variable_location(&self, variable: &str) -> Option<u32> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(variable))
            .as_deref()
            .copied()
    }

    fn pack_yarn(yarn: &str) -> Vec<i32> {
        let mut vec: Vec<i32> = Vec::with_capacity((yarn.len() / 4) + 1);
        // 6386532
        for chunk in yarn.as_bytes().chunks(4) {
            let packed_chars = match chunk.len() {
                1 => chunk[0] as i32,
                2 => (chunk[1] as i32) << 8 | (chunk[0] as i32),
                3 => (chunk[2] as i32) << 16 | (chunk[1] as i32) << 8 | (chunk[0] as i32),
                4 => {
                    (chunk[3] as i32) << 24
                        | (chunk[2] as i32) << 16
                        | (chunk[1] as i32) << 8
                        | (chunk[0] as i32)
                }
                _ => unreachable!(),
            };
            println!("{:#010x}", &packed_chars);

            vec.push(packed_chars);
        }
        vec
    }

    pub fn emit_function<'a>(&mut self, function: &BoundFunction<'a>) {
        self.add_function_label(&function.identifier);
        // Load the parameters into the stack.
        let parameters = &function.parameters;
        for i in 0..parameters.len() {
            let offset = (i as i32) - parameters.len() as i32;
            self.emit_instruction(Instruction::LOD { level: 1, offset });
        }

        self.emit_block(&function.block);
    }

    fn add_function_label(&mut self, label: &str) {
        self.function_labels
            .insert(label.to_string(), self.code.len() as u32);
    }

    fn add_variable_label(&mut self, label: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(label.to_string(), self.code.len() as u32);
        }
    }

    pub fn emit_instruction(&mut self, instruction: Instruction) {
        if !self.should_emit {
            return;
        }
        self.code.push(instruction);
    }

    pub fn emit_all(&mut self) -> io::Result<()> {
        for instruction in self.code {
            match instruction {
                Instruction::LOD { level, offset } => {
                    self.writer
                        .write(format!("LOD {} {}\r\n", level, offset).as_bytes())?;
                }
                Instruction::STO { level, offset } => {
                    self.writer
                        .write(format!("STO {} {}\r\n", level, offset).as_bytes())?;
                }
                Instruction::LIT { value } => {
                    self.writer
                        .write(format!("LIT 0 {}\r\n", value).as_bytes())?;
                }
                Instruction::JMP { address } => {
                    self.writer
                        .write(format!("JMP 0 {}\r\n", address).as_bytes())?;
                }
                Instruction::JMC { address } => {
                    self.writer
                        .write(format!("JMC 0 {}\r\n", address).as_bytes())?;
                }
                Instruction::CAL { level, address } => {
                    self.writer
                        .write(format!("CAL {} {}\r\n", level, address).as_bytes())?;
                }
                Instruction::OPR { operation } => {
                    self.writer
                        .write(format!("OPR 0 {}\r\n", *operation as u32).as_bytes())?;
                }
                Instruction::RET => {
                    self.writer.write(b"RET 0 0\r\n")?;
                }
                Instruction::INT { size } => {
                    self.writer
                        .write(format!("INT 0 {}\r\n", size).as_bytes())?;
                }
            }
            self.emit_debug_info(DebugKeyword::REGS)?;
        }
        Ok(())
    }

    pub fn emit_block<'a>(&mut self, block: &BoundBlock<'a>) {
        self.begin_scope();
        for statement in &block.statements {
            self.emit_statement(statement);
        }
        self.end_scope();
    }
    pub fn emit_statement<'a>(&mut self, statement: &Statement<'a>) {
        match statement {
            Statement::ExpressionStatement { expression, .. } => {
                self.emit_expression(expression);
            }
            Statement::VariableDeclaration { variable } => {
                self.add_variable_label(variable.identifier);
            }
            Statement::VariableDeclarationAndAssignment {
                variable,
                expression,
            } => {
                self.add_variable_label(variable.identifier);
                self.emit_expression(expression);
            }
            _ => todo!("emit_statement"),
        };
    }

    pub fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn end_scope(&mut self) {
        self.scopes.pop();
    }
}
