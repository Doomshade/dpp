use std::fmt::{Display, Formatter};
use std::io::Write;

use crate::parse::analysis::{BoundBlock, BoundFunction, FunctionScope, GlobalScope};
use crate::parse::parser::{BinaryOperator, Expression, Statement};

#[derive(Clone, Debug)]
pub enum Address {
    Absolute(u32),
    Label(String),
}

impl Display for Address {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Address::Absolute(absolute_address) => write!(f, "{absolute_address}")?,
            Address::Label(label) => write!(f, "@{label} ")?,
        };

        Ok(())
    }
}

#[derive(Clone, Debug)]
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
        address: Address,
    },
    RET,
    INT {
        size: i32,
    },
    /// Jump to the instruction at address.
    JMP {
        address: Address,
    },
    /// Pop the current value from the top of the stack. If it's 0 (false), jump to the instruction at address. Otherwise, continue with the current location of the program counter.
    JMC {
        address: Address,
    },
    // TODO: Those aren't instructions! Make a new enum.
    DBG {
        debug_keyword: DebugKeyword,
    },
    Label(String),
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
        // or, alternatively:
        // fmt::Debug::fmt(self, f)
    }
}

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Debug)]
pub enum DebugKeyword {
    REGS,
    STK,
    STKA,
    STKRG { start: u32, end: u32 },
    STKN { amount: u32 },
    ECHO { message: &'static str },
}

pub struct Emitter<'a, T>
where
    T: Write,
{
    writer: std::io::BufWriter<T>,
    // The instructions to be emitted.
    code: Vec<Instruction>,
    /// Stack of function scopes. Each scope is pushed and popped when entering and exiting a function.
    function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
    /// The global scope.
    global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
    /// The labels of the functions.
    function_labels: std::collections::HashMap<String, u32>,
}

const PL0_DATA_SIZE: usize = std::mem::size_of::<i32>();

impl<'a, T: Write> Emitter<'a, T> {
    pub fn new(
        writer: std::io::BufWriter<T>,
        function_scopes: std::rc::Rc<std::cell::RefCell<Vec<FunctionScope<'a>>>>,
        global_scope: std::rc::Rc<std::cell::RefCell<GlobalScope<'a>>>,
    ) -> Self {
        Self {
            writer,
            code: Vec::new(),
            function_labels: std::collections::HashMap::new(),
            function_scopes,
            global_scope,
        }
    }

    pub fn emit_debug_info(&mut self, debug_keyword: DebugKeyword) {
        self.emit_instruction(Instruction::DBG { debug_keyword });
    }

    pub fn emit_expression(&mut self, expression: &Expression<'a>) {
        match expression {
            Expression::NumberExpression { value, .. } => {
                self.emit_instruction(Instruction::LIT { value: *value })
            }
            Expression::PExpression { value: p, .. } => {
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
                let var_loc;
                {
                    let global_scope = self.global_scope.borrow();
                    var_loc = global_scope
                        .scope()
                        .get_variable(identifier)
                        .expect(format!("Unknown variable {identifier}").as_str())
                        .position_in_scope();
                    dbg!(&var_loc);
                }
                self.emit_debug_info(DebugKeyword::STK);
                self.load(0, var_loc as i32, 4);
                self.emit_debug_info(DebugKeyword::STK);
            }
            Expression::FunctionCall {
                arguments,
                identifier,
                ..
            } => {
                for argument in arguments {
                    self.emit_expression(argument);
                }
                self.emit_instruction(Instruction::CAL {
                    level: 1,
                    address: Address::Label(String::from(*identifier)),
                });
            }
            Expression::AssignmentExpression { .. } => {}
            Expression::InvalidExpression => {}
        }
    }

    pub fn emit_main_call(&mut self) {
        self.emit_instruction(Instruction::CAL {
            level: 0,
            address: Address::Label(String::from("main")),
        });
    }

    pub fn emit_function_call(&mut self, name: &str) {
        self.emit_instruction(Instruction::CAL {
            level: 1,
            address: Address::Label(String::from(name)),
        });
    }

    fn get_variable_location(&self, identifier: &str) -> Option<u32> {
        self.global_scope.borrow().scope().get_variable(identifier);
        Some(1)
    }

    fn pack_yarn(yarn: &str) -> Vec<i32> {
        let mut vec: Vec<i32> = Vec::with_capacity((yarn.len() / 4) + 1);
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

    pub fn emit_function(&mut self, function: &BoundFunction<'a>) {
        self.emit_label(function.identifier());

        // Load the parameters into the stack from the callee function.
        // The parameters are on the stack in FIFO order like so: [n, n + 1, n + 2, ...].
        // To load them we have to get the total size of parameters and subtract it
        // each time we load a parameter.
        // for example:
        // ```FUNc foo(argc: pp, argv:xxlpp) {
        // ...
        // }
        // foo(1, 2);```
        // The parameters are loaded as follows:
        // The total size is 4 (pp) + 8 (xxlpp) = 12.
        // Load the variable at offset 12 (argc) and then subtract 4 from the offset.
        // Load the variable at offset 8 (argv) and then subtract 8 from the offset.
        // The LOD function only loads 32 bits, so for anything bigger
        // than that we need to LOD again.
        let parameters = function.parameters();
        let total_size = parameters
            .iter()
            .fold(0, |acc, parameter| acc + parameter.data_type.size());
        let mut curr_offset = total_size as i32;
        for i in 0..parameters.len() {
            let size = parameters[parameters.len() - i - 1].data_type.size();
            self.load(1, curr_offset, size);
            curr_offset -= size as i32;
        }

        self.emit_block(function.block());
    }

    fn load(&mut self, level: u32, offset: i32, size: usize) {
        for i in 0..size / PL0_DATA_SIZE {
            self.emit_instruction(Instruction::LOD {
                level,
                offset: offset + i as i32, // Load 4 bytes at a time.
            });
        }
    }

    fn store(&mut self, level: u32, offset: i32, size: usize) {
        for i in 0..size / PL0_DATA_SIZE {
            self.emit_instruction(Instruction::STO {
                level,
                offset: offset + i as i32 * PL0_DATA_SIZE as i32, // Store 4 bytes at a time.
            });
        }
    }

    pub fn emit_label(&mut self, label: &str) {
        self.function_labels
            .insert(label.to_string(), self.code.len() as u32);
        self.code.push(Instruction::Label(String::from(label)));
    }

    pub fn emit_instruction(&mut self, instruction: Instruction) {
        self.code.push(instruction);
    }

    pub fn emit_all(&mut self) -> std::io::Result<()> {
        for instruction in &self.code {
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
                    let str = format!("JMP 0 {}\r\n", address);
                    self.writer.write(str.as_bytes())?;
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
                    // Stupid usage of clone because we get the reference to the enum.
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
                Instruction::DBG { debug_keyword } => match debug_keyword {
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
                },
                Instruction::Label(label) => {
                    self.writer.write(format!("@{label} ").as_bytes())?;
                }
            }
        }
        Ok(())
    }

    pub fn emit_block(&mut self, block: &BoundBlock<'a>) {
        for statement in &block.statements {
            self.emit_statement(statement);
        }
    }
    pub fn emit_statement(&mut self, statement: &Statement<'a>) {
        match statement {
            Statement::ExpressionStatement { expression, .. } => {
                self.emit_expression(expression);
            }
            Statement::VariableDeclaration { .. } => {}
            Statement::VariableDeclarationAndAssignment { expression, .. } => {
                self.emit_expression(expression);
                self.emit_debug_info(DebugKeyword::STK);
            }
            Statement::ByeStatement { expression, .. } => {
                if let Some(expression) = expression {
                    self.emit_expression(expression);
                }
                self.emit_debug_info(DebugKeyword::REGS);
                self.emit_debug_info(DebugKeyword::STK);
                self.emit_instruction(Instruction::RET);
                // Don't emit RET. The function `emit_function` will handle this
                // because in case of main function we want to JMP 0 0 instead of RET 0 0.
            }
            _ => todo!("Emitting statement: {:#?}", statement),
        };
    }
}
