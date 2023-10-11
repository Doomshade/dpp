use std::fmt::{Display, Formatter};
use std::io::Write;

use crate::parse::analysis::{
    BoundBlock, BoundFunction, BoundVariable, FunctionScope, GlobalScope,
};
use crate::parse::parser::{BinaryOperator, DataType, Expression, Statement};

#[derive(Clone, Debug)]
pub enum Address {
    Absolute(u32),
    Label(String),
}

impl Display for Address {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Absolute(absolute_address) => write!(f, "{absolute_address}")?,
            Self::Label(label) => write!(f, "@{label} ")?,
        };

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum Instruction {
    /// Push the literal value arg onto the stack.
    Literal {
        value: i32,
    },
    /// Return from a subroutine. This instruction uses the stack frame (or block mark) from the current invocation of the subroutine to clear the stack of all data local to the current subroutine, restore the base register, and restore the program counter. Like all operations which require no arguments, it uses the op code OPR, with a second argument (here zero) indicating which of the zero-argument operations to perform.
    Operation {
        operation: Operation,
    },
    /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
    Load {
        level: u32,
        offset: i32,
    },
    /// Store the value currently at the top of the stack to the memory cell identified by level and offset, popping the value off the stack in the process.
    Store {
        level: u32,
        offset: i32,
    },
    /// Call the subroutine at location address, which is level nesting levels different from the nesting level of the currently executing code. This instruction pushes a stack frame (or block mark) onto the stack, storing
    ///
    ///     the base address for variables, level blocks down on the stack (so that variables in outer blocks can be referred to and modified)
    ///     the current base address (so that it can be restored when the subroutine returns)
    ///     the current program counter (so that it can be restored when the subroutine returns)
    Call {
        level: u32,
        address: Address,
    },
    Return,
    Int {
        size: i32,
    },
    /// Jump to the instruction at address.
    Jump {
        address: Address,
    },
    /// Pop the current value from the top of the stack. If it's 0 (false), jump to the instruction at address. Otherwise, continue with the current location of the program counter.
    Jmc {
        address: Address,
    },
    // TODO: Those aren't instructions! Make a new enum.
    Dbg {
        debug_keyword: DebugKeyword,
    },
    Label(String),
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
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
    Registers,
    Stack,
    StackA,
    StackRg { start: u32, end: u32 },
    StackN { amount: u32 },
    Echo { message: String },
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

    pub fn emit_jump(&mut self, address: Address) {
        self.emit_instruction(Instruction::Jump { address });
    }

    pub fn emit_debug_info(&mut self, debug_keyword: DebugKeyword) {
        self.emit_instruction(Instruction::Dbg { debug_keyword });
    }

    pub fn emit_expression(&mut self, expression: &Expression<'a>) {
        match expression {
            Expression::Number { value, .. } => {
                self.emit_instruction(Instruction::Literal { value: *value });
            }
            Expression::P { value: p, .. } => {
                self.emit_instruction(Instruction::Literal { value: *p as i32 });
            }
            Expression::Booba { booba, .. } => {
                self.emit_instruction(Instruction::Literal {
                    value: i32::from(*booba),
                });
            }
            Expression::Yarn { yarn, .. } => {
                self.emit_instruction(Instruction::Literal {
                    value: yarn.len() as i32,
                });
                let vec = Self::pack_yarn(yarn);
                for four_packed_chars in vec {
                    self.emit_instruction(Instruction::Literal {
                        value: four_packed_chars,
                    });
                }
            }
            Expression::Binary { lhs, rhs, op, .. } => {
                self.emit_expression(lhs);
                self.emit_expression(rhs);
                match op {
                    BinaryOperator::Add => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Add,
                        });
                    }
                    BinaryOperator::Subtract => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Subtract,
                        });
                    }
                    BinaryOperator::Multiply => {
                        self.emit_instruction(Instruction::Operation {
                            operation: Operation::Multiply,
                        });
                    }
                    _ => {}
                }
            }
            Expression::Identifier { identifier, .. } => {
                let (level, var_loc) = self.find_variable(identifier);
                self.emit_debug_info(DebugKeyword::Stack);
                self.load(level, var_loc as i32, 1);
                self.emit_debug_info(DebugKeyword::Stack);
            }
            Expression::FunctionCall {
                arguments,
                identifier,
                ..
            } => {
                let has_return_type: Option<bool>;
                if let Expression::FunctionCall { identifier, .. } = expression {
                    let x = self.global_scope.borrow();
                    let function = x.get_function(identifier).unwrap();
                    if let DataType::Nopp = function.return_type() {
                        has_return_type = Some(false);
                    } else {
                        has_return_type = Some(true);
                    }
                } else {
                    has_return_type = None;
                }

                if let Some(has_return_type) = has_return_type {
                    if has_return_type {
                        self.emit_instruction(Instruction::Int { size: 1 });
                    }
                }

                for argument in arguments {
                    self.emit_expression(argument);
                }
                self.emit_debug_info(DebugKeyword::Echo {
                    message: format!("Function call: {identifier}"),
                });
                self.emit_instruction(Instruction::Call {
                    level: 1,
                    address: Address::Label(String::from(*identifier)),
                });
                self.emit_debug_info(DebugKeyword::Stack);
            }
            _ => todo!("Not implemented"),
        }
    }

    fn find_variable(&self, identifier: &str) -> (u32, u32) {
        if let Some(function_scope) = self.function_scopes.borrow().last() {
            if let Some(variable) = function_scope.get_variable(identifier) {
                return (0, variable.position_in_scope());
            }
        }

        (
            1,
            self.global_scope
                .borrow()
                .get_variable(identifier)
                .unwrap_or_else(|| panic!("Unknown variable {identifier}"))
                .position_in_scope(),
        )
    }

    pub fn emit_main_call(&mut self) {
        self.emit_debug_info(DebugKeyword::Echo {
            message: String::from("Calling main function."),
        });
        self.emit_instruction(Instruction::Call {
            level: 0,
            address: Address::Label(String::from("main")),
        });
    }

    fn get_variable_location(&self, identifier: &str) -> Option<u32> {
        self.global_scope.borrow().get_variable(identifier);
        Some(1)
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

    pub fn load_parameters(&mut self, parameters: &Vec<BoundVariable<'a>>) {
        let total_size = parameters.iter().fold(0, |acc, parameter| {
            acc + ((parameter.data_type().size() - 1) / PL0_DATA_SIZE) + 1
        });
        let mut curr_offset = total_size as i32;
        for parameter in parameters.iter().rev() {
            let size = ((parameter.data_type().size() - 1) / PL0_DATA_SIZE) + 1;
            self.load(0, -curr_offset, size);
            curr_offset += size as i32;
        }
    }

    fn load(&mut self, level: u32, offset: i32, count: usize) {
        for i in 0..count {
            self.emit_debug_info(DebugKeyword::Registers);
            self.emit_instruction(Instruction::Load {
                level,
                offset: offset + i as i32, // Load 4 bytes at a time.
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
                Instruction::Load { level, offset } => {
                    self.writer
                        .write_all(format!("LOD {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Store { level, offset } => {
                    self.writer
                        .write_all(format!("STO {level} {offset}\r\n").as_bytes())?;
                }
                Instruction::Literal { value } => {
                    self.writer
                        .write_all(format!("LIT 0 {value}\r\n").as_bytes())?;
                }
                Instruction::Jump { address } => {
                    let str = format!("JMP 0 {address}\r\n");
                    self.writer.write_all(str.as_bytes())?;
                }
                Instruction::Jmc { address } => {
                    self.writer
                        .write_all(format!("JMC 0 {address}\r\n").as_bytes())?;
                }
                Instruction::Call { level, address } => {
                    self.writer
                        .write_all(format!("CAL {level} {address}\r\n").as_bytes())?;
                }
                Instruction::Operation { operation } => {
                    // Stupid usage of clone because we get the reference to the enum.
                    self.writer
                        .write_all(format!("OPR 0 {}\r\n", *operation as u32).as_bytes())?;
                }
                Instruction::Return => {
                    self.writer.write_all(b"RET 0 0\r\n")?;
                }
                Instruction::Int { size } => {
                    self.writer
                        .write_all(format!("INT 0 {size}\r\n").as_bytes())?;
                }
                Instruction::Dbg { debug_keyword } => match debug_keyword {
                    DebugKeyword::Registers => {
                        self.writer.write_all(b"&REGS\r\n")?;
                    }
                    DebugKeyword::Stack => {
                        self.writer.write_all(b"&STK\r\n")?;
                    }
                    DebugKeyword::StackA => {
                        self.writer.write_all(b"&STKA\r\n")?;
                    }
                    DebugKeyword::StackRg { start, end } => {
                        self.writer
                            .write_all(format!("&STKRG {start} {end}\r\n").as_bytes())?;
                    }
                    DebugKeyword::StackN { amount } => {
                        self.writer
                            .write_all(format!("&STKN {amount}\r\n").as_bytes())?;
                    }
                    DebugKeyword::Echo { message } => {
                        self.writer
                            .write_all(format!("&ECHO {message}\r\n").as_bytes())?;
                    }
                },
                Instruction::Label(label) => {
                    self.writer.write_all(format!("@{label} ").as_bytes())?;
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
            Statement::Expression { expression, .. } => {
                self.emit_expression(expression);
                if let Expression::FunctionCall { identifier, .. } = expression {
                    // Drop the value returned by the function call if it returns anything.
                    let return_type;
                    {
                        let x = self.global_scope.borrow();
                        let function = x.get_function(identifier).unwrap();
                        return_type = function.return_type().clone();
                    }
                    if let DataType::Nopp = return_type {
                        // Do nothing.
                    } else {
                        self.emit_instruction(Instruction::Int { size: -1 });
                        self.emit_debug_info(DebugKeyword::Stack);
                    }
                }
            }
            Statement::VariableDeclaration { .. } => {}
            Statement::VariableDeclarationAndAssignment { expression, .. } => {
                self.emit_expression(expression);
                self.emit_debug_info(DebugKeyword::Stack);
            }
            Statement::Bye { expression, .. } => {
                if let Some(expression) = expression {
                    self.emit_expression(expression);
                    self.store(0, -1, 1); // TODO: Offset must be -parameter.len()
                }
                self.emit_debug_info(DebugKeyword::Registers);
                self.emit_debug_info(DebugKeyword::Stack);
                self.emit_instruction(Instruction::Return);
                // Don't emit RET. The function `emit_function` will handle this
                // because in case of main function we want to JMP 0 0 instead of RET 0 0.
            }
            _ => todo!("Emitting statement: {:#?}", statement),
        };
    }
}
