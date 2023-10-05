use crate::parse::analysis::{BoundAST, SemanticAnalyzer};

enum Instruction {
    LOD { level: u32, offset: u32 },
    STO { level: u32, offset: u32 },
    LIT { value: u32 },
    JMP { address: u32 },
    JPC { address: u32 },
    CAL { level: u32, address: u32 },
    OPR { operation: Operation },
}

enum Operation {
    Return = 0,
    Negate = 1,
    Add = 2,
    Subtract = 3,
    Multiply = 4,
    Divide = 5,
    Odd = 6,
    Equal = 8,
    NotEqual = 9,
    LessThan = 10,
    GreaterThan = 11,
    GreaterThanOrEqualTo = 12,
    LessThanOrEqualTo = 13,
}

pub struct Emitter<'a> {
    /// The number of bytes remaining on the stack. Each function will have its stack var
    /// eventually.
    _stack: u32,
    _label_count: usize,
    ast: BoundAST<'a>,
}

impl<'a> Emitter<'a> {
    pub fn new(ast: BoundAST<'a>) -> Self {
        Self {
            _stack: 0,
            _label_count: 0,
            ast,
        }
    }

    pub fn emit(&self) {}

    pub fn test() {
        let x = Operation::GreaterThan as u32;
    }
}
