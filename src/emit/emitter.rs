use crate::parse::analysis::{BoundAST, SemanticAnalyzer};

enum Instruction {
    /// Load (i.e. push onto the stack) the value of the cell identified by level and offset. A level value of 0 means the variable is in the currently executing procedure; 1 means it's in the immediately enclosing region of the program. 2 means it's the region outside that (in PL/0 as in Pascal procedures can nest indefinitely). The offset distinguishes among the variables declared at that level.
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

#[derive(Default)]
pub struct Emitter;

impl Emitter {
    pub fn test() {
        let x = Operation::GreaterThan as u32;
    }
    pub fn emit_instruction(instruction: Instruction) {

    }
}
