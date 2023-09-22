use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

use crate::parser::{BinaryOperator, Block, Expression, Function, Statement, TranslationUnit};
use crate::semantic_analyzer::SemanticAnalyzer;

pub struct Emitter {
    /// The number of bytes remaining on the stack. Each function will have its stack var
    /// eventually.
    _stack: u32,
    _label_count: usize,
    _semantic_analyzer: SemanticAnalyzer,
}

impl Emitter {
    pub fn new(semantic_analyzer: SemanticAnalyzer) -> Self {
        Self {
            _stack: 0,
            _label_count: 0,
            _semantic_analyzer: semantic_analyzer,
        }
    }

    // pub fn emit(&mut self, file: &File) -> io::Result<()> {
    //     {
    //         let mut writer = BufWriter::new(file);
    //         Self::emit_binary_start(&mut writer)?;
    //         // self.emit_program(program, &mut writer)?;
    //         assert_eq!(self.stack, 0, "{} bytes remaining on stack!", self.stack);
    //     }
    //     Ok(())
    // }
    //
    fn _push(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self._stack += 4; // TODO: Hardcoded size
        writer.write_all(format!("    push {register} ; {}\n", self._stack).as_bytes())
    }

    fn _pop(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self._stack -= 4; // TODO: Hardcoded size
        writer.write_all(format!("    pop {register} ; {}\n", self._stack).as_bytes())
    }

    fn _remove_stack_bytes(&mut self, by: u32, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self._stack -= by;
        writer.write_all(format!("    add esp, {} ; {}\n", by, self._stack).as_bytes())?; // TODO:
                                                                                          // Hardcoded size
        Ok(())
    }

    pub fn emit(&mut self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        let translation_unit = self._semantic_analyzer.analyze();
        dbg!(&translation_unit);
        Self::_start(writer)?;
        Self::_end(writer)?;
        Ok(())
    }

    fn _translation_unit(
        &mut self,
        translation_unit: TranslationUnit,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self._functions(translation_unit.functions, writer)
    }

    fn _functions(
        &mut self,
        functions: Vec<Function>,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        for function in functions {
            self._function(function, writer)?;
        }
        Ok(())
    }

    fn _function(&mut self, function: Function, writer: &mut BufWriter<&File>) -> io::Result<()> {
        let label = function.identifier;
        writer.write_all(format!("_{label}:").as_bytes())?;
        self._block(function.block, writer)?;
        Ok(())
    }

    fn _block(&mut self, block: Block, writer: &mut BufWriter<&File>) -> io::Result<()> {
        match block {
            Block { statements } => {
                self._push("ebx", writer)?;
                Self::_mov("ebx", "esp", writer)?;
                for statement in statements {
                    self._statement(statement, writer)?;
                }
                self._pop("ebx", writer)?;
            }
        }
        Ok(())
    }

    fn _statement(
        &mut self,
        statement: Statement,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        if let Statement::IfStatement {
            expression,
            statement,
        } = statement
        {
            self._if_statement(expression, *statement, writer)?;
        };
        Ok(())
    }

    fn _if_statement(
        &mut self,
        expression: Expression,
        _statement: Statement,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self._expression(expression, writer)?;
        self._pop("eax", writer)?;
        let label = self._label();
        writer.write_all(b"    test eax, eax\n")?;
        writer.write_all(format!("    jz {label}\n").as_bytes())?;
        // self.block(block, writer)?;
        writer.write_all(format!("{label}:\n").as_bytes())?;

        Ok(())
    }

    fn _label(&mut self) -> String {
        let label = format!("label{}", self._label_count);
        self._label_count += 1;
        label
    }

    fn _end(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    push format\n")?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp, 8\n")?;
        writer.write_all(b"    xor eax, eax\n")?;
        writer.write_all(b"    ret\n")?;
        Ok(())
    }

    fn _expression(
        &mut self,
        expression: Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        match expression {
            Expression::PpExpression(pp_expression) => self._pp_expression(pp_expression, writer),
            Expression::BoobaExpression(booba) => self._booba_expression(booba, writer),
            Expression::FiberExpression(_fiber_expression) => Ok(()),
            Expression::UnaryExpression { op: _, operand: _ } => Ok(()),
            Expression::BinaryExpression { lhs, op, rhs } => {
                self._binary_expression(*lhs, op, *rhs, writer)
            }
            Expression::IdentifierExpression { identifier } => {
                Self::_mov("eax", identifier.as_str(), writer)?;
                self._push("eax", writer)
            }
            Expression::FunctionCall { .. } => panic!("Not implemeneted"),
            Expression::AssignmentExpression { .. } => panic!("Not implemeneted"),
            Expression::EmptyExpression => panic!("Not implemeneted"),
        }
    }

    fn _binary_expression(
        &mut self,
        lhs: Expression,
        op: BinaryOperator,
        rhs: Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self._expression(lhs, writer)?;
        self._expression(rhs, writer)?;
        self._pop("ecx", writer)?;
        self._pop("eax", writer)?;

        match op {
            BinaryOperator::Add => writer.write_all(b"    add eax, ecx\n")?,
            BinaryOperator::Subtract => writer.write_all(b"    sub eax, ecx\n")?,
            BinaryOperator::Multiply => writer.write_all(b"    mul ecx\n")?,
            BinaryOperator::Divide => writer.write_all(b"    div ecx\n")?,
            BinaryOperator::NotEqual => todo!("Not implemented"),
            BinaryOperator::Equal => todo!("Not implemented"),
            BinaryOperator::GreaterThan => todo!("Not implemented"),
            BinaryOperator::GreaterThanOrEqual => todo!("Not implemented"),
            BinaryOperator::LessThan => todo!("Not implemented"),
            BinaryOperator::LessThanOrEqual => todo!("Not implemented"),
            BinaryOperator::EmptyOperator => todo!("Not implemented"),
        };
        self._push("eax", writer)?;

        Ok(())
    }

    fn _booba_expression(&mut self, booba: bool, writer: &mut BufWriter<&File>) -> io::Result<()> {
        Self::_mov("eax", booba.to_string().as_str(), writer)?;
        self._push("eax", writer)
    }

    fn _pp_expression(
        &mut self,
        pp_expression: i32,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        Self::_mov("eax", pp_expression.to_string().as_str(), writer)?;
        self._push("eax", writer)
    }

    fn _mov(op1: &str, op2: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(format!("    mov {op1}, {op2}\n").as_bytes())
    }

    fn _start(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    global _main\n")?;
        writer.write_all(b"    extern  _printf\n")?;
        writer.write_all(b"format:\n")?;
        writer.write_all(b"    db '%d', 10, 0\n")?;
        writer.write_all(b"    section .text\n")?;
        writer.write_all(b"_main:\n")?;
        Ok(())
    }
}
