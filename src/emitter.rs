use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

use crate::parser::{BinaryOperator, Block, Expression, Function, Statement, TranslationUnit};

#[derive(Default)]
pub struct Emitter {
    /// The number of bytes remaining on the stack. Each function will have its stack var
    /// eventually.
    stack: u32,
    label_count: usize,
}

impl Emitter {
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
    fn push(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.stack += 4; // TODO: Hardcoded size
        writer.write_all(format!("    push {register} ; {}\n", self.stack).as_bytes())
    }

    fn pop(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.stack -= 4; // TODO: Hardcoded size
        writer.write_all(format!("    pop {register} ; {}\n", self.stack).as_bytes())
    }

    fn remove_stack_bytes(&mut self, by: u32, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.stack -= by;
        writer.write_all(format!("    add esp, {} ; {}\n", by, self.stack).as_bytes())?; // TODO:
                                                                                         // Hardcoded size
        Ok(())
    }

    pub fn emit(
        &mut self,
        _translation_unit: TranslationUnit,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        Self::start(writer)?;
        Self::end(writer)?;
        Ok(())
    }

    fn translation_unit(
        &mut self,
        translation_unit: TranslationUnit,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        match translation_unit {
            TranslationUnit {
                functions,
                variables: _,
            } => self.functions(functions, writer),
        }
    }

    fn functions(
        &mut self,
        functions: Vec<Function>,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        for function in functions {
            self.function(function, writer)?;
        }
        Ok(())
    }

    fn function(&mut self, function: Function, writer: &mut BufWriter<&File>) -> io::Result<()> {
        let label = function.identifier;
        writer.write_all(format!("_{label}:").as_bytes())?;
        self.block(function.block, writer)?;
        Ok(())
    }

    fn block(&mut self, block: Block, writer: &mut BufWriter<&File>) -> io::Result<()> {
        match block {
            Block { statements } => {
                self.push("ebx", writer)?;
                Self::mov("ebx", "esp", writer)?;
                for statement in statements {
                    self.statement(statement, writer)?;
                }
                self.pop("ebx", writer)?;
            }
        }
        Ok(())
    }

    fn statement(&mut self, statement: Statement, writer: &mut BufWriter<&File>) -> io::Result<()> {
        match statement {
            Statement::VariableAssignment {
                identifier: _,
                expression,
            } => self.expression(expression, writer)?,

            Statement::VariableDeclaration {
                identifier: _,
                data_type: _,
            } => {}
            Statement::VariableDeclarationAndAssignment {
                identifier: _,
                data_type: _,
                expression,
            } => self.expression(expression, writer)?,
            Statement::IfStatement { expression, block } => {
                self.if_statement(expression, *block, writer)?
            }
            Statement::ReturnStatement { expression } => {}
        };
        Ok(())
    }

    fn if_statement(
        &mut self,
        expression: Expression,
        block: Block,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self.expression(expression, writer)?;
        self.pop("eax", writer)?;
        let label = self.label();
        writer.write_all(b"    test eax, eax\n")?;
        writer.write_all(format!("    jz {label}\n").as_bytes())?;
        self.block(block, writer)?;
        writer.write_all(format!("{label}:\n").as_bytes())?;

        Ok(())
    }

    fn label(&mut self) -> String {
        let label = format!("label{}", self.label_count);
        self.label_count += 1;
        label
    }

    fn end(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    push format\n")?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp, 8\n")?;
        writer.write_all(b"    xor eax, eax\n")?;
        writer.write_all(b"    ret\n")?;
        Ok(())
    }

    fn expression(
        &mut self,
        expression: Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        match expression {
            Expression::PpExpression(pp_expression) => self.pp_expression(pp_expression, writer),
            Expression::BoobaExpression(booba) => self.booba_expression(booba, writer),
            Expression::FiberExpression(_fiber_expression) => Ok(()),
            Expression::UnaryExpression { op: _, operand: _ } => Ok(()),
            Expression::BinaryExpression { lhs, op, rhs } => {
                self.binary_expression(*lhs, op, *rhs, writer)
            }
            Expression::IdentifierExpression { identifier } => {
                Self::mov("eax", identifier.as_str(), writer)?;
                self.push("eax", writer)
            }
        }
    }

    fn binary_expression(
        &mut self,
        lhs: Expression,
        op: BinaryOperator,
        rhs: Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self.expression(lhs, writer)?;
        self.expression(rhs, writer)?;
        self.pop("ecx", writer)?;
        self.pop("eax", writer)?;

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
            _ => unreachable!(),
        };
        self.push("eax", writer)?;

        Ok(())
    }

    fn booba_expression(&mut self, booba: bool, writer: &mut BufWriter<&File>) -> io::Result<()> {
        Self::mov("eax", booba.to_string().as_str(), writer)?;
        self.push("eax", writer)
    }

    fn pp_expression(
        &mut self,
        pp_expression: i32,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        Self::mov("eax", pp_expression.to_string().as_str(), writer)?;
        self.push("eax", writer)
    }

    fn mov(op1: &str, op2: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(format!("    mov {op1}, {op2}\n").as_bytes())
    }

    fn start(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    global _main\n")?;
        writer.write_all(b"    extern  _printf\n")?;
        writer.write_all(b"format:\n")?;
        writer.write_all(b"    db '%d', 10, 0\n")?;
        writer.write_all(b"    section .text\n")?;
        writer.write_all(b"_main:\n")?;
        Ok(())
    }
}
