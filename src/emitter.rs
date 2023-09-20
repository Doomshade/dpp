use crate::parser::{
    BoundBinaryExpression, BoundBoobaExpression, BoundPpExpression, Expression, Op,
};
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

#[derive(Default)]
pub struct Emitter {
    /// The number of bytes remaining on the stack. Each function will have its stack var
    /// eventually.
    stack: u32,
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
        expression: &Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        Self::emit_binary_start(writer)?;
        self.expression(expression, writer)?;
        Self::emit_end(writer)
    }

    fn emit_end(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    push format\n")?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp, 8\n")?;
        writer.write_all(b"    xor eax, eax\n")?;
        writer.write_all(b"    ret\n")?;
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        match expression {
            Expression::PpExpression(pp_expression) => self.pp_expression(pp_expression, writer),
            Expression::BoobaExpression(booba_expression) => {
                self.booba_expression(booba_expression, writer)
            }
            Expression::FiberExpression(_fiber_expression) => Ok(()),
            Expression::UnaryExpression(_unary_expression) => Ok(()),
            Expression::BinaryExpression(binary_expression) => {
                self.binary_expression(binary_expression, writer)
            }
        }
    }

    fn binary_expression(
        &mut self,
        binary_expression: &BoundBinaryExpression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self.expression(binary_expression.lhs(), writer)?;
        self.expression(binary_expression.rhs(), writer)?;
        self.pop("ecx", writer)?;
        self.pop("eax", writer)?;

        match binary_expression.op() {
            Op::Add => writer.write_all(b"    add eax, ecx\n")?,
            Op::Subtract => writer.write_all(b"    sub eax, ecx\n")?,
            Op::Multiply => writer.write_all(b"    mul ecx\n")?,
            Op::Divide => writer.write_all(b"    div ecx\n")?,
            Op::NotEqual => writer.write_all(b"add eax, ecx")?,
            Op::Equal => writer.write_all(b"add eax, ecx")?,
            Op::GreaterThan => writer.write_all(b"add eax, ecx")?,
            Op::GreaterThanOrEqual => writer.write_all(b"add eax, ecx")?,
            Op::LessThan => writer.write_all(b"add eax, ecx")?,
            Op::LessThanOrEqual => writer.write_all(b"add eax, ecx")?,
            Op::Not => writer.write_all(b"add eax, ecx")?,
            Op::Negate => writer.write_all(b"add eax, ecx")?,
        };
        self.push("eax", writer)?;

        Ok(())
    }

    fn booba_expression(
        &mut self,
        booba_expression: &BoundBoobaExpression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self.mov("eax", booba_expression.booba().to_string().as_str(), writer)?;
        self.push("eax", writer)
    }

    fn pp_expression(
        &mut self,
        pp_expression: &BoundPpExpression,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        self.mov("eax", pp_expression.pp().to_string().as_str(), writer)?;
        self.push("eax", writer)
    }

    fn mov(&mut self, op1: &str, op2: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(format!("    mov {op1}, {op2}\n").as_bytes())
    }


    fn emit_binary_start(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    global _main\n")?;
        writer.write_all(b"    extern  _printf\n")?;
        writer.write_all(b"format:\n")?;
        writer.write_all(b"    db '%d', 10, 0\n")?;
        writer.write_all(b"    section .text\n")?;
        writer.write_all(b"_main:\n")?;
        Ok(())
    }
}
