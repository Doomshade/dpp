use crate::parser::{BinaryExpression, Expression, Op, Program};
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::io::BufWriter;

pub struct Emitter {
    program: Program,
    stack: u32,
}

impl Emitter {
    pub const fn new(program: Program) -> Self {
        Self { program, stack: 0 }
    }

    pub fn emit(&mut self, file: &File) -> io::Result<()> {
        {
            let mut writer = BufWriter::new(file);
            Self::emit_binary_start(&mut writer)?;
            self.emit_program(&mut writer)?;
        }
        Ok(())
    }

    fn emit_push(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.stack += 1;
        writer.write_all(format!("    push {register} ; {}\n", self.stack).as_bytes())
    }

    fn emit_pop(&mut self, register: &str, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.stack -= 1;
        writer.write_all(format!("    pop {register} ; {}\n", self.stack).as_bytes())
    }
    fn emit_program(&mut self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        if let Some(expr) = self.program.expression() {
            self.emit_expression(writer, expr)?;
        }

        self.emit_pop("eax", writer)?;
        self.emit_push("eax", writer)?;
        self.emit_push("eax", writer)?;
        self.emit_push("format", writer)?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp,8\n")?;
        writer.write_all(b"    ret\n")?;
        writer.write_all(b"format:\n")?;
        writer.write_all(b"    db '%d', 10, 0\n")?;
        Ok(())
    }

    fn emit_expression(
        &mut self,
        writer: &mut BufWriter<&File>,
        expression: &Expression,
    ) -> io::Result<()> {
        if let Some(num) = expression.num() {
            self.emit_number(writer, *num, "eax")?;
        } else if let Some(binary_expression) = expression.binary_expression() {
            self.emit_binary_expression(writer, binary_expression)?;
        }
        Ok(())
    }

    fn emit_number(
        &mut self,
        writer: &mut BufWriter<&File>,
        num: i64,
        register: &str,
    ) -> io::Result<()> {
        writer.write_all(format!("    mov {register}, {num}\n").as_bytes())?;
        writer.write_all(format!("    push {register}\n").as_bytes())?;
        Ok(())
    }

    fn emit_binary_start(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    global _main\n")?;
        writer.write_all(b"    extern  _printf\n")?;
        writer.write_all(b"    section .text\n")?;
        writer.write_all(b"_main:\n")?;
        Ok(())
    }

    fn emit_binary_expression(
        &mut self,
        writer: &mut BufWriter<&File>,
        binary_expression: &BinaryExpression,
    ) -> io::Result<()> {
        self.emit_expression(writer, binary_expression.lhs())?;
        self.emit_expression(writer, binary_expression.rhs())?;
        writer.write_all(b"    pop ecx\n")?;
        writer.write_all(b"    pop eax\n")?;

        match binary_expression.op() {
            Op::Add => writer.write_all(b"    add eax, ecx\n"),
            Op::Subtract => writer.write_all(b"    sub eax, ecx\n"),
            Op::Multiply => writer.write_all(b"    mul ecx\n"),
            Op::Divide => writer.write_all(b"    div ecx\n"),
        }?;
        writer.write_all(b"    push eax\n")?;
        Ok(())
    }
}
