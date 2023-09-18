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
            let stack = &mut 0u32;
            self.emit_program(stack, &mut writer)?;
        }
        Ok(())
    }

    fn emit_push(
        &self,
        stack: &mut u32,
        register: &str,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        *stack += 1;
        writer.write_all(format!("    push {register} ; {}\n", self.stack).as_bytes())
    }

    fn emit_pop(
        &self,
        stack: &mut u32,
        register: &str,
        writer: &mut BufWriter<&File>,
    ) -> io::Result<()> {
        *stack -= 1;

        writer.write_all(format!("    pop {register} ; {}\n", self.stack).as_bytes())
    }
    fn emit_program(&mut self, stack: &mut u32, writer: &mut BufWriter<&File>) -> io::Result<()> {
        if let Some(expr) = self.program.expression() {
            self.emit_expression(stack, writer, expr)?;
        }

        self.emit_pop(stack, "eax", writer)?;
        self.emit_push(stack, "eax", writer)?;
        self.emit_push(stack, "eax", writer)?;
        self.emit_push(stack, "format", writer)?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp,8\n")?;
        writer.write_all(b"    ret\n")?;
        writer.write_all(b"format:\n")?;
        writer.write_all(b"    db '%d', 10, 0\n")?;
        Ok(())
    }

    fn emit_expression(
        &self,
        stack: &mut u32,
        writer: &mut BufWriter<&File>,
        expression: &Expression,
    ) -> io::Result<()> {
        if let Some(num) = expression.num() {
            self.emit_number(stack, writer, *num, "eax")?;
        } else if let Some(binary_expression) = expression.binary_expression() {
            self.emit_binary_expression(stack, writer, binary_expression)?;
        }
        Ok(())
    }

    fn emit_number(
        &self,
        stack: &mut u32,

        writer: &mut BufWriter<&File>,
        num: i64,
        register: &str,
    ) -> io::Result<()> {
        writer.write_all(format!("    mov {register}, {num}\n").as_bytes())?;
        self.emit_push(stack, register, writer)?;
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
        &self,
        stack: &mut u32,
        writer: &mut BufWriter<&File>,
        binary_expression: &BinaryExpression,
    ) -> io::Result<()> {
        self.emit_expression(stack, writer, binary_expression.lhs())?;
        self.emit_expression(stack, writer, binary_expression.rhs())?;
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
