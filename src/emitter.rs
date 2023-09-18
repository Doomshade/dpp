use std::io;
use std::io::prelude::*;
use std::io::BufWriter;
use std::fs::File;
use crate::parser::{BinaryExpression, Expression, Op, Program};

pub struct Emitter {
    program: Program,
}

impl Emitter {
    pub fn new(program: Program) -> Self {
        Self {
            program
        }
    }

    pub fn emit(&mut self, file: &File) -> io::Result<()> {
        {
            let mut writer = BufWriter::new(file);
            Self::emit_binary_start(&mut writer)?;
            self.emit_program(&mut writer)?;
            writer.write_all(b"    call _printf\n")?;
            writer.write_all(b"    add esp,4\n")?;
            writer.write_all(b"    ret\n")?;
            // Self::emit_hello_world(&mut writer)?;
        }
        Ok(())
    }

    fn emit_program(&self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        if let Some(expr) = self.program.expression() {
            self.emit_expression(writer, expr)?;
        }
        Ok(())
    }

    fn emit_expression(&self, writer: &mut BufWriter<&File>, expression: &Expression) -> io::Result<()> {
        if let Some(num) = expression.num() {
            // TODO: Emit it properly.
            self.emit_number(writer, *num, "eax")?;
        } else if let Some(binary_expression) = expression.binary_expression() {
            self.emit_binary_expression(writer, binary_expression)?;
        }
        Ok(())
    }

    fn emit_number(&self, writer: &mut BufWriter<&File>, num: i64, register: &str) -> io::Result<()> {
        writer.write_all(format!("    mov {register}, {num}\n").as_bytes())?;
        writer.write_all(format!("    push {register}\n").as_bytes())?;
        Ok(())

    }


    fn emit_binary_start(writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"global _main\n")?;
        writer.write_all(b"    extern  _printf\n")?;
        writer.write_all(b"segment .data\n")?;
        writer.write_all(b"  message:\n")?;
        writer.write_all(b"    db 'Hello World', 0\n")?;
        writer.write_all(b"section .text\n")?;
        writer.write_all(b"  _main:\n")?;
        Ok(())
    }
    // fn emit_hello_world(writer: &mut BufWriter<&File>) -> io::Result<()> {
    //     writer.write_all(b"    push message\n")?;
    //     writer.write_all(b"    call _printf\n")?;
    //     writer.write_all(b"    add esp,4\n")?;
    //     writer.write_all(b"    ret\n")?;
    //
    //     Ok(())
    // }
    fn emit_binary_expression(&self, writer: &mut BufWriter<&File>, binary_expression: &BinaryExpression) -> io::Result<()> {
        self.emit_expression(writer, binary_expression.lhs())?;
        self.emit_expression(writer, binary_expression.rhs())?;
        writer.write_all(b"    pop ebx\n")?;
        writer.write_all(b"    pop eax\n")?;

        match binary_expression.op() {
            Op::Add =>      writer.write_all(b"    add eax, ebx\n"),
            Op::Subtract => writer.write_all(b"    sub eax, ebx\n"),
            Op::Multiply => writer.write_all(b"    mul ebx\n"),
            Op::Divide =>   writer.write_all(b"    div ebx\n"),
        }?;
        writer.write_all(b"    push eax\n")?;
        Ok(())
    }
}
