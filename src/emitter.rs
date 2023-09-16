use std::io;
use std::io::prelude::*;
use std::io::BufWriter;
use std::fs::File;
use crate::parser::{BinaryExpression, Op, Program};

pub struct Emitter {
    program: Program,
}

impl Emitter {
    pub fn new(program: Program) -> Self {
        Emitter {
            program
        }
    }

    pub fn emit(&mut self, file: &File) -> io::Result<()> {
        {
            let mut writer = BufWriter::new(file);
            writer.write_all("global _main\n".as_bytes())?;
            writer.write_all("    extern  _printf\n".as_bytes())?;
            writer.write_all("segment .data\n".as_bytes())?;
            writer.write_all("  message:\n".as_bytes())?;
            writer.write_all("    db 'Hello World', 0\n".as_bytes())?;
            writer.write_all("section .text\n".as_bytes())?;
            writer.write_all("  _main:\n".as_bytes())?;
            // self.emit_program(&mut writer)?;
            self.emit_hello_world(&mut writer)?;
        }
        Ok(())
    }

    fn emit_program(&self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        self.emit_binary_expression(self.program.binary_expression(), writer)
    }

    fn emit_hello_world(&self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all("    push message\n".as_bytes())?;
        writer.write_all("    call _printf\n".as_bytes())?;
        writer.write_all("    add esp,4\n".as_bytes())?;
        writer.write_all("    ret\n".as_bytes())?;

        Ok(())
    }

    fn emit_binary_expression(&self, binary_expression: &BinaryExpression, writer: &mut BufWriter<&File>) -> io::Result<()> {
        let num1 = binary_expression.num1();
        let num2 = binary_expression.num2();
        writer.write_all(format!("    mov eax, {}\n", num1).as_bytes())?;
        writer.write_all(format!("    mov ebx, {}\n", num2).as_bytes())?;
        match binary_expression.op() {
            Op::Add => {
                writer.write_all("    add eax, ebx\n".as_bytes())?;
            }
        }
        writer.write_all("    push eax\n".as_bytes())?;

        Ok(())
    }
}