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
        Self {
            program
        }
    }

    pub fn emit(&mut self, file: &File) -> io::Result<()> {
        {
            let mut writer = BufWriter::new(file);
            writer.write_all(b"global _main\n")?;
            writer.write_all(b"    extern  _printf\n")?;
            writer.write_all(b"segment .data\n")?;
            writer.write_all(b"  message:\n")?;
            writer.write_all(b"    db 'Hello World', 0\n")?;
            writer.write_all(b"section .text\n")?;
            writer.write_all(b"  _main:\n")?;
            // self.emit_program(&mut writer)?;
            self.emit_hello_world(&mut writer)?;
        }
        Ok(())
    }
    //
    // fn emit_program(&self, writer: &mut BufWriter<&File>) -> io::Result<()> {
    //     self.emit_binary_expression(self.program.binary_expression(), writer)
    // }
    //
    fn emit_hello_world(&self, writer: &mut BufWriter<&File>) -> io::Result<()> {
        writer.write_all(b"    push message\n")?;
        writer.write_all(b"    call _printf\n")?;
        writer.write_all(b"    add esp,4\n")?;
        writer.write_all(b"    ret\n")?;

        Ok(())
    }
    //
    // fn emit_binary_expression(&self, binary_expression: &BinaryExpression, writer: &mut BufWriter<&File>) -> io::Result<()> {
    //     let lhs = binary_expression.lhs();
    //     let rhs = binary_expression.rhs();
    //     writer.write_all(format!("    mov eax, {}\n", lhs.num).as_bytes())?;
    //     writer.write_all(format!("    mov ebx, {}\n", rhs.num).as_bytes())?;
    //     match binary_expression.op() {
    //         Op::Add => {
    //             writer.write_all(b"    add eax, ebx\n")?;
    //         }
    //     }
    //     writer.write_all(b"    push eax\n")?;
    //
    //     Ok(())
    // }
}
