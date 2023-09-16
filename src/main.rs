use crate::lexer::Lexer;
use crate::parser::Parser;
use std::fs;
use std::fs::File;
use crate::emitter::Emitter;

mod ast;
mod lexer;
mod parser;
mod emitter;

fn main() {
    let file =
        fs::read_to_string("examples/first_simple_example.dpp").expect("Should have been able to read the file");

    let lexer = Lexer::new(file.as_str());
    let mut parser = Parser::new(lexer);
    let program = parser.parse().expect("Syntax error occured.");
    let mut emitter = Emitter::new(program);
    let file_name = String::from("out/dpp/first_simple_example.asm");
    let file = File::create(&file_name).unwrap_or_else(|_| panic!("Failed to create file {file_name}"));
    dbg!(emitter.emit(&file)).expect("Failed to emit assembly code");
}
