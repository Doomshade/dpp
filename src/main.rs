#![warn(
    clippy::all,
    clippy::restriction,
    clippy::pedantic,
    clippy::nursery,
    clippy::cargo
)]
use crate::emitter::Emitter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use std::fs;
use std::fs::File;

mod ast;
mod emitter;
mod lexer;
mod parser;

fn main() {
    let file = fs::read_to_string("examples/first_simple_example.dpp")
        .expect("Should have been able to read the file");

    let lexer = Lexer::new(file.as_str());
    let mut parser = Parser::new(lexer);
    let program = parser.parse().expect("Syntax error occured.");
    parser.print_parse_tree();
    let mut emitter = Emitter::new(program);
    let file_name = String::from("out/dpp/first_simple_example.asm");
    let file = File::create(&file_name).unwrap_or_else(|er| {
        panic!(
            "Failed to create file \
    {file_name}: {er}"
        )
    });
    dbg!(emitter.emit(&file)).expect("Failed to emit assembly code");
}
