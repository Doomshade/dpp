//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::error::Error;
use std::fs;
use std::fs::File;

use crate::emitter::Emitter;
use crate::lexer::Lexer;
use crate::parser::Parser;

pub mod ast;
pub mod emitter;
pub mod lexer;
pub mod parser;

fn main() -> Result<(), Box<dyn Error>> {
    let file = fs::read_to_string("examples/first_simple_example.dpp")?;

    let lexer = Lexer::new(file.as_str());
    let mut parser = Parser::new(lexer);
    let program = parser.parse().expect("Syntax error occured.");
    parser.print_parse_tree();
    let mut emitter = Emitter::default();
    let file_name = String::from("out/dpp/first_simple_example.asm");
    let file = File::create(file_name)?;
    emitter.emit(program, &file)?;

    Ok(())
}
