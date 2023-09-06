use crate::lexer::Lexer;
use crate::parser::Parser;
use std::fs;

mod ast;
mod lexer;
mod parser;

fn main() {
    let file =
        fs::read_to_string("examples/main.dpp").expect("Should have been able to read the file");

    let lexer = Lexer::new(file);
    let mut parser = Parser::new(lexer);
    match parser.parse() {
        Ok(ast) => println!("OK: {ast:?}"),
        Err(err) => panic!("ERROR: {err:?}"),
    }
}
