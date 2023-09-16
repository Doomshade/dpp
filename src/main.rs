use crate::lexer::Lexer;
use crate::parser::Parser;
use std::fs;

mod ast;
mod lexer;
mod parser;

fn main() {
    let file =
        fs::read_to_string("examples/first_simple_example.dpp").expect("Should have been able to read the file");

    let lexer = Lexer::new(file.as_str());
    let mut parser = Parser::new(lexer);
    let ast = parser.parse();
    dbg!(ast).expect("TODO: panic message");
}
