use crate::lexer::Lexer;
use std::fs;

mod lexer;
mod parse;

fn main() {
    let file =
        fs::read_to_string("examples/main.dpp").expect("Should have been able to read the file");

    let mut lexer = Lexer::new(file.as_str());
    lexer.lex();
}
