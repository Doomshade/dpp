use std::fs;
use crate::lexer::Lexer;

mod lexer;
mod parse;

fn main() {
    let mut lexer = Lexer::default();
    let file = fs::read_to_string("examples/main.dpp")
        .expect("Should have been able to read the file");

    let vec = lexer.lex(file.as_str());
    println!("{:?}", vec);
}
