//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::cell::RefCell;
use std::error::Error;
use std::fs;
use std::rc::Rc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::semantic_analyzer::SemanticAnalyzer;

pub mod ast;
pub mod emitter;
pub mod error_diagnosis;
pub mod lexer;
pub mod parser;
pub mod semantic_analyzer;

fn main() -> Result<(), Box<dyn Error>> {
    let path = "examples/first_simple_example.dpp";
    let file = fs::read_to_string(path)?;

    let error_diag = Rc::new(RefCell::new(ErrorDiagnosis::new(path)));
    let mut lexer = Lexer::new(file.as_str(), error_diag.clone());

    let translation_unit = Parser::new(Rc::new(lexer.lex()), error_diag.clone()).parse();
    error_diag.borrow().check_errors()?;
    dbg!(&translation_unit);
    let mut analyzer = SemanticAnalyzer::new(error_diag.clone());
    analyzer.analyze(translation_unit);
    error_diag.borrow().check_errors()?;

    // let file_name = String::from("out/dpp/first_simple_example.asm");
    // let file = File::create(file_name)?;
    // let mut writer = BufWriter::new(&file);
    // emitter.emit(program, &file)?;

    Ok(())
}
