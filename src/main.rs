//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::cell::RefCell;
use std::error::Error;
use std::fs;
use std::fs::File;
use std::io::BufWriter;
use std::rc::Rc;

use crate::emitter::Emitter;
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
    let file = fs::read_to_string(&path)?;

    let error_diag = Rc::new(RefCell::new(ErrorDiagnosis::new(path)));
    let mut lexer = Lexer::new(file.as_str(), error_diag.clone());
    let tokens = Rc::new(lexer.lex());
    error_diag.borrow().check_errors()?;

    let translation_unit = Parser::new(tokens, error_diag.clone()).parse();
    error_diag.borrow().check_errors()?;
    let analyzer = SemanticAnalyzer::new(translation_unit);
    error_diag.clone().borrow().check_errors()?;
    let mut emitter = Emitter::new(analyzer);
    error_diag.clone().borrow().check_errors()?;

    let file_name = String::from("out/dpp/first_simple_example.asm");
    let file = File::create(file_name)?;
    let mut writer = BufWriter::new(&file);
    emitter.emit(&mut writer)?;
    // emitter.emit(program, &file)?;

    Ok(())
}
