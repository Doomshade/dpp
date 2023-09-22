//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]

use std::error::Error;
use std::fs;
use std::fs::File;
use std::io::BufWriter;

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

    let error_diag = ErrorDiagnosis::new(path);
    let lexer = Lexer::new(file.as_str(), error_diag);
    let parser = Parser::new(lexer);
    let analyzer = SemanticAnalyzer::new(parser);
    let mut emitter = Emitter::new(analyzer);

    let file_name = String::from("out/dpp/first_simple_example.asm");
    let file = File::create(file_name)?;
    let mut writer = BufWriter::new(&file);
    emitter.emit(&mut writer)?;
    // emitter.emit(program, &file)?;

    Ok(())
}
