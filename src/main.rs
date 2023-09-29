//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::cargo)]

use std::cell::RefCell;
use std::error::Error;
use std::fs;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::analysis::SemanticAnalyzer;
use crate::parse::evaluate::Evaluator;
use crate::parse::lexer::{Lexer, Token};
use crate::parse::parser::{Parser, TranslationUnit};

pub mod emitter;
pub mod error_diagnosis;
pub mod parse;

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: Pass this as a command line argument.
    let path = "examples/simple_expr.dpp";
    // TODO: Make this Arc so that we can use the lines in the error diagnosis.
    let file = fs::read_to_string(path)?;
    let error_diag = Arc::new(RefCell::new(ErrorDiagnosis::new(path)));

    // Lex -> parse -> analyze -> emit.
    // Pass error diag to each step.
    let tokens = lex(file, &error_diag)?;
    dbg!(&tokens);
    let translation_unit = parse(tokens, &error_diag)?;
    dbg!(&translation_unit);
    analyze(translation_unit, &error_diag)?;
    Ok(())
}

fn lex(
    file: String,
    error_diag: &Arc<RefCell<ErrorDiagnosis>>,
) -> Result<Vec<Token>, Box<dyn Error>> {
    let mut lexer = Lexer::new(file.as_str(), error_diag.clone());
    let tokens = lexer.lex();
    error_diag.borrow().check_errors()?;
    Ok(tokens)
}

fn parse(
    tokens: Vec<Token>,
    error_diag: &Arc<RefCell<ErrorDiagnosis>>,
) -> Result<TranslationUnit, Box<dyn Error>> {
    let mut parser = Parser::new(Arc::new(tokens), error_diag.clone());
    let result = parser.parse();
    error_diag.borrow().check_errors()?;
    Ok(result)
}

fn analyze(
    translation_unit: TranslationUnit,
    error_diag: &Arc<RefCell<ErrorDiagnosis>>,
) -> Result<(), Box<dyn Error>> {
    let mut analyzer = SemanticAnalyzer::new(error_diag.clone());
    analyzer.analyze(translation_unit);
    error_diag.borrow().check_errors()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {
        assert_eq!(1, 1);
    }
}
