//! The compiler for the dpp language.

#![warn(clippy::pedantic, clippy::cargo)]

use std::cell::RefCell;
use std::error::Error;
use std::sync::Arc;
use std::{env, fs};

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::analysis::SemanticAnalyzer;
use crate::parse::lexer::{Lexer, Token};
use crate::parse::parser::{Parser, TranslationUnit};

pub mod emitter;
pub mod error_diagnosis;
pub mod parse;

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: Pass this as a command line argument.
    const FILE_PATH: &'static str = "examples/simple_expr.dpp";
    let file_contents = fs::read_to_string(FILE_PATH)?;
    let error_diag = Arc::new(RefCell::new(ErrorDiagnosis::new(FILE_PATH, &file_contents)));

    // Lex -> parse -> analyze -> emit.
    // Pass error diag to each step.
    let tokens = lex(&file_contents, &error_diag)?;
    dbg!(&tokens);
    let translation_unit = parse(tokens, &error_diag)?;
    dbg!(&translation_unit);
    analyze(translation_unit, &error_diag)?;
    Ok(())
}

fn lex<'a, 'b>(
    input: &'a str,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, 'b>>>,
) -> Result<Vec<Token<'a>>, Box<dyn Error>> {
    let mut lexer = Lexer::new(input, error_diag.clone());
    let tokens = lexer.lex();
    error_diag.borrow().check_errors()?;
    Ok(tokens)
}

fn parse<'a, 'b>(
    tokens: Vec<Token<'a>>,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, 'b>>>,
) -> Result<TranslationUnit<'a>, Box<dyn Error>> {
    let mut parser = Parser::new(Arc::new(tokens), error_diag.clone());
    let result = parser.parse();
    error_diag.borrow().check_errors()?;
    Ok(result)
}

fn analyze<'a, 'b>(
    translation_unit: TranslationUnit<'a>,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, 'b>>>,
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
