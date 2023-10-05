//! The compiler for the dpp language.
#![deny(unsafe_code)]
#![warn(
clippy::all,
clippy::await_holding_lock,
clippy::char_lit_as_u8,
clippy::checked_conversions,
clippy::dbg_macro,
clippy::debug_assert_with_mut_call,
clippy::doc_markdown,
clippy::empty_enum,
clippy::enum_glob_use,
clippy::exit,
clippy::expl_impl_clone_on_copy,
clippy::explicit_deref_methods,
clippy::explicit_into_iter_loop,
clippy::fallible_impl_from,
clippy::filter_map_next,
clippy::flat_map_option,
clippy::float_cmp_const,
clippy::fn_params_excessive_bools,
clippy::from_iter_instead_of_collect,
clippy::if_let_mutex,
clippy::implicit_clone,
clippy::imprecise_flops,
clippy::inefficient_to_string,
clippy::invalid_upcast_comparisons,
clippy::large_digit_groups,
clippy::large_stack_arrays,
clippy::large_types_passed_by_value,
clippy::let_unit_value,
clippy::linkedlist,
clippy::lossy_float_literal,
clippy::macro_use_imports,
clippy::manual_ok_or,
clippy::map_err_ignore,
clippy::map_flatten,
clippy::map_unwrap_or,
clippy::match_on_vec_items,
clippy::match_same_arms,
clippy::match_wild_err_arm,
clippy::match_wildcard_for_single_variants,
clippy::mem_forget,
clippy::mismatched_target_os,
clippy::missing_enforced_import_renames,
clippy::mut_mut,
clippy::mutex_integer,
clippy::needless_borrow,
clippy::needless_continue,
clippy::needless_for_each,
clippy::option_option,
clippy::path_buf_push_overwrite,
clippy::ptr_as_ptr,
clippy::rc_mutex,
clippy::ref_option_ref,
clippy::rest_pat_in_fully_bound_structs,
clippy::same_functions_in_if_condition,
clippy::semicolon_if_nothing_returned,
clippy::single_match_else,
clippy::string_add_assign,
clippy::string_add,
clippy::string_lit_as_bytes,
clippy::string_to_string,
clippy::todo,
clippy::trait_duplication_in_bounds,
clippy::unimplemented,
clippy::unnested_or_patterns,
clippy::unused_self,
clippy::useless_transmute,
clippy::verbose_file_reads,
clippy::zero_sized_map_values,
future_incompatible,
nonstandard_style,
rust_2018_idioms
)]

use std::cell::RefCell;
use std::error::Error;
use std::fs;
use std::sync::Arc;

use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::analysis::SemanticAnalyzer;
use crate::parse::lexer::{Lexer, Token};
use crate::parse::parser::{Parser, TranslationUnit};

pub mod emitter;
pub mod error_diagnosis;
pub mod parse;

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: Pass this as a command line argument.
    const FILE_PATH: &str = "examples/simple_expr.dpp";
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

fn lex<'a>(
    input: &'a str,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, '_>>>,
) -> Result<Vec<Token<'a>>, Box<dyn Error>> {
    let mut lexer = Lexer::new(input, error_diag.clone());
    let tokens = lexer.lex();
    error_diag.borrow().check_errors()?;
    Ok(tokens)
}

fn parse<'a>(
    tokens: Vec<Token<'a>>,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, '_>>>,
) -> Result<TranslationUnit<'a>, Box<dyn Error>> {
    let mut parser = Parser::new(Arc::new(tokens), error_diag.clone());
    let result = parser.parse();
    error_diag.borrow().check_errors()?;
    Ok(result)
}

fn analyze<'a>(
    translation_unit: TranslationUnit<'a>,
    error_diag: &Arc<RefCell<ErrorDiagnosis<'a, '_>>>,
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
