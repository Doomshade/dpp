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

use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

use std::process::{Command, Stdio};
use std::{env, fs};

use crate::emit::emitter::Emitter;
use crate::error_diagnosis::ErrorDiagnosis;
use crate::parse::analysis::{GlobalScope, SemanticAnalyzer};
use crate::parse::lexer::{Lexer, Token};
use crate::parse::parser::{Parser, TranslationUnit};

mod emit;
pub mod error_diagnosis;
mod parse;

#[derive(Debug)]
struct ArgsError {
    args: Vec<String>,
}

impl Display for ArgsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Usage: ./{} <file.dpp>", self.args[0])
    }
}

impl Error for ArgsError {}

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: Pass this as a command line argument.
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        let error = ArgsError { args };
        eprintln!("{}", &error);
        return Err(Box::new(error));
    }

    let file_path = &args[1];

    let file_contents = fs::read_to_string(file_path)?;
    let error_diag = std::rc::Rc::new(std::cell::RefCell::new(ErrorDiagnosis::new(
        file_path,
        &file_contents,
    )));

    // Lex -> parse -> analyze -> emit.
    // Pass error diag to each step.
    let tokens = lex(&file_contents, &error_diag)?;
    let translation_unit = parse(tokens, &error_diag)?;
    const OUTPUT: &str = "out/dpp/test.pl0";

    analyze_and_emit(translation_unit, &error_diag, OUTPUT)?;
    let child = Command::new("resources/pl0_interpret.exe")
        .args(["-a", "+d", "+l", "+i", "+t", "+s", OUTPUT])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let output = String::from_utf8(child.wait_with_output()?.stdout)?;
    println!("{output}");
    Ok(())
}

fn lex<'a>(
    input: &'a str,
    error_diag: &std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, '_>>>,
) -> Result<Vec<Token<'a>>, Box<dyn Error>> {
    let mut lexer = Lexer::new(input, error_diag.clone());
    let tokens = lexer.lex();
    error_diag.borrow().check_errors()?;
    Ok(tokens)
}

fn parse<'a>(
    tokens: Vec<Token<'a>>,
    error_diag: &std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, '_>>>,
) -> Result<TranslationUnit<'a>, Box<dyn Error>> {
    let mut parser = Parser::new(std::rc::Rc::new(tokens), error_diag.clone());
    let result = parser.parse();
    error_diag.borrow().check_errors()?;
    Ok(result)
}

fn analyze_and_emit<'a>(
    translation_unit: TranslationUnit<'a>,
    error_diag: &std::rc::Rc<std::cell::RefCell<ErrorDiagnosis<'a, '_>>>,
    output: &str,
) -> Result<(), Box<dyn Error>> {
    let file = fs::File::create(output).expect("Unable to create file");
    let writer = std::io::BufWriter::new(file);

    let function_scopes = std::rc::Rc::new(std::cell::RefCell::new(Vec::default()));
    let global_scope = std::rc::Rc::new(std::cell::RefCell::new(GlobalScope::default()));

    let emitter = Emitter::new(
        writer,
        std::rc::Rc::clone(&function_scopes),
        std::rc::Rc::clone(&global_scope),
    );
    let mut analyzer = SemanticAnalyzer::new(
        error_diag.clone(),
        function_scopes.clone(),
        global_scope.clone(),
        emitter,
    );
    analyzer.analyze(&translation_unit);
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
