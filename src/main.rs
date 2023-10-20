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

use std::env;
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

use crate::parse::compiler::DppCompiler;

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
    const OUTPUT: &'static str = "out/dpp/test.pl0";
    const PL0_INTERPRET_PATH: &'static str = "resources/pl0_interpret/bin/refint_pl0_ext.exe";
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        let error = ArgsError { args };
        eprintln!("{}", &error);
        return Err(Box::new(error));
    }

    let file_path = &args[1];
    DppCompiler::compile_translation_unit(file_path, OUTPUT, PL0_INTERPRET_PATH)?;
    Ok(())
}
