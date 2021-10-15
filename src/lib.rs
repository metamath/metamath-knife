//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

// rust lints we want
#![warn(
    bare_trait_objects,
    elided_lifetimes_in_paths,
    missing_docs,
    missing_copy_implementations,
    missing_debug_implementations,
    future_incompatible,
    rust_2018_idioms,
    trivial_numeric_casts,
    variant_size_differences,
    unreachable_pub,
    unused,
    missing_docs
)]
// all the clippy
#![warn(clippy::all, clippy::pedantic, clippy::nursery, clippy::cargo)]
// all the clippy::restriction lints we want
#![warn(
    clippy::float_arithmetic,
    clippy::get_unwrap,
    clippy::inline_asm_x86_att_syntax,
    clippy::rest_pat_in_fully_bound_structs,
    clippy::string_add
)]
// // all the clippy lints we don't want
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    clippy::enum_glob_use,
    clippy::if_not_else,
    clippy::inline_always,
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::option_if_let_else,
    clippy::redundant_pub_crate,
    clippy::semicolon_if_nothing_returned,
    clippy::shadow_unrelated,
    clippy::too_many_lines,
    clippy::unseparated_literal_suffix,
    clippy::struct_excessive_bools,
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::use_self
)]

mod bit_set;
mod segment_set;
mod tree;
mod util;

pub mod database;
pub mod diag;
pub mod export;
pub mod formula;
pub mod grammar;
pub mod line_cache;
pub mod nameck;
pub mod outline;
pub mod parser;
pub mod proof;
pub mod scopeck;
pub mod verify;

#[cfg(test)]
mod formula_tests;
#[cfg(test)]
mod grammar_tests;
#[cfg(test)]
mod parser_tests;
#[cfg(test)]
mod util_tests;

pub use database::Database;
pub use formula::Formula;
pub use formula::Label;
pub use formula::Symbol;
