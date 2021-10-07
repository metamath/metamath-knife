//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.
#![warn(missing_docs)]

pub use filetime;
pub use fnv;
pub use regex;

mod bit_set;
mod segment_set;
mod tree;

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
pub mod util;
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
