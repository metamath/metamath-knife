//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

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
pub mod nameck;
pub mod outline;
pub mod parser;
pub mod proof;
pub mod scopeck;
pub mod util;
pub mod verify;

pub use database::Database;
pub use formula::Formula;
pub use formula::Label;
pub use formula::Symbol;
