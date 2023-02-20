//! Verification of definitions
//!
//! Implement verification of definitions per the set.mm/iset.mm conventions.
//! If the "exceptions" string is empty we use the "typical" set.mm values.
//! The current typical values are "ax-*,df-bi,df-clab,df-cleq,df-clel".
//! For glob syntax see: https://docs.rs/globset/latest/globset/
//! but in the future we may reduce the glob language sophistication.
//! For more information see:
//! https://us.metamath.org/mpeuni/conventions.html
//! https://github.com/digama0/mmj2/blob/master/mmj2jar/macros/definitionCheck.js
//! and "Metamath: A Computer Language for Mathematical Proofs" by
//! Norman Megill and David A. Wheeler, 2019, page 155.

use crate::diag::Diagnostic;
use crate::statement::StatementAddress;
use crate::{Database, StatementRef, StatementType};
use globset::{Glob, GlobSetBuilder};

/// Verify the definition in this statement.
/// Return a diagnostic if there's a problem, else None for no problem.
fn verify_definition_statement(stmt: &StatementRef<'_>) -> Option<Diagnostic> {
    // Rule 1: New definitions must be introduced using = or <->
    // TODO
    if let Ok(label) = std::str::from_utf8(stmt.label()) {
        println!(" Need to check: $a statement {}", label);
    }

    None
}

impl Database {
    /// Verify that definitions meet set.mm/iset.mm conventions;
    /// exclude *exceptions* from this check.
    #[must_use]
    pub fn verify_definitions(&self, exceptions: &str) -> Vec<(StatementAddress, Diagnostic)> {
        let mut diags = vec![];
        let exceptions_str = if exceptions.is_empty() {
            "ax-*,df-bi,df-clab,df-cleq,df-clel" // Default for set.mm.
        } else {
            exceptions
        };
        let vector_exceptions: Vec<&str> = exceptions_str.split(",").collect();

        // Compile the glob patterns before using them in a loop.
        // The Rust glob libraries only support &str, not [u8] byte arrays,
        // so we will convert every label to &str to use a glob library.
        // This causes some unnecessary overhead, but it's less code to write.
        // The Rust glob libraries are absurdly over-featured for our use case
        // *and* can't handle [u8]. In the future we might replace this with
        // a function that meets our needs and stop using this library.
        let mut builder = GlobSetBuilder::new();
        for exception in vector_exceptions {
            let glob = Glob::new(exception).expect("Failed to compile pattern");
            builder.add(glob);
        }
        let compiled_exceptions = builder.build().unwrap();

        let typecode_provable = "|-".as_bytes();

        for stmt in self.statements() {
            match stmt.statement_type() {
                StatementType::Axiom => {
                    if let Some(typecode) = stmt.math_iter().next() {
                        if *typecode == *typecode_provable { // Typecode is |-
                            if let Ok(label) = std::str::from_utf8(stmt.label()) {
                                if !compiled_exceptions.is_match(label) {
                                    // println!("DEBUG: Processing $a {}", label);
                                    let result = verify_definition_statement(&stmt);
                                    if let Some(problem) = result {
                                        diags.push((stmt.address(), problem));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {} // TODO: Non-axioms
            }
        }
        diags
    }
}
