//! Export support for mmj2 proof files.

use diag::Diagnostic;
use nameck::Nameset;
use parser::StatementRef;
use regex::Regex;
use scopeck::ScopeResult;
use segment_set::SegmentSet;
use std::io::Write;

/// Export an mmp file for a given statement.
pub fn export_mmp<W: Write>(segments: &SegmentSet,
                            nset: &Nameset,
                            scope: &ScopeResult,
                            stmt: StatementRef,
                            out: &mut W)
                            -> Result<(), Diagnostic> {
    try!(writeln!(out,
                  "$( <MM> <PROOF_ASST> THEOREM={}  LOC_AFTER=?\n",
                  String::from_utf8_lossy(stmt.label())));
    if let Some(comment) = stmt.associated_comment() {
        let mut span = comment.span();
        span.start += 2;
        span.end -= 3;
        println!("{:?}", span);
        let cstr = Regex::new(r"\n +")
            .unwrap()
            .replace(&String::from_utf8_lossy(span.as_ref(&comment.segment().segment.buffer)),
                     "\n  ");
        try!(writeln!(out, "*{}\n", cstr));
    }
    
    try!(writeln!(out, "\n$)"));
    Ok(())
}