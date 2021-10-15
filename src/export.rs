//! Export support for mmj2 proof files.

use crate::diag::Diagnostic;
use crate::parser::as_str;
use crate::parser::StatementRef;
use crate::parser::StatementType;
use crate::parser::TokenRef;
use crate::proof::ProofStyle;
use crate::proof::ProofTreeArray;
use crate::proof::ProofTreePrinter;
use crate::Database;
use regex::Regex;
use std::error;
use std::fmt;
use std::io;
use std::io::Write;
use std::str;

/// The error type for [`Database::export_mmp`].
#[derive(Debug)]
pub enum ExportError {
    /// IO Error during write
    Io(io::Error),
    /// Proof verification error
    Verify(Diagnostic),
    /// Formatting error
    Format(fmt::Error),
}

impl From<io::Error> for ExportError {
    fn from(err: io::Error) -> ExportError {
        ExportError::Io(err)
    }
}
impl From<Diagnostic> for ExportError {
    fn from(err: Diagnostic) -> ExportError {
        ExportError::Verify(err)
    }
}
impl From<fmt::Error> for ExportError {
    fn from(err: fmt::Error) -> ExportError {
        ExportError::Format(err)
    }
}

impl fmt::Display for ExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ExportError::Io(ref err) => write!(f, "IO error: {}", err),
            ExportError::Verify(ref err) => write!(f, "{:?}", err),
            ExportError::Format(ref err) => write!(f, "Format error: {:?}", err),
        }
    }
}

impl error::Error for ExportError {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            ExportError::Io(ref err) => Some(err),
            ExportError::Verify(_) => None,
            ExportError::Format(ref err) => Some(err),
        }
    }
}

impl Database {
    /// Export an mmp file for a given statement.
    pub fn export_mmp<W: Write>(
        &self,
        stmt: StatementRef<'_>,
        out: &mut W,
    ) -> Result<(), ExportError> {
        let thm_label = stmt.label();
        writeln!(
            out,
            "$( <MM> <PROOF_ASST> THEOREM={}  LOC_AFTER=?\n",
            as_str(thm_label)
        )?;
        if let Some(comment) = stmt.associated_comment() {
            let mut span = comment.span();
            span.start += 2;
            span.end -= 3;
            let cstr = Regex::new(r"\n +").unwrap().replace_all(
                as_str(span.as_ref(&comment.segment().segment.buffer)),
                "\n  ",
            );
            writeln!(out, "*{}\n", cstr)?;
        }

        let arr = ProofTreeArray::new(self, stmt)?;
        self.export_mmp_proof_tree(thm_label, &arr, out)
    }

    /// Export an mmp file for a given proof tree.
    pub fn export_mmp_proof_tree<W: Write>(
        &self,
        thm_label: &[u8],
        arr: &ProofTreeArray,
        out: &mut W,
    ) -> Result<(), ExportError> {
        let sset = self.parse_result();
        let nset = self.name_result();

        // TODO(Mario): remove hardcoded logical step symbol
        let provable_tc = b"|-";
        let provable_tc = nset.lookup_symbol(provable_tc).map(|_| provable_tc);

        // This array maps the proof tree index to 0 for syntax proofs and a 1-based
        // index for logical steps
        let mut logical_steps: Vec<usize> = vec![];
        let mut ix = 0usize;
        // This is indexed based on the numbering in logical_steps, so
        // if logical_steps[i] = j+1 then arr.trees[i] corresponds to (i, typecode[i], lines[j])
        let mut lines: Vec<(usize, TokenRef<'_>, String)> = vec![];
        for tree in &arr.trees {
            let stmt = sset.statement(tree.address);
            let label = stmt.label();
            let tc = stmt.math_at(0);
            let logical = provable_tc.map_or(true, |tref| *tref == *tc);

            let cur = logical_steps.len();
            logical_steps.push(if logical {
                ix += 1;
                ix
            } else {
                0
            });

            // Because a step only references previous steps in the array,
            // we are clear to start output before finishing the loop
            if logical {
                let mut line = match stmt.statement_type() {
                    // Floating will not happen unless we don't recognize the grammar
                    StatementType::Essential | StatementType::Floating => format!("h{}", ix),
                    _ => {
                        if cur == arr.qed {
                            "qed".to_string()
                        } else {
                            ix.to_string()
                        }
                    }
                };
                let mut delim = ':';
                for &hyp in &tree.children {
                    let hix = logical_steps[hyp];
                    if hix != 0 {
                        line.push(delim);
                        delim = ',';
                        line.push_str(&hix.to_string());
                    }
                }
                if delim == ':' {
                    line.push(delim);
                }
                line.push(':');
                line.push_str(str::from_utf8(label).unwrap());
                line.push(' ');
                lines.push((cur, tc, line));
            }
        }

        let indent = arr.indent();
        let spaces = lines
            .iter()
            .map(|&(cur, _, ref line)| line.len() as i16 - indent[cur] as i16)
            .max()
            .unwrap() as u16;
        for &mut (cur, tc, ref mut line) in &mut lines {
            for _ in 0..(spaces + indent[cur] - line.len() as u16) {
                line.push(' ')
            }
            line.push_str(str::from_utf8(&tc).unwrap());
            line.push_str(&String::from_utf8_lossy(&arr.exprs[cur]));
            writeln!(out, "{}", line)?;
        }
        writeln!(
            out,
            "\n$={}",
            ProofTreePrinter {
                sset,
                nset,
                scope: self.scope_result(),
                thm_label,
                style: ProofStyle::Compressed,
                arr,
                initial_chr: 2,
                indent: 6,
                line_width: 79,
            }
        )?;

        writeln!(out, "\n$)")?;
        Ok(())
    }
}
