//! Export support for mmj2 proof files.

use crate::as_str;
use crate::diag::Diagnostic;
use crate::proof::ProofStyle;
use crate::proof::ProofTreeArray;
use crate::proof::ProofTreePrinter;
use crate::Database;
use crate::StatementRef;
use crate::StatementType;
use regex::Regex;
use std::error;
use std::fmt;
use std::io;
use std::io::Write;
use std::str;
use std::sync::OnceLock;

/// The error type for [`Database::export_mmp`].
#[derive(Debug)]
#[allow(variant_size_differences)]
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
        match self {
            ExportError::Io(err) => write!(f, "IO error: {err}"),
            ExportError::Verify(err) => write!(f, "{err:?}"),
            ExportError::Format(err) => write!(f, "Format error: {err:?}"),
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
            static LEADING_WHITESPACE: OnceLock<Regex> = OnceLock::new();
            let leading_whitespace =
                LEADING_WHITESPACE.get_or_init(|| Regex::new(r"\n +").unwrap());
            let mut span = comment.span();
            span.start += 2;
            span.end -= 3;
            let cstr = leading_whitespace.replace_all(
                as_str(span.as_ref(&comment.segment().segment.buffer)),
                "\n  ",
            );
            writeln!(out, "*{cstr}\n")?;
        }

        match ProofTreeArray::from_stmt(self, stmt, true) {
            Ok(arr) => self.export_mmp_proof_tree(thm_label, &arr, out),
            Err(Diagnostic::ProofIncomplete) => self.export_incomplete_proof(stmt, out),
            Err(diag) => Err(diag.into()),
        }
    }
}

impl ProofTreeArray {
    /// Applies the provided function to each of the logical steps.
    /// It takes 4 parameters:
    /// * `cur` - the index of the step among all proof steps (incuding non-logical ones).
    ///   This can be used as an index in `ProofTreeArray`'s expressions `exprs` and `indents`.
    /// * `ix` - the index of the step, when only logical steps are counted,
    /// * `stmt` - the statement applied at this step,
    /// * `hyps` - the indices of the hypotheses for this step (only counting logical hypotheses)
    pub fn with_logical_steps<T>(
        &self,
        db: &Database,
        f: impl Fn(usize, usize, StatementRef<'_>, Vec<usize>) -> T,
    ) -> Vec<T> {
        let sset = db.parse_result();
        let nset = db.name_result();

        // TODO(Mario): remove hardcoded logical step symbol
        let provable_tc = b"|-";
        let provable_tc = nset.lookup_symbol(provable_tc).map(|_| provable_tc);

        // This array maps the proof tree index to 0 for syntax proofs and a 1-based
        // index for logical steps
        let mut logical_steps: Vec<usize> = vec![];
        let mut ix = 0usize;
        // This is indexed based on the numbering in logical_steps, so
        // if logical_steps[i] = j+1 then arr.trees[i] corresponds to (i, typecode[i], lines[j])
        let mut out = vec![];
        for (cur, tree) in self.trees.iter().enumerate() {
            let stmt = sset.statement(tree.address);
            let tc = stmt.math_at(0);
            let logical = provable_tc.is_none_or(|tref| *tref == *tc);
            logical_steps.push(if logical {
                ix += 1;
                let hyps = tree
                    .children
                    .iter()
                    .filter_map(|ix| {
                        let hix = logical_steps[*ix];
                        if hix != 0 {
                            Some(hix)
                        } else {
                            None
                        }
                    })
                    .collect();
                out.push(f(cur, ix, stmt, hyps));
                ix
            } else {
                0
            });
        }
        out
    }

    /// Applies the provided function to each of the steps.
    /// It takes 3 parameters:
    /// * `cur` - the current index of the step,
    /// * `stmt` - the statement applied at this step,
    /// * `hyps` - the indices of the hypotheses for this step,
    pub fn with_steps<T>(
        &self,
        db: &Database,
        f: impl Fn(usize, StatementRef<'_>, &'_ Vec<usize>) -> T,
    ) -> Vec<T> {
        let sset = db.parse_result();
        self.trees
            .iter()
            .enumerate()
            .map(|(cur, tree)| f(cur, sset.statement(tree.address), &tree.children))
            .collect()
    }
}

impl Database {
    /// Export an mmp file for a given proof tree.
    /// ## Panics
    /// The `ProofTreeArray` must have `enable_exprs = true`.
    pub fn export_mmp_proof_tree<W: Write>(
        &self,
        thm_label: &[u8],
        arr: &ProofTreeArray,
        out: &mut W,
    ) -> Result<(), ExportError> {
        // TODO(Mario): remove hardcoded logical step symbol
        let tc = b"|-";
        let mut lines = arr.with_logical_steps(self, |cur, ix, stmt, hyps| {
            let mut line = match stmt.statement_type() {
                // Floating will not happen unless we don't recognize the grammar
                StatementType::Essential | StatementType::Floating => format!("h{ix}"),
                _ => {
                    if cur == arr.qed {
                        "qed".to_string()
                    } else {
                        ix.to_string()
                    }
                }
            };
            let mut delim = ':';
            for &hix in &hyps {
                line.push(delim);
                delim = ',';
                line.push_str(&hix.to_string());
            }
            if delim == ':' {
                line.push(delim);
            }
            line.push(':');
            line.push_str(str::from_utf8(stmt.label()).unwrap());
            line.push(' ');
            (cur, line)
        });

        let indent = arr.indent();
        let spaces = lines
            .iter()
            .map(|&(cur, ref line)| line.len() as i16 - indent[cur] as i16)
            .max()
            .unwrap() as u16;
        let exprs = arr
            .exprs()
            .expect("exporting MMP requires expressions enabled in the ProofTreeArray");
        for &mut (cur, ref mut line) in &mut lines {
            for _ in 0..(spaces + indent[cur] - line.len() as u16) {
                line.push(' ')
            }
            line.push_str(str::from_utf8(tc).unwrap());
            line.push_str(&String::from_utf8_lossy(&exprs[cur]));
            writeln!(out, "{line}")?;
        }
        let mut printer = ProofTreePrinter::new(self, thm_label, ProofStyle::Compressed, arr);
        printer.set_initial_chr(2);
        writeln!(out, "\n$={printer}")?;
        writeln!(out, "\n$)")?;
        Ok(())
    }

    fn export_incomplete_proof<W: Write>(
        &self,
        stmt: StatementRef<'_>,
        out: &mut W,
    ) -> Result<(), ExportError> {
        let mut hyp = 1;

        // Hypotheses
        for (label, _) in self
            .scope_result()
            .get(stmt.label())
            .expect("Statement without scope")
            .as_ref(self)
            .essentials()
        {
            let hyp_stmt = self.statement_by_label(label).unwrap();
            write!(out, "h{}::{} ", hyp, as_str(hyp_stmt.label()))?;
            for token in hyp_stmt.math_iter() {
                write!(out, "{} ", as_str(&token))?;
            }
            writeln!(out)?;
            hyp += 1;
        }

        // Statement assertion
        write!(out, "!qed::")?;
        for token in stmt.math_iter() {
            write!(out, " {}", as_str(&token))?;
        }
        writeln!(out, "\n\n$)")?;
        Ok(())
    }
}
