//! Generation of the `axiom_use` file.
use std::sync::Arc;

use itertools::PeekingNext;

use crate::bit_set::Bitset;
use crate::diag::Diagnostic;
use crate::segment::SegmentRef;
use crate::segment_set::SegmentSet;
use crate::statement::{CommandToken, StatementAddress, TokenPtr};
use crate::util::HashMap;
use crate::{as_str, database::time, Database};
use crate::{StatementRef, StatementType};

/// Diagnostics issued when checking axiom usage in the Database.
///
#[derive(Debug, Default)]
pub struct UsageResult(Vec<(StatementAddress, Diagnostic)>);

impl UsageResult {
    /// Returns the list of errors that were generated during the usage check pass.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        self.0.clone()
    }
}

struct UsagePass<'a> {
    axiom_use_map: HashMap<TokenPtr<'a>, Bitset>,
    axioms: Vec<TokenPtr<'a>>,
    result: &'a mut UsageResult,
}

impl<'a> UsagePass<'a> {
    // Parses the 'usage' commmands in the database,
    fn parse_command(
        &self,
        sref: SegmentRef<'_>,
        args: &[CommandToken],
    ) -> Result<(), Vec<Diagnostic>> {
        use CommandToken::*;
        let buf = &**sref.buffer;
        match args {
            [Keyword(cmd), label, Keyword(avoids), axioms @ ..]
                if cmd.as_ref(buf) == b"usage" && avoids.as_ref(buf) == b"avoids" =>
            {
                let stmt = &*label.value(buf);
                let usage = self
                    .axiom_use_map
                    .get(stmt)
                    .ok_or_else(|| vec![Diagnostic::UnknownLabel(label.full_span())])?;
                let mut diags = vec![];
                for cmd in axioms {
                    let axiom = &*cmd.value(buf);
                    if let Some(index) = self.axioms.iter().position(|&x| x == axiom) {
                        if usage.has_bit(index) {
                            // TODO possibly research the usage "path" leading to this error.
                            diags.push(Diagnostic::UsageViolation(
                                cmd.full_span(),
                                stmt.into(),
                                axiom.into(),
                            ));
                        }
                    }
                }
                Err(diags)
            }
            _ => Ok(()),
        }
    }

    /// Verify that all usage declarations are correct.
    fn verify_usage(&'a mut self, sset: &'a SegmentSet) {
        for sref in sset.segments(..) {
            let mut j_commands: std::slice::Iter<'_, (i32, (crate::Span, Vec<CommandToken>))> =
                sref.j_commands.iter();
            for stmt in sref.range(..) {
                match stmt.statement_type() {
                    StatementType::AdditionalInfoComment => {
                        while let Some(&(_, (_, ref args))) =
                            j_commands.peeking_next(|i| i.0 == stmt.index)
                        {
                            if let Err(diags) = self.parse_command(sref, args) {
                                for diag in diags {
                                    self.result.0.push((stmt.address(), diag));
                                }
                            }
                        }
                    }
                    StatementType::Provable => {
                        let label = stmt.label();
                        let usage = get_proof_usage(&stmt, &self.axiom_use_map);
                        self.axiom_use_map.insert(label, usage);
                    }
                    StatementType::Axiom => {
                        let label = stmt.label();
                        if label.starts_with(b"ax-") {
                            let mut usage = Bitset::new();
                            usage.set_bit(self.axioms.len());
                            self.axioms.push(label);
                            self.axiom_use_map.insert(label, usage);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Verify the axiom usage
pub(crate) fn verify_usage(sset: &Arc<SegmentSet>, usage: &mut UsageResult) {
    UsagePass {
        axiom_use_map: HashMap::default(),
        axioms: vec![],
        result: usage,
    }
    .verify_usage(sset);
}

impl Database {
    /// Writes a `stmt_use` file to the given writer.
    pub fn write_stmt_use(
        &self,
        label_test: impl Fn(&[u8]) -> bool,
        out: &mut impl std::io::Write,
    ) -> Result<(), std::io::Error> {
        time(&self.options.clone(), "stmt_use", || {
            let mut stmt_use_map = HashMap::default();
            let mut stmt_list = vec![];
            for sref in self.statements().filter(|stmt| stmt.is_assertion()) {
                let label = sref.label();
                if label_test(label) {
                    let mut usage = Bitset::new();
                    usage.set_bit(stmt_list.len());
                    stmt_list.push(as_str(label));
                    stmt_use_map.insert(label, usage);
                } else if sref.statement_type() == StatementType::Provable {
                    let usage = get_proof_usage(&sref, &stmt_use_map);
                    write!(out, "{}:", as_str(label))?;
                    for i in &usage {
                        write!(out, " {}", stmt_list[i])?;
                    }
                    writeln!(out)?;
                    stmt_use_map.insert(label, usage);
                }
            }
            Ok(())
        })
    }
}

#[inline]
fn get_proof_usage(sref: &StatementRef<'_>, stmt_use_map: &HashMap<&[u8], Bitset>) -> Bitset {
    let mut usage = Bitset::new();
    if sref.proof_slice_at(0) == b"(" {
        let mut i = 1;
        loop {
            let tk = sref.proof_slice_at(i);
            i += 1;
            if tk == b")" {
                break;
            }
            if let Some(usage2) = stmt_use_map.get(tk) {
                usage |= usage2
            }
            if i == sref.proof_len() {
                break;
            }
        }
    } else {
        #[cold]
        fn process_non_compressed(
            sref: &StatementRef<'_>,
            stmt_use_map: &HashMap<&[u8], Bitset>,
            usage: &mut Bitset,
        ) {
            let mut i = 0;
            while i < sref.proof_len() {
                let tk = sref.proof_slice_at(i);
                if let Some(usage2) = stmt_use_map.get(tk) {
                    *usage |= usage2
                } else if let Some(i) = tk
                    .iter()
                    .position(|&x| x == b'=')
                    .or_else(|| tk.iter().position(|&x| x == b':'))
                {
                    if let Some(usage2) = stmt_use_map.get(&tk[i + 1..]) {
                        *usage |= usage2
                    }
                }
                i += 1;
            }
        }
        process_non_compressed(sref, stmt_use_map, &mut usage)
    }
    usage
}
