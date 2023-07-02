//! Generation of the `axiom_use` file.
use std::sync::Arc;

use itertools::PeekingNext;

use crate::bit_set::Bitset;
use crate::diag::Diagnostic;
use crate::segment::SegmentRef;
use crate::segment_set::SegmentSet;
use crate::statement::{CommandToken, StatementAddress, TokenPtr};
use crate::util::HashMap;
use crate::StatementType;
use crate::{as_str, database::time, Database};

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
        &mut self,
        sref: SegmentRef<'_>,
        args: &[CommandToken],
    ) -> Result<(), Vec<Diagnostic>> {
        use CommandToken::*;
        let buf = &**sref.buffer;
        match args {
            [Keyword(cmd), label, Keyword(avoids), axioms @ ..]
                if cmd.as_ref(buf) == b"usage" && avoids.as_ref(buf) == b"avoids" =>
            {
                let stmt = label.value(buf);
                let usage = self
                    .axiom_use_map
                    .get(stmt)
                    .ok_or_else(|| vec![Diagnostic::UnknownLabel(label.full_span())])?;
                let mut diags = vec![];
                for cmd in axioms {
                    let axiom = cmd.value(buf);
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
                        let mut usage = Bitset::new();
                        let mut i = 1;
                        loop {
                            let tk = stmt.proof_slice_at(i);
                            i += 1;
                            if tk == b")" {
                                break;
                            }
                            if let Some(usage2) = self.axiom_use_map.get(tk) {
                                usage |= usage2
                            }
                            if i == stmt.proof_len() {
                                break;
                            }
                        }
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
    /// Writes a `axiom_use` file to the given writer.
    pub fn write_axiom_use(&self, out: &mut impl std::io::Write) -> Result<(), std::io::Error> {
        time(&self.options.clone(), "axiom_use", || {
            let mut axiom_use_map = HashMap::default();
            let mut axioms = vec![];
            for sref in self.statements().filter(|stmt| stmt.is_assertion()) {
                let label = sref.label();
                let mut usage = Bitset::new();
                if sref.statement_type() == StatementType::Provable {
                    let mut i = 1;
                    loop {
                        let tk = sref.proof_slice_at(i);
                        i += 1;
                        if tk == b")" {
                            break;
                        }
                        if let Some(usage2) = axiom_use_map.get(tk) {
                            usage |= usage2
                        }
                    }
                    write!(out, "{}:", as_str(label))?;
                    for i in &usage {
                        write!(out, " {}", axioms[i])?;
                    }
                    writeln!(out)?;
                    axiom_use_map.insert(label, usage);
                } else if label.starts_with(b"ax-") {
                    usage.set_bit(axioms.len());
                    axioms.push(as_str(label));
                    axiom_use_map.insert(label, usage);
                }
            }
            Ok(())
        })
    }
}
