//! Regeneration of the `discouraged` file.
//!
//! This module attempts to reproduce the same function of metamath-exe, see
//! [function `showDiscouraged`](https://github.com/metamath/metamath-exe/blob/86c5c2c5/src/mmcmds.c#L5408)
use crate::StatementType;
use crate::{as_str, comment_parser::Discouragements, database::time, Database};
use std::collections::{BTreeMap, BTreeSet};

impl Database {
    /// Writes a `discouraged` file to the given writer.
    pub fn write_discouraged(&self, out: &mut impl std::io::Write) -> Result<(), std::io::Error> {
        time(&self.options.clone(), "discouraged", || {
            let mut usage_discouraged_map = BTreeMap::new();
            let mut modif_discouraged_map = BTreeMap::new();
            for sref in self.statements().filter(|stmt| stmt.is_assertion()) {
                let Discouragements {
                    modification_discouraged,
                    usage_discouraged,
                } = sref.discouragements();
                let label = sref.label();
                if usage_discouraged {
                    usage_discouraged_map.insert(label, BTreeSet::new());
                }
                if sref.statement_type() == StatementType::Provable {
                    let mut steps;
                    if sref.proof_len() > 0 && sref.proof_slice_at(0) == b"(" {
                        let mut i = 1;
                        while i < sref.proof_len() {
                            let tk = sref.proof_slice_at(i);
                            i += 1;
                            if tk == b")" {
                                break;
                            }
                            if let Some(usage) = usage_discouraged_map.get_mut(tk) {
                                usage.insert(label);
                            }
                        }
                        steps = 0;
                        while i < sref.proof_len() {
                            let chunk = sref.proof_slice_at(i);
                            steps += chunk.iter().filter(|ch| (b'A'..=b'T').contains(ch)).count();
                            i += 1;
                        }
                    } else {
                        let mut i = 0;
                        while i < sref.proof_len() {
                            let tk = sref.proof_slice_at(i);
                            if let Some(usage) = usage_discouraged_map.get_mut(tk) {
                                usage.insert(label);
                            }
                            i += 1;
                        }
                        steps = i as usize;
                    }
                    if modification_discouraged {
                        modif_discouraged_map.insert(label, steps);
                    }
                }
            }
            for (label, uses) in &usage_discouraged_map {
                let label = as_str(label);
                for used_by in uses {
                    writeln!(out, "\"{label}\" is used by \"{}\".", as_str(used_by))?;
                }
            }
            for (label, uses) in usage_discouraged_map {
                let label = as_str(label);
                let uses = uses.len();
                writeln!(
                    out,
                    "New usage of \"{label}\" is discouraged ({uses} uses)."
                )?;
            }
            for (label, steps) in modif_discouraged_map {
                let label = as_str(label);
                writeln!(
                    out,
                    "Proof modification of \"{label}\" is discouraged ({steps} steps)."
                )?;
            }
            Ok(())
        })
    }
}
