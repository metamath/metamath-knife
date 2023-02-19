//! Regeneration of the `discouraged` file.
//!
//! This module attempts to reproduce the same function of metamath-exe, see [function `showDiscouraged`](https://github.com/metamath/metamath-exe/blob/86c5c2c5118bb8a4274925a4eb550fc58c3ca705/src/mmcmds.c#L5408)
use std::io::Write;
use std::{collections::HashMap, fs::File};

use crate::{
    as_str, comment_parser::Discouragements, database::time, diag::Diagnostic,
    proof::ProofTreeArray, Database,
};
use crate::{StatementRef, StatementType};
use std::collections::{BTreeMap, BTreeSet};

impl Database {
    /// Regenerates the `discouraged` file in the current directory
    pub fn regen_discouraged(&self) -> Result<(), Diagnostic> {
        time(&self.options.clone(), "discouraged", || {
            self.output_discouraged(&mut File::create("discouraged")?)
        })
    }

    /// Regenerates a `discouraged` file into the provided output file
    /// Requires: [`Database::scope_pass`], [`Database::typesetting_pass`]
    pub fn output_discouraged(&self, out: &mut File) -> Result<(), Diagnostic> {
        let mut usage_discouraged_map = HashMap::new();
        let mut usage_discouraged_list = BTreeMap::new();
        let mut modif_discouraged_list = BTreeMap::new();
        for sref in self.statements().filter(|stmt| stmt.is_assertion()) {
            let Discouragements {
                modification_discouraged,
                usage_discouraged,
            } = sref.discouragements();
            let label = as_str(sref.label());
            if usage_discouraged {
                usage_discouraged_list.insert(label, sref.address());
                usage_discouraged_map.insert(sref.address(), BTreeSet::new());
            }
            if sref.statement_type() == StatementType::Provable {
                let steps = match ProofTreeArray::from_stmt(self, sref, false) {
                    Ok(proof) => {
                        for step in proof.trees {
                            if let Some(usage) = usage_discouraged_map.get_mut(&step.address) {
                                usage.insert(label);
                            };
                        }
                        step_count(sref)
                    }
                    _ => 0,
                };
                if modification_discouraged {
                    modif_discouraged_list.insert(label, steps);
                }
            }
        }
        for (label, saddr) in &usage_discouraged_list {
            if let Some(uses) = usage_discouraged_map.get(saddr) {
                for used_by in uses {
                    writeln!(out, "\"{label}\" is used by \"{used_by}\".")?;
                }
            }
        }
        for (label, saddr) in usage_discouraged_list {
            let uses = usage_discouraged_map.get(&saddr).map_or(0, BTreeSet::len);
            writeln!(
                out,
                "New usage of \"{label}\" is discouraged ({uses} uses)."
            )?;
        }
        for (label, steps) in modif_discouraged_list {
            writeln!(
                out,
                "Proof modification of \"{label}\" is discouraged ({steps} steps)."
            )?;
        }
        Ok(())
    }
}

/// Attempts to emulate counting proof steps from metamath-exe
/// This appears to sometimes be off by 3 or 6 steps.
fn step_count(stmt: StatementRef<'_>) -> usize {
    if stmt.proof_len() > 0 && stmt.proof_slice_at(0) == b"(" {
        // This is a compressed proof
        let mut i = 0;
        let mut step_count = 0;
        while i < stmt.proof_len() {
            let chunk = stmt.proof_slice_at(i);
            step_count += chunk.iter().filter(|ch| (b'A'..=b'T').contains(ch)).count();
            i += 1;
        }
        step_count
    } else {
        // This is an uncompressed proof
        stmt.proof_len() as usize
    }
}
