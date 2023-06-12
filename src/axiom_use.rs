//! Generation of the `axiom_use` file.
use crate::bit_set::Bitset;
use crate::util::HashMap;
use crate::StatementType;
use crate::{as_str, database::time, Database};

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
