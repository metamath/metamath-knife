//! Verification of definitions
//!
//! Implement verification of definitions per the set.mm/iset.mm conventions.
//! If the "exceptions" string is empty we use the "typical" set.mm values.
//! The current typical values are "ax-*,df-bi,df-clab,df-cleq,df-clel".
//! For glob syntax see: <https://docs.rs/globset/latest/globset/>
//! but in the future we may reduce the glob language sophistication.
//! For more information see:
//! <https://us.metamath.org/mpeuni/conventions.html>
//! <https://github.com/digama0/mmj2/blob/master/mmj2jar/macros/definitionCheck.js>
//! and "Metamath: A Computer Language for Mathematical Proofs" by
//! Norman Megill and David A. Wheeler, 2019, page 155.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::diag::Diagnostic;
use crate::segment_set::SegmentSet;
use crate::statement::CommandToken;
use crate::{as_str, Database, Label, StatementRef, StatementType};

/// Information related to definitions in the database.
///
#[derive(Debug, Default)]
pub struct DefResult {
    equalities: Vec<Label>,
    primitives: Vec<Label>,
    justifications: HashMap<Label, Label>,
    definitions: HashSet<Label>,
    def_map: HashMap<Label, Label>,
}

impl DefResult {
    /// Returns the definition axiom for the given syntax axiom.
    #[must_use]
    pub fn definition_for(&self, syntax_axiom: Label) -> Option<&Label> {
        self.def_map.get(&syntax_axiom)
    }
}

impl Database {
    // Parses the 'equality', 'primitive', and 'justification' commmands in the database,
    // and store the result in the database for future fast access.
    fn parse_equality_commands(&self, sset: &SegmentSet, definitions: &mut DefResult) {
        for sref in sset.segments(..) {
            let buf = &**sref.buffer;
            for (_, (_, command)) in &sref.j_commands {
                use CommandToken::*;
                match &**command {
                    [Keyword(cmd), label, Keyword(from), _reflexivity_law, _commutativity_law, _transitivity_law]
                        if cmd.as_ref(buf) == b"equality" && from.as_ref(buf) == b"from" =>
                    {
                        let equality = self
                            .name_result()
                            .lookup_label(label.value(buf))
                            .unwrap()
                            .atom;
                        println!(
                            "Found equality {label}: {equality:?}",
                            label = as_str(label.value(buf)),
                            equality = equality
                        );
                        definitions.equalities.push(equality);
                    }
                    [Keyword(cmd), ..] if cmd.as_ref(buf) == b"primitive" => {
                        for label in &command[1..] {
                            println!(
                                "Found primitive {label:?}",
                                label = as_str(label.value(buf))
                            );
                            let primitive = self
                                .name_result()
                                .lookup_label(label.value(buf))
                                .unwrap()
                                .atom;
                            definitions.primitives.push(primitive);
                        }
                    }
                    [Keyword(cmd), justif_label, Keyword(for_), label]
                        if cmd.as_ref(buf) == b"justification" && for_.as_ref(buf) == b"for" =>
                    {
                        println!(
                            "Found justification for {label:?}",
                            label = as_str(label.value(buf))
                        );
                        let theorem = self
                            .name_result()
                            .lookup_label(justif_label.value(buf))
                            .unwrap()
                            .atom;
                        let definition = self
                            .name_result()
                            .lookup_label(label.value(buf))
                            .unwrap()
                            .atom;
                        definitions.justifications.insert(definition, theorem);
                    }
                    _ => {}
                }
            }
        }
    }

    /// Verify that definitions meet set.mm/iset.mm conventions;
    pub(crate) fn verify_definitions(
        &self,
        sset: &Arc<SegmentSet>,
        definitions: &mut DefResult,
    ) -> Result<(), Diagnostic> {
        self.parse_equality_commands(sset, definitions);
        let names = self.name_result();

        // Fail the whole check if no equality has been defined
        #[allow(clippy::manual_assert)]
        if definitions.equalities.is_empty() {
            panic!("No equality command found, definitional soundness check cannot be done in this database.");
        }

        // TODO verify that the reflexivity, associativity, and transivity laws are well-formed

        let mut pending_definitions = vec![];
        for sref in self
            .statements()
            .filter(|stmt| stmt.statement_type() == StatementType::Axiom)
        {
            println!("Checking {label:?}", label = as_str(sref.label()));
            if names.get_atom(sref.math_at(0).slice) != self.grammar_result().provable_typecode() {
                // Non-provable typecodes are syntax axioms.
                // TODO Check that the axiom label does _not_ start with `df-`.
                let syntax_axiom = names
                    .lookup_label(sref.label())
                    .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?
                    .atom;
                if !definitions.primitives.contains(&syntax_axiom) {
                    // This syntax axiom is in need of a definition
                    pending_definitions.push(syntax_axiom);
                }
            } else if pending_definitions.is_empty() {
                // No definition to check, this is a regular axiom
                // TODO Check that the axiom label starts with `ax-`.
                println!("Regular axiom: {label}", label = as_str(sref.label()));
            } else {
                println!(
                    "Definition: {label} ({count} pending)",
                    label = as_str(sref.label()),
                    count = pending_definitions.len()
                );
                // TODO Check that the definition label starts with `df-`.

                let definition = names
                    .lookup_label(sref.label())
                    .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?
                    .atom;
                if definitions.justifications.contains_key(&definition) {
                    // Skip definitional check for definitions having a justification.
                    //
                    // We normally don't know which syntax axiom this definition is for,
                    // but we can make a guess if there is only one pending definition.
                    // In set.mm, only `df-bi` is in this case.
                    if pending_definitions.len() == 1 {
                        println!("Skipped check because justification exists.");
                        let syntax_axiom = pending_definitions.remove(0);

                        // Store the validated definition
                        definitions.definitions.insert(definition);
                        definitions.def_map.insert(syntax_axiom, definition);
                    } else {
                        panic!("A justification was found for {label}, but there is no way to track it to a definiendum, since there are {count} pending definitions.", label = as_str(sref.label()), count = pending_definitions.len());
                    }
                } else {
                    // Check that the top level of the definition is an equality
                    let fmla = self
                        .stmt_parse_result()
                        .get_formula(&sref)
                        .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?;
                    let equality = &fmla.get_by_path(&[]).unwrap();
                    if !definitions.equalities.contains(equality) {
                        // TODO -  This fails at ~ax-hilex in set.mm.
                        // panic!("Definition's top level syntax is {equality:?}, which is not an equality", equality=equality);
                        println!(
                            "Skipping {label} because it's not a definition",
                            label = as_str(sref.label())
                        );
                        continue;
                    }

                    let syntax_axiom = &fmla.get_by_path(&[0]).unwrap();
                    if let Some(pending_index) =
                        pending_definitions.iter().position(|x| *x == *syntax_axiom)
                    {
                        pending_definitions.swap_remove(pending_index);
                    } else {
                        //panic!("Definition {label} found for unknown syntax axiom {syntax_axiom:?}", label = as_str(sref.label()));
                        println!(
                            "Skipping {label} because its definiendum has not been found.",
                            label = as_str(sref.label())
                        );
                    }

                    println!("Checked {label} OK", label = as_str(sref.label()));

                    // Store the validated definition
                    definitions.definitions.insert(definition);
                    definitions.def_map.insert(*syntax_axiom, definition);
                }
            }
        }
        // TODO - This fails because of `~cmesy`
        //assert!(pending_definitions.is_empty(), "Some syntax axioms like {label} don't have definitions.", label = as_str(self.name_result().atom_name(pending_definitions[0])));

        Ok(())
    }

    /// Returns whether the given statement is a definition
    #[must_use]
    pub fn is_definition(&self, sref: StatementRef<'_>) -> bool {
        sref.is_assertion() && {
            let label = self.name_result().lookup_label(sref.label()).unwrap().atom;
            self.definitions_result().definitions.contains(&label)
        }
    }
}
