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
use crate::nameck::Nameset;
use crate::segment_set::SegmentSet;
use crate::statement::{CommandToken, StatementAddress};
use crate::{Database, Label, StatementRef, StatementType};

/// Information related to definitions in the database.
///
#[derive(Debug, Default)]
pub struct DefResult {
    equalities: Vec<Label>,
    primitives: Vec<Label>,
    justifications: HashMap<Label, Label>,
    definitions: HashSet<Label>,
    def_map: HashMap<Label, Label>,
    diagnostics: HashMap<StatementAddress, Diagnostic>,
}

impl DefResult {
    /// Returns the definition axiom for the given syntax axiom.
    #[must_use]
    pub fn definition_for(&self, syntax_axiom: Label) -> Option<&Label> {
        self.def_map.get(&syntax_axiom)
    }

    /// Returns the list of errors that were generated during the definition check pass.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sa, diag) in &self.diagnostics {
            out.push((*sa, diag.clone()));
        }
        out
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
                        definitions.equalities.push(equality);
                    }
                    [Keyword(cmd), ..] if cmd.as_ref(buf) == b"primitive" => {
                        for label in &command[1..] {
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

    fn verify_definition_statement(
        &self,
        sref: StatementRef<'_>,
        names: &Arc<Nameset>,
        definitions: &mut DefResult,
        pending_definitions: &mut Vec<Label>,
    ) -> Result<(), Diagnostic> {
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
            Ok(())
        } else if pending_definitions.is_empty() {
            // No definition to check, this is a regular axiom
            // TODO Check that the axiom label starts with `ax-`.
            Ok(())
        } else {
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
                    let syntax_axiom = pending_definitions.remove(0);

                    // Store the validated definition
                    definitions.definitions.insert(definition);
                    definitions.def_map.insert(syntax_axiom, definition);
                    Ok(())
                } else {
                    Err(Diagnostic::DefCkJustificationWithoutDef(
                        sref.label().into(),
                        pending_definitions.len(),
                    ))
                }
            } else {
                // Check that the top level of the definition is an equality
                let fmla = self
                    .stmt_parse_result()
                    .get_formula(&sref)
                    .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?;
                let equality = &fmla.get_by_path(&[]).unwrap();
                if !definitions.equalities.contains(equality) {
                    Err(Diagnostic::DefCkNotAnEquality(
                        names.atom_name(*equality).into(),
                        definitions
                            .equalities
                            .iter()
                            .map(|label| names.atom_name(*label).into())
                            .collect(),
                    ))
                } else {
                    // Remove the definition from the pending list
                    let syntax_axiom = &fmla.get_by_path(&[0]).unwrap();
                    let result = if let Some(pending_index) =
                        pending_definitions.iter().position(|x| *x == *syntax_axiom)
                    {
                        pending_definitions.swap_remove(pending_index);
                        Ok(())
                    } else if let Some(previous_saddr) = definitions
                        .definition_for(*syntax_axiom)
                        .map(|a| names.lookup_label_by_atom(*a).address)
                    {
                        Err(Diagnostic::DefCkDuplicateDefinition(
                            names.atom_name(*syntax_axiom).into(),
                            previous_saddr,
                        ))
                    } else {
                        Err(Diagnostic::DefCkMalformedDefinition)
                    };

                    // Store the validated definition
                    definitions.definitions.insert(definition);
                    definitions.def_map.insert(*syntax_axiom, definition);
                    result
                }
            }
        }
    }

    /// Verify that definitions meet set.mm/iset.mm conventions;
    pub(crate) fn verify_definitions(&self, sset: &Arc<SegmentSet>, definitions: &mut DefResult) {
        self.parse_equality_commands(sset, definitions);
        let names = self.name_result();

        // Fail the whole check if no equality has been defined
        #[allow(clippy::manual_assert)]
        if definitions.equalities.is_empty() {
            definitions
                .diagnostics
                .insert(StatementAddress::default(), Diagnostic::DefCkNoEquality);
        }

        // TODO verify that the reflexivity, associativity, and transivity laws are well-formed

        let mut pending_definitions = vec![];
        for sref in self
            .statements()
            .filter(|stmt| stmt.statement_type() == StatementType::Axiom)
        {
            if let Err(diag) =
                self.verify_definition_statement(sref, names, definitions, &mut pending_definitions)
            {
                definitions.diagnostics.insert(sref.address(), diag);
            }
        }

        for missing_definition in pending_definitions {
            definitions.diagnostics.insert(
                names.lookup_label_by_atom(missing_definition).address,
                Diagnostic::DefCkMissingDefinition(names.atom_name(missing_definition).into()),
            );
        }
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
