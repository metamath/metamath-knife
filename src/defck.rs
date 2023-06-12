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

use std::sync::Arc;

use itertools::PeekingNext;

use crate::diag::Diagnostic;
use crate::formula::TypeCode;
use crate::grammar::{Grammar, StmtParse};
use crate::nameck::Nameset;
use crate::scopeck::{Hyp, ScopeResult};
use crate::segment::SegmentRef;
use crate::segment_set::SegmentSet;
use crate::statement::{CommandToken, GlobalSpan, StatementAddress, StatementIndex};
use crate::util::{HashMap, HashSet};
use crate::{Database, Label, Span, StatementRef, StatementType};

/// Information related to definitions in the database.
///
#[derive(Debug, Default)]
pub struct DefResult {
    equalities_by_tc: HashMap<TypeCode, (Label, GlobalSpan)>,
    primitives: Vec<Label>,
    justifications: HashMap<Label, Label>,
    definitions: HashSet<Label>,
    def_map: HashMap<Label, Label>,
    diagnostics: Vec<(StatementAddress, Diagnostic)>,
}

impl DefResult {
    /// Returns the definition axiom for the given syntax axiom.
    #[must_use]
    pub fn definition_for(&self, syntax_axiom: Label) -> Option<Label> {
        self.def_map.get(&syntax_axiom).copied()
    }

    /// Returns the list of errors that were generated during the definition check pass.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        self.diagnostics.clone()
    }
}

struct DefinitionPass<'a> {
    db: &'a Database,
    nset: &'a Nameset,
    scope: &'a ScopeResult,
    stmts: &'a StmtParse,
    grammar: &'a Grammar,
    pending_primitive: Vec<Label>,
    pending_syntax: Vec<Label>,
    pending_defn: Vec<StatementAddress>,
    /// The value is `true` if it is an equality in `equalities_by_tc`, and `false`
    /// if it is not a registered equality but we have already reported this error
    /// and are suppressing further errors about it.
    equalities: HashMap<Label, bool>,
    result: &'a mut DefResult,
}

impl DefinitionPass<'_> {
    // Parses the 'equality', 'primitive', and 'justification' commmands in the database,
    // and store the result in the database for future fast access.
    fn parse_equality_command(
        &mut self,
        sref: SegmentRef<'_>,
        index: StatementIndex,
        span: Span,
        args: &[CommandToken],
    ) -> Result<(), Diagnostic> {
        use CommandToken::*;
        let buf = &**sref.buffer;
        match args {
            [Keyword(cmd), label, Keyword(from), _refl, _symm, _trans]
                if cmd.as_ref(buf) == b"equality" && from.as_ref(buf) == b"from" =>
            {
                let tok = label.value(buf);
                let equality = self
                    .nset
                    .lookup_label(tok)
                    .ok_or_else(|| Diagnostic::UnknownLabel(label.span()))?;
                match *self
                    .scope
                    .get(tok)
                    .ok_or_else(|| Diagnostic::UnknownLabel(label.span()))?
                    .hypotheses
                {
                    [Hyp::Floating(_, _, tc), Hyp::Floating(_, _, tc2)] if tc == tc2 => {
                        if let Some((_, prev_span)) = self
                            .result
                            .equalities_by_tc
                            .insert(tc, (equality.atom, (sref.id, span)))
                        {
                            return Err(Diagnostic::DefCkDuplicateEquality(
                                self.nset.atom_name(tc).into(),
                                prev_span,
                                span,
                            ));
                        }
                        self.equalities.insert(equality.atom, true);
                    }
                    _ => {
                        return Err(Diagnostic::DefCkMalformedEquality(
                            equality.address,
                            label.span(),
                        ))
                    }
                };

                // TODO verify that the reflexivity, symmetry, and transitivity laws are well-formed
            }
            [Keyword(cmd), rest @ ..] if cmd.as_ref(buf) == b"primitive" => {
                self.flush_pending_definitions();
                for label in rest {
                    let primitive = self.nset.lookup_label(label.value(buf)).unwrap().atom;
                    // Remove the definition from the pending list
                    if let Some(pending_index) =
                        self.pending_primitive.iter().position(|&x| x == primitive)
                    {
                        self.pending_primitive.swap_remove(pending_index);
                        self.result.primitives.push(primitive)
                    } else {
                        self.result.diagnostics.push((
                            StatementAddress::new(sref.id, index),
                            Diagnostic::DefCkMisplacedPrimitive(label.span()),
                        ));
                    }
                }
            }
            [Keyword(cmd), justif_label, Keyword(for_), label]
                if cmd.as_ref(buf) == b"justification" && for_.as_ref(buf) == b"for" =>
            {
                let theorem = self
                    .nset
                    .lookup_label(justif_label.value(buf))
                    .unwrap()
                    .atom;
                let definition = self.nset.lookup_label(label.value(buf)).unwrap().atom;
                self.result.justifications.insert(definition, theorem);
            }
            _ => {}
        }
        Ok(())
    }

    fn verify_definition_statement(&mut self, addr: StatementAddress) -> Result<(), Diagnostic> {
        let stmt = self.db.statement_by_address(addr);
        let definition = self
            .nset
            .lookup_label(stmt.label())
            .ok_or_else(|| Diagnostic::UnknownLabel(stmt.label_span()))?
            .atom;
        if self.result.justifications.contains_key(&definition) {
            // Skip definitional check for definitions having a justification.
            //
            // We normally don't know which syntax axiom this definition is for,
            // but we can make a guess if there is only one pending definition.
            // In set.mm, only `df-bi` is in this case.
            if self.pending_syntax.len() == 1 {
                let syntax_axiom = self.pending_syntax.remove(0);

                // TODO check that the justification matches the definition

                // Store the validated definition
                self.result.definitions.insert(definition);
                self.result.def_map.insert(syntax_axiom, definition);
                Ok(())
            } else {
                Err(Diagnostic::DefCkJustificationWithoutDef(
                    stmt.label().into(),
                    self.pending_syntax.len(),
                ))
            }
        } else {
            // Check that the top level of the definition is an equality
            let fmla = self
                .stmts
                .get_formula(&stmt)
                .ok_or_else(|| Diagnostic::UnknownLabel(stmt.label_span()))?;
            let root = fmla.root(self.db);
            let equality = root.label();
            match self.equalities.get(&equality) {
                None => {
                    self.equalities.insert(equality, false);
                    Err(Diagnostic::DefCkNotAnEquality(
                        self.nset.atom_name(equality).into(),
                        self.result
                            .equalities_by_tc
                            .iter()
                            .map(|(&label, _)| self.nset.atom_name(label).into())
                            .collect(),
                    ))
                }
                Some(false) => Ok(()), // already reported the error
                Some(true) => {
                    let Some(lhs) = root.nth_child(0) else {
                        return Err(Diagnostic::DefCkMalformedDefinition)
                    };

                    let syntax_axiom = lhs.label();
                    // push the definition to the validated list early, so that later definitions
                    // aren't as messed up if this check fails
                    self.result.definitions.insert(definition);
                    if let Some(prev) = self.result.def_map.insert(syntax_axiom, definition) {
                        return Err(Diagnostic::DefCkDuplicateDefinition(
                            self.nset.atom_name(syntax_axiom).into(),
                            self.nset.lookup_label_by_atom(prev).address,
                        ));
                    }

                    // Remove the definition from the pending list
                    if let Some(pending_index) =
                        self.pending_syntax.iter().position(|&x| x == syntax_axiom)
                    {
                        self.pending_syntax.swap_remove(pending_index);
                    } else {
                        return Err(Diagnostic::DefCkMalformedDefinition);
                    }

                    // TODO definition check

                    Ok(())
                }
            }
        }
    }

    /// Called when something breaks a "definition block", forcing us to check the statements
    /// and purge them from the pending queue. We use this delayed checking mechanism
    /// to handle set.mm patterns like defining many syntax axioms followed by many definitions,
    /// or $j commands which come after the definitions they apply to.
    fn flush_pending_definitions(&mut self) {
        if self.pending_syntax.is_empty() {
            return;
        }

        for addr in std::mem::take(&mut self.pending_defn) {
            if let Err(diag) = self.verify_definition_statement(addr) {
                self.result.diagnostics.push((addr, diag));
            }
        }

        self.pending_primitive.append(&mut self.pending_syntax);
    }

    /// Verify that definitions meet set.mm/iset.mm conventions
    pub(crate) fn verify_definitions(&mut self, sset: &SegmentSet) {
        for sref in sset.segments(..) {
            let mut j_commands = sref.j_commands.iter();
            for stmt in sref.range(..) {
                match stmt.statement_type() {
                    StatementType::AdditionalInfoComment => {
                        while let Some(&(index, (span, ref args))) =
                            j_commands.peeking_next(|i| i.0 == stmt.index)
                        {
                            if let Err(diag) = self.parse_equality_command(sref, index, span, args)
                            {
                                self.result.diagnostics.push((stmt.address(), diag));
                            }
                        }
                    }
                    StatementType::Axiom => {
                        if self.nset.get_atom(stmt.math_at(0).slice)
                            != self.grammar.provable_typecode()
                        {
                            // Non-provable typecodes are syntax axioms.
                            if !self.pending_defn.is_empty() {
                                self.flush_pending_definitions()
                            }
                            // TODO Check that the axiom label does _not_ start with `df-`.
                            let syntax_axiom = self.nset.lookup_label(stmt.label()).unwrap().atom;
                            self.pending_syntax.push(syntax_axiom);
                        } else if self.pending_syntax.is_empty() {
                            // No definition to check, this is a regular axiom
                            // TODO Check that the axiom label starts with `ax-`.
                        } else {
                            // Definition, push it to the pending list for later processing
                            self.pending_defn.push(stmt.address());
                        }
                    }
                    StatementType::Provable => self.flush_pending_definitions(),
                    _ => {}
                }
            }
        }

        self.flush_pending_definitions();
        for missing_definition in self.pending_primitive.drain(..) {
            self.result.diagnostics.push((
                self.nset.lookup_label_by_atom(missing_definition).address,
                Diagnostic::DefCkMissingDefinition,
            ));
        }
    }
}

impl Database {
    /// Verify that definitions meet set.mm/iset.mm conventions
    pub(crate) fn verify_definitions(&self, sset: &Arc<SegmentSet>, definitions: &mut DefResult) {
        DefinitionPass {
            db: self,
            nset: self.name_result(),
            scope: self.scope_result(),
            stmts: self.stmt_parse_result(),
            grammar: self.grammar_result(),
            pending_primitive: vec![],
            pending_syntax: vec![],
            pending_defn: vec![],
            equalities: HashMap::default(),
            result: definitions,
        }
        .verify_definitions(sset);
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
