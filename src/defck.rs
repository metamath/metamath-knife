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
use crate::formula::{SubFormulaChildren, SubFormulaRef, TypeCode};
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

fn app(
    label: Label,
    args: impl FnOnce(SubFormulaChildren<'_>) -> bool,
) -> impl FnOnce(SubFormulaRef<'_>) -> bool {
    move |c| c.label() == label && args(c.children())
}
fn cons(
    f: impl FnOnce(SubFormulaRef<'_>) -> bool,
    args: impl FnOnce(SubFormulaChildren<'_>) -> bool,
) -> impl FnOnce(SubFormulaChildren<'_>) -> bool {
    move |mut c| c.next().map_or(false, f) && args(c)
}
fn nil(mut c: SubFormulaChildren<'_>) -> bool {
    c.next().is_none()
}
fn get_var(db: &Database, iter: &mut std::slice::Iter<'_, Hyp>) -> Option<Label> {
    let Hyp::Floating(addr, _, _) = *iter.next()? else { return None };
    let label = db.statement_by_address(addr).label();
    Some(db.name_result().lookup_label(label)?.atom)
}
fn check(
    db: &Database,
    addr: StatementAddress,
    f: impl FnOnce(SubFormulaRef<'_>) -> bool,
) -> Option<()> {
    let stmt = db.statement_by_address(addr);
    let formula = db.stmt_parse_result().get_formula(&stmt)?;
    f(formula.root(db)).then_some(())
}
fn check_hyp(
    db: &Database,
    iter: &mut std::slice::Iter<'_, Hyp>,
    f: impl FnOnce(SubFormulaRef<'_>) -> bool,
) -> Option<()> {
    let Hyp::Essential(addr, _) = *iter.next()? else { return None };
    check(db, addr, f)
}

struct DefinitionPass<'a> {
    db: &'a Database,
    nset: &'a Nameset,
    scope: &'a ScopeResult,
    stmts: &'a StmtParse,
    grammar: &'a Grammar,
    /// These are most likely errors, but will be suppressed if there
    /// turns out to be a `primitive` command later on.
    pending_primitive: Vec<(Label, StatementAddress, Diagnostic)>,
    /// These are syntax axioms which are pending a definition to claim them.
    pending_syntax: Vec<Label>,
    /// These are (definition addr, syntax axiom label) pairs pending processing.
    /// (We don't process them immediately so that $j commands can apply.)
    pending_defn: Vec<(StatementAddress, Label)>,
    /// The value is `true` if it is an equality in `equalities_by_tc`, and `false`
    /// if it is not a registered equality but we have already reported this error
    /// and are suppressing further errors about it.
    equalities: HashMap<Label, bool>,
    result: &'a mut DefResult,
}

impl DefinitionPass<'_> {
    fn check_equality_theorem_matches(
        &mut self,
        buf: &[u8],
        span: Span,
        f: impl FnOnce(StatementAddress, &mut std::slice::Iter<'_, Hyp>) -> Option<()>,
    ) -> Result<(), Diagnostic> {
        let tok = span.as_ref(buf);
        let thm = self
            .nset
            .lookup_label(tok)
            .ok_or_else(|| Diagnostic::UnknownLabel(span))?;
        let frame = self
            .scope
            .get(tok)
            .ok_or_else(|| Diagnostic::UnknownLabel(span))?;
        f(thm.address, &mut frame.hypotheses.iter())
            .ok_or_else(|| Diagnostic::DefCkMalformedEquality(thm.address, span))
    }

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
            [Keyword(cmd), label, Keyword(from), refl, symm, trans]
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

                let eq = equality.atom;
                // TODO: macro?
                self.check_equality_theorem_matches(buf, refl.span(), |addr, iter| {
                    let x = get_var(self.db, iter)?;
                    iter.next().is_none().then_some(())?;
                    let f = app(eq, cons(app(x, nil), cons(app(x, nil), nil)));
                    check(self.db, addr, f)
                })?;
                self.check_equality_theorem_matches(buf, symm.span(), |addr, iter| {
                    let x = get_var(self.db, iter)?;
                    let y = get_var(self.db, iter)?;
                    let f = app(eq, cons(app(x, nil), cons(app(y, nil), nil)));
                    check_hyp(self.db, iter, f)?;
                    iter.next().is_none().then_some(())?;
                    let f = app(eq, cons(app(y, nil), cons(app(x, nil), nil)));
                    check(self.db, addr, f)
                })?;
                self.check_equality_theorem_matches(buf, trans.span(), |addr, iter| {
                    let x = get_var(self.db, iter)?;
                    let y = get_var(self.db, iter)?;
                    let z = get_var(self.db, iter)?;
                    let f = app(eq, cons(app(x, nil), cons(app(y, nil), nil)));
                    check_hyp(self.db, iter, f)?;
                    let f = app(eq, cons(app(y, nil), cons(app(z, nil), nil)));
                    check_hyp(self.db, iter, f)?;
                    iter.next().is_none().then_some(())?;
                    let f = app(eq, cons(app(x, nil), cons(app(z, nil), nil)));
                    check(self.db, addr, f)
                })?;
            }
            [Keyword(cmd), rest @ ..] if cmd.as_ref(buf) == b"primitive" => {
                self.flush_pending_syntax();
                for label in rest {
                    let primitive = self.nset.lookup_label(label.value(buf)).unwrap().atom;
                    // Remove the definition from the pending list
                    if let Some(pending_index) =
                        self.pending_primitive.iter().position(|x| x.0 == primitive)
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

    fn verify_definition_statement(
        &mut self,
        syntax_axiom: Label,
        addr: StatementAddress,
    ) -> Result<(), Diagnostic> {
        let stmt = self.db.statement_by_address(addr);
        let definition = self.nset.lookup_label(stmt.label()).unwrap().atom;

        let syntax_addr = self.nset.lookup_label_by_atom(syntax_axiom).address;

        // push the definition to the validated list early, so that later definitions
        // aren't as messed up if this check fails
        self.result.definitions.insert(definition);
        if let Some(prev) = self.result.def_map.insert(syntax_axiom, definition) {
            return Err(Diagnostic::DefCkDuplicateDefinition(
                self.nset.atom_name(syntax_axiom).into(),
                self.nset.lookup_label_by_atom(prev).address,
            ));
        }

        if self.result.justifications.contains_key(&definition) {
            // Skip definitional check for definitions having a justification.

            // TODO check that the justification matches the definition
        } else {
            // Check that the top level of the definition is an equality
            let Some(fmla) = self.stmts.get_formula(&stmt) else {
                // Ok because the error would have been reported already
                return Ok(())
            };

            let root = fmla.root(self.db);
            let equality = root.label();
            match self.equalities.get(&equality) {
                None => {
                    self.equalities.insert(equality, false); // suppress future errors
                    return Err(Diagnostic::DefCkNotAnEquality(
                        self.nset.atom_name(equality).into(),
                        self.result
                            .equalities_by_tc
                            .iter()
                            .map(|(&label, _)| self.nset.atom_name(label).into())
                            .collect(),
                    ));
                }
                Some(false) => return Ok(()), // already reported the error
                Some(true) => {}
            }

            let Some(lhs) = root.nth_child(0) else {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            };
            if lhs.label() != syntax_axiom {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            }

            // TODO definition check
        }
        Ok(())
    }

    /// Called when something breaks a "definition block", forcing us to check the statements
    /// and purge them from the pending queue. We use this delayed checking mechanism
    /// to handle set.mm patterns like defining many syntax axioms followed by many definitions,
    /// or $j commands which come after the definitions they apply to.
    fn flush_pending_syntax(&mut self) {
        if !self.pending_syntax.is_empty() {
            self.flush_pending_definitions();

            self.pending_primitive
                .extend(self.pending_syntax.drain(..).map(|label| {
                    (
                        label,
                        self.db.statement_by_label(label).unwrap().address(),
                        Diagnostic::DefCkMissingDefinition,
                    )
                }));
        }
    }

    fn flush_pending_definitions(&mut self) {
        if !self.pending_defn.is_empty() {
            for (addr, syntax) in std::mem::take(&mut self.pending_defn) {
                if let Err(diag) = self.verify_definition_statement(syntax, addr) {
                    self.result.diagnostics.push((addr, diag));
                }
            }
        }
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
                            // TODO Check that the axiom label does _not_ start with `df-`.
                            let syntax_axiom = self.nset.lookup_label(stmt.label()).unwrap().atom;
                            self.pending_syntax.push(syntax_axiom);
                        } else if self.pending_syntax.is_empty() {
                            // No definition to check, this is a regular axiom
                            // TODO Check that the axiom label starts with `ax-`.
                        } else if let Some(syntax) =
                            self.ensure_frame_does_not_use_pending_syntax(&stmt, true)
                        {
                            // Definition, push it to the pending list for later processing
                            self.pending_defn.push((stmt.address(), syntax));
                        } else {
                            // Also a regular axiom, it uses no new definitions
                        }
                    }
                    StatementType::Provable => {
                        if !self.pending_syntax.is_empty() {
                            self.flush_pending_definitions();
                            self.ensure_frame_does_not_use_pending_syntax(&stmt, false);
                        }
                    }
                    _ => {}
                }
            }
        }

        self.flush_pending_syntax();
        for (_, addr, delayed_diag) in self.pending_primitive.drain(..) {
            self.result.diagnostics.push((addr, delayed_diag));
        }
    }

    fn ensure_frame_does_not_use_pending_syntax(
        &mut self,
        stmt: &StatementRef<'_>,
        except_for_one: bool,
    ) -> Option<Label> {
        let res = self.ensure_statement_does_not_use_pending_syntax(stmt, except_for_one);
        if let Some(frame) = self.scope.get(stmt.label()) {
            for hyp in &*frame.hypotheses {
                if let Hyp::Essential(addr, _) = *hyp {
                    let stmt = self.db.statement_by_address(addr);
                    self.ensure_statement_does_not_use_pending_syntax(&stmt, false);
                }
            }
        }
        res
    }

    fn ensure_statement_does_not_use_pending_syntax(
        &mut self,
        stmt: &StatementRef<'_>,
        except_for_one: bool,
    ) -> Option<Label> {
        let mut the_def = None;
        if let Some(f) = self.stmts.get_formula(stmt) {
            for (label, _) in f.labels_iter().filter(|(_, var)| !var) {
                if let Some(i) = self.pending_syntax.iter().position(|&x| x == label) {
                    self.pending_syntax.swap_remove(i);
                    if except_for_one && the_def.map_or(true, |l| l == label) {
                        the_def = Some(label)
                    } else {
                        self.pending_primitive.push((
                            label,
                            stmt.address(),
                            Diagnostic::DefCkSyntaxUsedBeforeDefinition(
                                self.nset.atom_name(label).into(),
                                self.nset.lookup_label_by_atom(label).address,
                            ),
                        ))
                    }
                }
            }
        }
        the_def
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
