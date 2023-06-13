//! Verification of definitions
//!
//! Implement verification of definitions per the set.mm/iset.mm conventions.
//! For more information see:
//! <https://us.metamath.org/mpeuni/conventions.html>
//! <https://github.com/digama0/mmj2/blob/master/mmj2jar/macros/definitionCheck.js>
//! and "Metamath: A Computer Language for Mathematical Proofs" by
//! Norman Megill and David A. Wheeler, 2019, page 155.

use std::collections::hash_map::Entry;
use std::sync::Arc;

use itertools::{Itertools, PeekingNext};

use crate::bit_set::Bitset;
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
    justifications: HashMap<Label, (Label, GlobalSpan)>,
    definitions: HashSet<Label>,
    /// Maps syntax axioms to the corresponding definitions
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

fn check_lhs(
    syntax: Label,
    f: SubFormulaRef<'_>,
    is_param: &mut Bitset,
    to_index: &HashMap<Label, usize>,
) -> bool {
    syntax == f.label()
        && f.children()
            .all(|v| v.is_variable() && !is_param.replace_bit(to_index[&v.label()]))
}

fn find_lhs<'a>(syntax: Label, f: SubFormulaRef<'a>, lhs: &mut Option<SubFormulaRef<'a>>) -> bool {
    if f.label() == syntax {
        if let Some(lhs2) = lhs {
            f == *lhs2
        } else {
            *lhs = Some(f);
            true
        }
    } else {
        f.children().all(|f| find_lhs(syntax, f, lhs))
    }
}

struct JustificationSubst<'a> {
    vars: HashMap<Label, SubFormulaRef<'a>>,
    rhs: Option<SubFormulaRef<'a>>,
}

fn match_justification<'a>(
    syntax: Label,
    just: SubFormulaRef<'a>,
    f: SubFormulaRef<'a>,
    subst: &mut JustificationSubst<'a>,
) -> bool {
    if f.label() == syntax {
        if let Some(rhs2) = &subst.rhs {
            just == *rhs2
        } else {
            subst.rhs = Some(just);
            just.labels_iter().all(|(label, _)| label != syntax)
        }
    } else if just.is_variable() {
        match subst.vars.entry(just.label()) {
            Entry::Occupied(e) => *e.get() == f,
            Entry::Vacant(e) => {
                e.insert(f);
                true
            }
        }
    } else {
        just.label() == f.label()
            && just
                .children()
                .zip(f.children())
                .all(|(just, f)| match_justification(syntax, just, f, subst))
    }
}

fn get_free_vars(_body: SubFormulaRef<'_>) -> HashSet<Label> {
    // TODO
    HashSet::default()
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

    fn check_syntax_axiom(&mut self, stmt: &StatementRef<'_>) -> Result<(), Diagnostic> {
        let Some(frame) = self.scope.get(stmt.label()) else { return Ok(()) };
        if frame
            .hypotheses
            .iter()
            .all(|hyp| matches!(hyp, Hyp::Floating(..)))
            && frame.mandatory_dv.is_empty()
            && frame.target.tail.iter().map(|frag| frag.var).all_unique()
        {
            Ok(())
        } else {
            Err(Diagnostic::DefCkMalformedSyntaxAxiom)
        }
    }

    // Parses the 'equality', 'primitive', and 'justification' commmands in the database,
    // and store the result in the database for future fast access.
    fn parse_command(
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
                self.result
                    .justifications
                    .insert(definition, (theorem, (sref.id, justif_label.span())));
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

        let Some(fmla) = self.stmts.get_formula(&stmt) else {
            // Ok because the error would have been reported already
            return Ok(())
        };
        let root = fmla.root(self.db);
        let mut is_param = Bitset::new();
        let mut free_dummies = HashSet::default();
        let lhs;

        let def_frame = self.scope.get(stmt.label()).unwrap();
        let mut to_index = HashMap::default();
        for (label, _) in root.labels_iter().filter(|&(_, var)| var) {
            to_index.entry(label).or_insert_with(|| {
                let atom = self.db.statement_by_label(label).unwrap().math_at(1).slice;
                let atom = self.db.name_result().get_atom(atom);
                def_frame.var_list.iter().position(|&i| i == atom).unwrap()
            });
        }

        if let Some(&(justification, span)) = self.result.justifications.get(&definition) {
            let mut opt_lhs = None;
            if !find_lhs(syntax_axiom, root, &mut opt_lhs) {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            }
            lhs = opt_lhs.unwrap();
            if !check_lhs(syntax_axiom, lhs, &mut is_param, &to_index) {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            }

            let just = self.db.statement_by_label(justification).unwrap();
            let just_body = self.stmts.get_formula(&just).unwrap().root(self.db);
            let mut subst = JustificationSubst {
                vars: HashMap::default(),
                rhs: None,
            };
            if !match_justification(syntax_axiom, just_body, root, &mut subst) {
                return Err(Diagnostic::DefCkMalformedJustification(span));
            }

            let just_frame = self.scope.get(just.label()).unwrap();
            let mut subst2 = vec![None; just_frame.mandatory_count];
            for hyp in &*just_frame.hypotheses {
                if let Hyp::Floating(addr, i, _) = *hyp {
                    let label = self.db.statement_by_address(addr).label();
                    subst2[i] = subst.vars.get(&self.nset.lookup_label(label).unwrap().atom);
                }
            }

            let mut violated_dv = HashSet::default();
            for &(i1, i2) in &*just_frame.mandatory_dv {
                if let (Some(f1), Some(f2)) = (subst2[i1], subst2[i2]) {
                    for &a1 in f1.labels_iter().filter_map(|(lab, _)| to_index.get(&lab)) {
                        for &a2 in f2.labels_iter().filter_map(|(lab, _)| to_index.get(&lab)) {
                            if !def_frame.optional_dv[a1].has_bit(a2) {
                                violated_dv.insert(a1);
                                violated_dv.insert(a2);
                            }
                        }
                    }
                }
            }

            if !violated_dv.is_empty() {
                let violated_dv = violated_dv
                    .into_iter()
                    .map(|i| self.nset.atom_name(def_frame.var_list[i]).into())
                    .sorted()
                    .collect();
                return Err(Diagnostic::DefCkFreeDummyVarsJustification(
                    just.address(),
                    violated_dv,
                ));
            }

            let rhs = subst.rhs.unwrap();
            let fvars = get_free_vars(rhs);

            for (label, var) in rhs.labels_iter() {
                if var && !subst.vars.contains_key(&label) && fvars.contains(&label) {
                    free_dummies.insert(label);
                }
            }

            if !free_dummies.is_empty() {
                let free_dummies = free_dummies
                    .into_iter()
                    .map(|atom| {
                        let sref = self.db.statement_by_label(atom).unwrap();
                        sref.math_at(1).slice.into()
                    })
                    .sorted()
                    .collect();
                self.result.diagnostics.push((
                    just.address(),
                    Diagnostic::DefCkFreeDummyVarsJustification(addr, free_dummies),
                ));
                return Ok(());
            }
        } else {
            // Check that the top level of the definition is an equality
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

            lhs = root.nth_child(0).unwrap();

            if !check_lhs(syntax_axiom, lhs, &mut is_param, &to_index) {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            }

            let mut all_vars = Bitset::new();
            let mut dummy_dv_violations = Bitset::new();
            for i in 0..def_frame.mandatory_count {
                all_vars.set_bit(i)
            }
            for i in (0..def_frame.mandatory_count).filter(|&i| !is_param.has_bit(i)) {
                let vars = &def_frame.optional_dv[i];
                all_vars.unset_bit(i);
                if !all_vars.is_subset_of(vars) {
                    dummy_dv_violations.set_bit(i);
                    for i in 0..def_frame.mandatory_count {
                        if !vars.has_bit(i) {
                            dummy_dv_violations.set_bit(i)
                        }
                    }
                }
                all_vars.set_bit(i);
            }

            if !dummy_dv_violations.is_empty() {
                let mut params = vec![];
                let mut dummies = vec![];
                for i in &dummy_dv_violations {
                    let var = self.nset.atom_name(def_frame.var_list[i]).into();
                    if is_param.has_bit(i) {
                        params.push(var)
                    } else {
                        dummies.push(var)
                    }
                }
                params.sort();
                dummies.sort();
                return Err(Diagnostic::DefCkDummyDj(
                    params.into_boxed_slice(),
                    dummies.into_boxed_slice(),
                ));
            }

            let rhs = root.nth_child(1).unwrap();
            if rhs.labels_iter().any(|(label, _)| label == syntax_axiom) {
                return Err(Diagnostic::DefCkMalformedDefinition(syntax_addr));
            }

            let fvars = get_free_vars(rhs);

            for (label, var) in rhs.labels_iter() {
                if var && !is_param.has_bit(to_index[&label]) && fvars.contains(&label) {
                    free_dummies.insert(label);
                }
            }

            if !free_dummies.is_empty() {
                let free_dummies = free_dummies
                    .into_iter()
                    .map(|atom| {
                        let sref = self.db.statement_by_label(atom).unwrap();
                        sref.math_at(1).slice.into()
                    })
                    .sorted()
                    .collect();
                return Err(Diagnostic::DefCkFreeDummyVars(free_dummies));
            }
        }

        let mut dv_params = HashSet::default();
        for &(i1, i2) in &*def_frame.mandatory_dv {
            if is_param.has_bit(i1) && is_param.has_bit(i2) {
                dv_params.insert(i1);
                dv_params.insert(i2);
            }
        }

        if !dv_params.is_empty() {
            let dv_params = dv_params
                .into_iter()
                .map(|i| self.nset.atom_name(def_frame.var_list[i]).into())
                .sorted()
                .collect();
            return Err(Diagnostic::DefCkParameterDj(dv_params));
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
    /// All statements are scanned, and the checker expects to find, for each definition, first, a syntax axiom,
    /// and then, either a `primitive` command, or the definition.
    fn verify_definitions(&mut self, sset: &SegmentSet) {
        for sref in sset.segments(..) {
            let mut j_commands = sref.j_commands.iter();
            for stmt in sref.range(..) {
                match stmt.statement_type() {
                    StatementType::AdditionalInfoComment => {
                        while let Some(&(index, (span, ref args))) =
                            j_commands.peeking_next(|i| i.0 == stmt.index)
                        {
                            if let Err(diag) = self.parse_command(sref, index, span, args) {
                                self.result.diagnostics.push((stmt.address(), diag));
                            }
                        }
                    }
                    StatementType::Axiom => {
                        if self.nset.get_atom(stmt.math_at(0).slice)
                            != self.grammar.provable_typecode()
                        {
                            // Non-provable typecodes are syntax axioms.
                            if let Err(diag) = self.check_syntax_axiom(&stmt) {
                                self.result.diagnostics.push((stmt.address(), diag));
                            }
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

    /// Ensures the given frame does not use pending syntax.
    /// If `except_for_one` is `True`, one occurrence of the syntax is allowed,
    /// only in the main statement, and the label of that syntax axiom is returned.
    /// Unallowed occurrences are added to the `pending_primitive` table.
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

    /// Ensures the given statement does not use pending syntax.
    /// If `except_for_one` is `True`, one occurrence of the syntax is allowed,
    /// and the label of that syntax axiom is returned.
    /// Unallowed occurrences are added to the `pending_primitive` table.
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
