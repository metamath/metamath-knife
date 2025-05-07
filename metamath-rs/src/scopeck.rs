//! This module calculates 3 things which are related only by the fact that they
//! can be done at the same time:
//!
//! 1. For `$c $v $f` and labelled statements (`$e $f $a $p`): Check for
//!    duplication
//!
//! 2. For `$e $d $f $a $p`: Check that all used math symbols are active in
//!    scope
//!
//! 3. For `$a $p`: Compute the frame
//!
//! Rules of precedence for error detection and recovery:
//!
//! 1. Math symbols and labels are actually in separate namespaces.  We warn
//!    about collisions but otherwise do nothing.  Variables have responsibility
//!    for the warning.
//!
//! 2. When two definitions have overlapping live ranges, the earlier one wins.
//!
//! 3. Constant/nested variable collisions are special because they don't
//!    involve scope overlaps. The constant wins, the variable must notify.
//!
//! Since this is always run before the verifier, it focuses on supporting the
//! verifier; things that the verifier won't use mostly aren't done.  This
//! principally affects frame generation for for `$e` statements and atomization
//! of math strings.
//!
//! The scope check procedure runs a single pass over the statements in a
//! segment, tracking the active `$e` and `$f` statements at each point.

use crate::bit_set::Bitset;
use crate::diag::Diagnostic;
use crate::nameck::{Atom, NameReader, NameUsage, Nameset};
use crate::segment::{Comparer, Segment, SegmentOrder, SegmentRef};
use crate::segment_set::SegmentSet;
use crate::statement::{
    GlobalRange, SegmentId, StatementAddress, StatementIndex, SymbolType, Token, TokenAddress,
    TokenPtr, TokenRef, NO_STATEMENT,
};
use crate::util::{fast_extend, HashMap, HashSet};
use crate::{parser, Label};
use crate::{Database, StatementType};
use crate::{Formula, StatementRef};
use std::collections::VecDeque;
use std::ops::Range;
use std::sync::Arc;

/// Information on a `$v` active in the local or global scope.
#[derive(Clone, Copy)]
struct LocalVarInfo {
    /// Definition location
    start: TokenAddress,
    /// Exclusive end of the valid range
    end: StatementIndex,
    /// Atom for the variable name
    atom: Atom,
}

/// Information on a `$f` active in scope
#[derive(Copy, Clone, Debug, Default)]
struct LocalFloatInfo {
    valid: GlobalRange,
    typecode: Atom,
}

/// Information on a math symbol which has been determined to be valid in the
/// current scope
#[derive(Copy, Clone, Debug)]
enum CheckedToken<'a> {
    Const(TokenPtr<'a>, Atom),
    Var(TokenPtr<'a>, Atom, LocalFloatInfo),
}
use self::CheckedToken::*;

/// Information on a `$d` statement active in the local scope
#[derive(Clone, Debug)]
struct LocalDvInfo {
    valid: GlobalRange,
    vars: Vec<Atom>,
}

#[derive(Clone, Debug)]
struct LocalEssentialInfo<'a> {
    valid: GlobalRange,
    _label: TokenPtr<'a>,
    string: Vec<CheckedToken<'a>>,
}

/// Semantic type for renamed variables.
///
/// Within each frame, variable names are replaced with small integers.
pub type VarIndex = usize;

/// A literal-variable pair, used in the frame expressions.
#[derive(Clone, Debug)]
pub struct ExprFragment {
    /// Pointer into the frame's constant pool for a literal span consisting of
    /// zero or more constant symbols.
    pub prefix: Range<usize>,
    /// A variable to subsitute after the literal span.
    pub var: VarIndex,
}

/// An expression which can be substituted with variables in the verifier.
///
/// All variables are replaced with integers and the expression is broken at
/// each variable into an alternating sequence of literal segments and variable
/// subsitutions.  The first symbol is required by the spec to be a constant and
/// has special matching behavior, so it is represented out of band as an atom.
///
/// The verifier represents math strings as byte sequences, where the boundaries
/// between math symbols are indicated by setting the 8th bit on the last byte
/// of each symbol.  The same compressed representation is used in literal
/// segments so that execution can be simple copying.
#[derive(Clone, Default, Debug)]
pub struct VerifyExpr {
    /// Atom representation of the first constant symbol in the expression.
    pub typecode: Atom,
    /// Constant pool reference for the part of the expression after the last
    /// variable.
    pub rump: Range<usize>,
    /// The parts of the expression up to and including the last variable, as a
    /// sequence of literal, variable pairs.
    pub tail: Box<[ExprFragment]>,
}

impl VerifyExpr {
    /// Returns an iterator over runs of constants in the expression,
    /// as references into the constant pool.
    pub fn const_ranges(&self) -> impl Iterator<Item = Range<usize>> + '_ {
        (self.tail.iter().map(|e| &e.prefix))
            .chain(std::iter::once(&self.rump))
            .cloned()
    }
}

/// Representation of a hypothesis in a frame program.
#[derive(Clone, Debug)]
pub enum Hyp {
    /// An `$e` hypothesis, which is substituted and then compared to a stack
    /// slot.
    Essential(StatementAddress, VerifyExpr),
    /// A `$f` hypothesis, which is checked against the typecode on the stack
    /// and then used to augment the subsitution.
    Floating(StatementAddress, VarIndex, Atom),
}

impl Hyp {
    /// Returns the address of the statement which created this hypothesis.
    #[must_use]
    pub const fn address(&self) -> StatementAddress {
        match *self {
            Hyp::Essential(addr, _) | Hyp::Floating(addr, _, _) => addr,
        }
    }

    /// Returns the typecode expected on the stack for this hypothesis.
    #[must_use]
    pub const fn typecode(&self) -> Atom {
        match *self {
            Hyp::Essential(_, ref expr) => expr.typecode,
            Hyp::Floating(_, _, typecode) => typecode,
        }
    }
}

/// Frames represent the logical content of the database, and are the main work
/// product of the scope check pass.
///
/// Every `$a` and `$p` statement in the database is associated with a "frame"
/// and an "extended frame" as defined in the Metamath spec.  The frame consists
/// of the math string of the statement, the strings of all hypotheses, and any
/// disjoint variable hypotheses which are required to hold when using the
/// statement in a later proof; the extended frame additionally contains types
/// and disjointness conditions for variables that may be used in the proof, but
/// are not mentioned in the hypotheses and thus need not be respected by users.
///
/// In the spec, the extended frame includes all `$f` statements which are in
/// scope.  We do not actually track optional `$f` statements directly in the
/// frame; instead, when you encounter a use of a `$f` statement in a proof, you
/// need to look it up and check the valid range to see if it can be used in the
/// current proof.  `$f` statements are tracked using the same `Frame` data
/// type, although they do not strictly speaking have associated frames.
///
/// Since the primary user of frames currently is the verifier, the format is
/// heavily tuned for what the verifier requires.  From the verifier's
/// perspective, the main use of a frame is to match the top several entries in
/// a proof stack and perform substitutions; the frame may be considered a kind
/// of program, and optimizations are taken for the execution of steps.
///
/// _Support for non-verifier users of frame data is expected to be quite weak
/// at the present time._
///
/// Variable names are replaced with small integers so that the substitution
/// being built can be maintained as an array.
#[derive(Clone, Debug, Default)]
pub struct Frame {
    /// Type of this statement, will be `StatementType::Axiom`,
    /// `StatementType::Floating`, or `StatementType::Provable`.
    pub stype: StatementType,
    /// Valid range of this statement.
    ///
    /// Use this to ensure that `$f` pseudo-frames are used only where they are
    /// in scope, and that `$a $p` frames are not used before they are defined.
    pub valid: GlobalRange,
    /// Atom representation of this statement's label (valid only if
    /// `incremental`).
    pub label_atom: Atom,
    /// Backing array for all literal fragments in the hypotheses and target
    /// expression.
    pub const_pool: Box<[u8]>,
    /// Ordered list of hypotheses required by this frame.
    ///
    /// The last entry corresponds to the top of the stack at application time.
    /// If you process hypotheses in the order of this list, then you will never
    /// need to subsitute a variable before it has been set; this is a
    /// consequence of Metamath rules requiring `$f` to be in scope for an `$e`
    /// to be valid.
    pub hypotheses: Box<[Hyp]>,
    /// Expression which is subsituted and pushed on the stack after validating
    /// hypotheses.
    pub target: VerifyExpr,
    /// Compressed representation of the variable name, used only for `$f`
    /// pseudo-frames.
    pub stub_expr: Box<[u8]>,
    /// Mapping from variable indices to the variable names.
    pub var_list: Box<[Atom]>,
    /// Length of the prefix of `var_list` representing mandatory variables; the
    /// number of slots in the subsitution for this frame.
    pub mandatory_count: usize,
    /// List of pairs of variables in simple mandatory disjoint variable
    /// constraints for this frame.
    pub mandatory_dv: Box<[(VarIndex, VarIndex)]>,
    /// Two-dimensional bit array of pairs of variables which can be treated as
    /// disjoint in proofs of this frame.
    pub optional_dv: Box<[Bitset]>,
}

impl Frame {
    /// Augment a frame with a database reference, to produce a [`FrameRef`].
    #[must_use]
    pub const fn as_ref<'a>(&'a self, db: &'a Database) -> FrameRef<'a> {
        FrameRef { db, frame: self }
    }

    /// The list of mandatory variables in the frame.
    #[must_use]
    pub fn mandatory_vars(&self) -> &[Atom] {
        &self.var_list[..self.mandatory_count]
    }

    /// The list of mandatory hypotheses in the frame.
    /// Every [`Hyp`] in this list will be [`Hyp::Floating`].
    #[must_use]
    pub fn mandatory_hyps(&self) -> &[Hyp] {
        &self.hypotheses[..self.mandatory_count]
    }
}

/// Data which is tracked during scope checking, but discarded when done.
struct ScopeState<'a> {
    /// Accumulated errors for this segment.
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    /// Segment ordering in effect.
    order: &'a SegmentOrder,
    /// Name data for this database (used for atom lookups only).
    nameset: &'a Nameset,
    /// Name reader, tracks labels and math symbols used in this segment.
    gnames: NameReader<'a>,
    /// Local `$v` statements in effect at this point.
    local_vars: HashMap<Token, Vec<LocalVarInfo>>,
    /// Local `$f` statements in effect at this point.
    local_floats: HashMap<Token, Vec<LocalFloatInfo>>,
    /// Local `$d` statements in effect at this point.
    local_dv: Vec<LocalDvInfo>,
    /// Local `$e` statements in effect at this point.
    local_essen: Vec<LocalEssentialInfo<'a>>,
    /// Frames built so far.
    frames_out: Vec<Frame>,
}

fn push_diagnostic(state: &mut ScopeState<'_>, ix: StatementIndex, diag: Diagnostic) {
    state.diagnostics.entry(ix).or_default().push(diag);
}

/// Verifies that this is the true (first) use of a label.  The returned atom
/// will be meaningful only in incremental mode, but the `is_some` state is
/// always usable.
fn check_label_dup(state: &mut ScopeState<'_>, sref: StatementRef<'_>) -> Option<Atom> {
    // is the label unique in the database?
    if let Some(def) = state.gnames.lookup_label(sref.label()) {
        if def.address != sref.address() {
            push_diagnostic(state, sref.index(), Diagnostic::DuplicateLabel(def.address));
            return None;
        }
        return Some(def.atom);
    }
    unreachable!()
}

/// Find the definition of a math symbol and verify that it is in scope.
fn check_math_symbol(
    state: &mut ScopeState<'_>,
    s_ref: StatementRef<'_>,
    t_ref: TokenRef<'_>,
) -> Option<(SymbolType, Atom)> {
    // active global definition?
    if let Some(sdef) = state.gnames.lookup_symbol(&t_ref) {
        if state.order.lt(&sdef.address, &t_ref.address) {
            return Some((sdef.stype, sdef.atom));
        }
    }

    // active local definition?
    if let Some(local_slot) = state
        .local_vars
        .get(t_ref.slice)
        .and_then(|slot| slot.last())
    {
        if check_endpoint(s_ref.index(), local_slot.end) {
            return Some((SymbolType::Variable, local_slot.atom));
        }
    }

    push_diagnostic(
        state,
        s_ref.index(),
        Diagnostic::NotActiveSymbol(t_ref.index()),
    );
    None
}

/// Find the active typecode for a variable.
fn lookup_float<'a>(
    state: &mut ScopeState<'a>,
    s_ref: StatementRef<'a>,
    t_ref: TokenRef<'a>,
) -> Option<LocalFloatInfo> {
    // active global definition?
    if let Some(fdef) = state.gnames.lookup_float(&t_ref) {
        if state.order.lt(&fdef.address, &s_ref.address()) {
            return Some(LocalFloatInfo {
                valid: fdef.address.unbounded_range(),
                typecode: fdef.typecode_atom,
            });
        }
    }

    // active local definition?
    if let Some(&local_slot) = state
        .local_floats
        .get(t_ref.slice)
        .and_then(|slot| slot.last())
    {
        if check_endpoint(s_ref.index(), local_slot.valid.end) {
            return Some(local_slot);
        }
    }

    None
}

/// Given a math string, verify that all tokens are active, all variables have
/// typecodes, and the head is a constant.
fn check_eap<'a>(
    state: &mut ScopeState<'a>,
    s_ref: StatementRef<'a>,
) -> Option<Vec<CheckedToken<'a>>> {
    let mut bad = false;
    let mut out = Vec::with_capacity(s_ref.math_len() as usize);

    for t_ref in s_ref.math_iter() {
        match check_math_symbol(state, s_ref, t_ref) {
            None => bad = true,
            Some((SymbolType::Constant, atom)) => {
                out.push(Const(t_ref.slice, atom));
            }
            Some((SymbolType::Variable, atom)) => {
                if t_ref.index() == 0 {
                    push_diagnostic(state, s_ref.index(), Diagnostic::ExprNotConstantPrefix(0));
                    bad = true;
                } else {
                    match lookup_float(state, s_ref, t_ref) {
                        None => {
                            push_diagnostic(
                                state,
                                s_ref.index(),
                                Diagnostic::VariableMissingFloat(t_ref.index()),
                            );
                            bad = true;
                        }
                        Some(lfi) => out.push(Var(t_ref.slice, atom, lfi)),
                    }
                }
            }
        }
    }

    if bad {
        None
    } else {
        Some(out)
    }
}

/// Constructs the psuedo-frames which are required by the verifier for optional
/// `$f` hypotheses.
fn construct_stub_frame(
    state: &mut ScopeState<'_>,
    s_ref: StatementRef<'_>,
    l_atom: Atom,
    expr: &[CheckedToken<'_>],
) {
    let mut iter = expr.iter();
    let typecode = match *iter.next().expect("parser checks $eap token count") {
        Const(_, typecode) => typecode,
        Var(..) => unreachable!(),
    };
    let mut mvars = Vec::new();
    let mut conststr = Vec::new();

    for &ctok in iter {
        match ctok {
            Const(t_ref, _) => {
                conststr.extend_from_slice(t_ref);
                *conststr.last_mut().unwrap() |= 0x80;
            }
            Var(t_ref, atom, _) => {
                conststr.extend_from_slice(t_ref);
                *conststr.last_mut().unwrap() |= 0x80;
                mvars.push(atom);
            }
        }
    }

    state.frames_out.push(Frame {
        stype: s_ref.statement_type(),
        label_atom: l_atom,
        valid: s_ref.scope_range(),
        hypotheses: Box::default(),
        target: VerifyExpr {
            typecode,
            rump: 0..0,
            tail: Box::default(),
        },
        const_pool: Box::default(),
        stub_expr: conststr.into_boxed_slice(),
        mandatory_count: mvars.len(),
        var_list: mvars.into_boxed_slice(),
        mandatory_dv: Box::default(),
        optional_dv: Box::default(),
    });
}

/// Data used to build a frame.
///
/// This is not part of `ScopeState` due to incompatible borrowing constraints.
struct InchoateFrame {
    /// Variables referenced so far while processing `$e` hypotheses, used to
    /// find mandatory `$f` hypotheses.
    variables: HashMap<Atom, (VarIndex, LocalFloatInfo)>,
    /// Variables referenced so far by index.
    var_list: Vec<Atom>,
    /// Set to the count of mandatory variables before adding optional
    /// variables.
    mandatory_count: usize,
    /// Accumulator for disjoint variable constraints which fall within the
    /// mandatory range.
    mandatory_dv: Vec<(VarIndex, VarIndex)>,
    /// Accumulator for disjoint variable constraints regardless of index.
    optional_dv: Vec<Bitset>,
    /// Literal fragments are written here, becomes the frame's constant pool.
    const_pool: Vec<u8>,
}

/// Given a math string previously processed by `check_eap`, generate the
/// substitution program for the verifier.
///
/// Also responsible for building the list of mandatory variables for the
/// inchoate frame.
fn scan_expression(iframe: &mut InchoateFrame, expr: &[CheckedToken<'_>]) -> VerifyExpr {
    let mut iter = expr.iter();
    let head = match *iter.next().expect("parser checks $eap token count") {
        Const(_, head) => head,
        Var(..) => unreachable!(),
    };
    let mut open_const = iframe.const_pool.len();
    let mut tail = Vec::with_capacity(expr.len());

    for &ctok in iter {
        match ctok {
            Const(tref, _) => {
                fast_extend(&mut iframe.const_pool, tref);
                // since we restrict tokens to 7-bit, this can be used as a delimiter
                *iframe.const_pool.last_mut().unwrap() |= 0x80;
            }
            Var(_, atom, lfi) => {
                // check if the variable is in use
                #[allow(clippy::map_unwrap_or)]
                let index = iframe
                    .variables
                    .get(&atom)
                    .map(|&(x, _)| x)
                    .unwrap_or_else(|| {
                        // it's not!  record it in the frame, and save the $f info for later
                        let index = iframe.variables.len();
                        iframe.var_list.push(atom);
                        // make room in the dv-list
                        iframe.optional_dv.push(Bitset::new());
                        iframe.variables.insert(atom, (index, lfi));
                        index
                    });
                // the tail is broken at each variable, so start a new segment
                tail.push(ExprFragment {
                    prefix: open_const..iframe.const_pool.len(),
                    var: index,
                });
                open_const = iframe.const_pool.len();
            }
        }
    }

    VerifyExpr {
        typecode: head,
        rump: open_const..iframe.const_pool.len(),
        tail: tail.into_boxed_slice(),
    }
}

/// Adds a compound disjoint variable hypothesis to the frame being built.
fn scan_dv(iframe: &mut InchoateFrame, var_set: &[Atom]) {
    // any variable encountered for the first time in a dv is an optional
    // variable, but we already checked validity in scope_check_dv
    let mut var_ids = Vec::with_capacity(var_set.len());

    for &varatom in var_set {
        let index = if let Some(mvarindex) = iframe.variables.get(&varatom).map(|&(x, _)| x) {
            mvarindex
        } else {
            // it's not a mandatory variable and so we don't need $f info,
            // but it still needs to be indexed.
            let index = iframe.variables.len();
            iframe.var_list.push(varatom);
            iframe.optional_dv.push(Bitset::new());
            iframe
                .variables
                .insert(varatom, (index, LocalFloatInfo::default()));
            index
        };
        var_ids.push(index);
    }

    // we've been extending optional_dv every time we add a new variable, so the
    // indexing is safe here
    for (leftpos, &leftid) in var_ids.iter().enumerate() {
        for &rightid in &var_ids[leftpos + 1..] {
            if !iframe.optional_dv[leftid].replace_bit(rightid) {
                iframe.optional_dv[rightid].set_bit(leftid);
                if leftid < iframe.mandatory_count && rightid < iframe.mandatory_count {
                    iframe.mandatory_dv.push((leftid, rightid));
                }
            }
        }
    }
}

/// Actually constructs frame programs for `$a`/`$p` statements.
fn construct_full_frame<'a>(
    state: &mut ScopeState<'a>,
    sref: StatementRef<'a>,
    label_atom: Atom,
    expr: &[CheckedToken<'a>],
) {
    state
        .local_essen
        .retain(|hyp| check_endpoint(sref.index(), hyp.valid.end));
    state
        .local_dv
        .retain(|hyp| check_endpoint(sref.index(), hyp.valid.end));
    // local_essen and local_dv now contain only things still in scope

    // collect mandatory variables
    let mut iframe = InchoateFrame {
        variables: HashMap::default(),
        var_list: Vec::new(),
        optional_dv: Vec::new(),
        mandatory_dv: Vec::new(),
        mandatory_count: 0,
        const_pool: Vec::new(),
    };
    let mut hyps = Vec::new();

    for ess in &state.local_essen {
        let scanned = scan_expression(&mut iframe, &ess.string);
        hyps.push(Hyp::Essential(ess.valid.start, scanned));
    }

    let scan_res = scan_expression(&mut iframe, expr);
    // we now have all $e hyps and all mandatory variables, with $f data.  note
    // that the $e hyps are not in their final positions because the $f have not
    // been inserted

    // include any mandatory $f hyps
    for &(index, ref lfi) in iframe.variables.values() {
        hyps.push(Hyp::Floating(lfi.valid.start, index, lfi.typecode));
    }

    hyps.sort_by(|h1, h2| state.order.cmp(&h1.address(), &h2.address()));
    // any variables added for DV are not mandatory
    iframe.mandatory_count = iframe.var_list.len();

    for (_, vars) in state.gnames.lookup_global_dv() {
        scan_dv(&mut iframe, vars)
    }

    for dv in &state.local_dv {
        scan_dv(&mut iframe, &dv.vars);
    }

    state.frames_out.push(Frame {
        stype: sref.statement_type(),
        label_atom,
        valid: sref.address().unbounded_range(),
        hypotheses: hyps.into_boxed_slice(),
        target: scan_res,
        stub_expr: Box::default(),
        const_pool: iframe.const_pool.into_boxed_slice(),
        var_list: iframe.var_list.into_boxed_slice(),
        mandatory_count: iframe.mandatory_count,
        mandatory_dv: iframe.mandatory_dv.into_boxed_slice(),
        optional_dv: iframe.optional_dv.into_boxed_slice(),
    });
}

fn scope_check_assert<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if let Some(latom) = check_label_dup(state, sref) {
        if let Some(expr) = check_eap(state, sref) {
            construct_full_frame(state, sref, latom, &expr);
        }
    }
}

fn scope_check_constant(state: &mut ScopeState<'_>, sref: StatementRef<'_>) {
    if sref.in_group() {
        // nested $c are ignored by smetamath3, the parser generates a
        // diagnostic

        // assert!(sref.statement.diagnostics.len() > 0);
        return;
    }

    for tref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(&tref) {
            push_diagnostic(
                state,
                sref.index(),
                Diagnostic::SymbolDuplicatesLabel(tref.index(), ldef.address),
            );
        }

        if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
            if cdef.address != tref.address {
                push_diagnostic(
                    state,
                    sref.index(),
                    Diagnostic::SymbolRedeclared(tref.index(), cdef.address),
                );
            }
        }
    }
}

fn scope_check_dv<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut used = HashMap::default();
    let mut bad = false;
    let mut vars = Vec::new();

    for tref in sref.math_iter() {
        match check_math_symbol(state, sref, tref) {
            None => bad = true,
            Some((SymbolType::Constant, _)) => {
                push_diagnostic(state, sref.index(), Diagnostic::DjNotVariable(tref.index()));
                bad = true;
            }
            Some((SymbolType::Variable, varat)) => {
                if let Some(&previx) = used.get(&varat) {
                    push_diagnostic(
                        state,
                        sref.index(),
                        Diagnostic::DjRepeatedVariable(tref.index(), previx),
                    );
                    bad = true;
                    continue;
                }

                used.insert(varat, tref.index());
                vars.push(varat);
            }
        }
    }

    if bad {
        return;
    }

    // we need to do validity checking on global $d _somewhere_, and that
    // happens to be here, but the knowledge of the $d is handled by nameck
    // in that case and we need to not duplicate it
    if sref.in_group() {
        // record the $d in our local storage, will be deleted in
        // construct_full_frame when it's no longer in scope
        state.local_dv.push(LocalDvInfo {
            valid: sref.scope_range(),
            vars,
        });
    }
}

fn scope_check_essential<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if check_label_dup(state, sref).is_some() {
        if let Some(expr) = check_eap(state, sref) {
            // record the $e in our local storage, will be deleted in
            // construct_full_frame when it's no longer in scope
            state.local_essen.push(LocalEssentialInfo {
                valid: sref.scope_range(),
                _label: sref.label(),
                string: expr,
            });
        }
    }
}

fn scope_check_float<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut bad = false;
    // length checked by the parser with an invalidation
    assert!(sref.math_len() == 2);
    let const_tok = sref.math_at(0);
    let var_tok = sref.math_at(1);

    let Some(l_atom) = check_label_dup(state, sref) else {
        return;
    };

    // $f must be one constant and one variable - parser can't check this
    let mut const_at = Atom::default();
    match check_math_symbol(state, sref, const_tok) {
        None => bad = true,
        Some((SymbolType::Constant, atom)) => const_at = atom,
        Some((SymbolType::Variable, _)) => {
            push_diagnostic(state, sref.index(), Diagnostic::FloatNotConstant(0));
            bad = true;
        }
    }

    let mut var_at = Atom::default();
    match check_math_symbol(state, sref, var_tok) {
        None => bad = true,
        Some((SymbolType::Variable, atom)) => var_at = atom,
        _ => {
            push_diagnostic(state, sref.index(), Diagnostic::FloatNotVariable(1));
            bad = true;
        }
    }

    if bad {
        return;
    }

    if let Some(prev) = lookup_float(state, sref, sref.math_at(1)) {
        push_diagnostic(
            state,
            sref.index(),
            Diagnostic::FloatRedeclared(prev.valid.start),
        );
        return;
    }

    // record the $f; global $f are tracked by nameck but must still be verified
    // here
    if sref.in_group() {
        state
            .local_floats
            .entry((*var_tok).into())
            .or_default()
            .push(LocalFloatInfo {
                typecode: const_at,
                valid: sref.scope_range(),
            });
    }

    let expr = [
        Const(&const_tok, const_at),
        Var(&var_tok, var_at, LocalFloatInfo::default()),
    ];
    construct_stub_frame(state, sref, l_atom, &expr);
}

const fn check_endpoint(cur: StatementIndex, end: StatementIndex) -> bool {
    end == NO_STATEMENT || cur < end
}

// factored out to make a useful borrow scope
fn maybe_add_local_var(
    state: &mut ScopeState<'_>,
    s_ref: StatementRef<'_>,
    t_ref: TokenRef<'_>,
) -> Option<TokenAddress> {
    let lv_slot = state.local_vars.entry((*t_ref).into()).or_default();

    if let Some(lv_most_recent) = lv_slot.last() {
        if check_endpoint(s_ref.index(), lv_most_recent.end) {
            return Some(lv_most_recent.start);
        }
    }

    lv_slot.push(LocalVarInfo {
        start: t_ref.address,
        end: s_ref.scope_range().end,
        atom: state.nameset.get_atom(&t_ref),
    });
    None
}

fn scope_check_variable(state: &mut ScopeState<'_>, sref: StatementRef<'_>) {
    for tref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(&tref) {
            push_diagnostic(
                state,
                sref.index(),
                Diagnostic::SymbolDuplicatesLabel(tref.index(), ldef.address),
            );
        }

        if !sref.in_group() {
            // top level $v, may conflict with a prior $c
            if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
                if cdef.address != tref.address {
                    push_diagnostic(
                        state,
                        sref.index(),
                        Diagnostic::SymbolRedeclared(tref.index(), cdef.address),
                    );
                }
            }
        } else {
            // nested $v, may conflict with an outer scope $v, top level $v/$c,
            // or a _later_ $c
            if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
                if state.order.lt(&cdef.address, &tref.address) {
                    push_diagnostic(
                        state,
                        sref.index(),
                        Diagnostic::SymbolRedeclared(tref.index(), cdef.address),
                    );
                    continue;
                } else if cdef.stype == SymbolType::Constant {
                    push_diagnostic(
                        state,
                        sref.index(),
                        Diagnostic::VariableRedeclaredAsConstant(tref.index(), cdef.address),
                    );
                    continue;
                }
            }

            // recorded in local state here
            if let Some(prev_addr) = maybe_add_local_var(state, sref, tref) {
                // local/local conflict
                push_diagnostic(
                    state,
                    sref.index(),
                    Diagnostic::SymbolRedeclared(tref.index(), prev_addr),
                );
            }
        }
    }
}

/// Data generated by the scope checking process for a segment.
#[derive(Debug)]
struct SegmentScopeResult {
    id: SegmentId,
    source: Arc<Segment>,
    name_usage: NameUsage,
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    frames_out: Vec<Frame>,
}

/// Runs scope checking for a single segment.
fn scope_check_single(
    sset: &SegmentSet,
    names: &Nameset,
    seg: SegmentRef<'_>,
) -> SegmentScopeResult {
    let mut state = ScopeState {
        diagnostics: HashMap::default(),
        order: &sset.order,
        nameset: names,
        gnames: NameReader::new(names),
        local_vars: HashMap::default(),
        local_floats: HashMap::default(),
        local_dv: Vec::new(),
        local_essen: Vec::new(),
        frames_out: Vec::new(),
    };

    for sref in seg {
        match sref.statement_type() {
            StatementType::Constant => scope_check_constant(&mut state, sref),
            StatementType::Disjoint => scope_check_dv(&mut state, sref),
            StatementType::Essential => scope_check_essential(&mut state, sref),
            StatementType::Floating => scope_check_float(&mut state, sref),
            StatementType::Axiom | StatementType::Provable => scope_check_assert(&mut state, sref),
            StatementType::Variable => scope_check_variable(&mut state, sref),
            _ => {}
        }
    }

    state.frames_out.shrink_to_fit();

    SegmentScopeResult {
        id: seg.id,
        source: (*seg).clone(),
        name_usage: state.gnames.into_usage(),
        diagnostics: state.diagnostics,
        frames_out: state.frames_out,
    }
}

/// Data generated by scope checking for a database.
///
/// To extract frames, use a `ScopeReader`.
#[derive(Default, Clone, Debug)]
pub struct ScopeResult {
    incremental: bool,
    generation: usize,
    segments: Vec<Option<Arc<SegmentScopeResult>>>,
    frame_index: HashMap<Token, (usize, usize, usize)>,
}

impl ScopeResult {
    /// Returns a list of errors that were generated during the scope
    /// computation.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sid, ssro) in self.segments.iter().enumerate() {
            if let Some(ref ssr) = *ssro {
                for (&six, diag) in &ssr.diagnostics {
                    for d in diag {
                        out.push((StatementAddress::new(SegmentId(sid as u32), six), d.clone()));
                    }
                }
            }
        }
        out
    }

    /// Fetch a frame.
    #[must_use]
    pub fn get(&self, name: TokenPtr<'_>) -> Option<&Frame> {
        self.frame_index
            .get(name)
            .map(|&(_gen, segid, frix)| &self.segments[segid].as_ref().unwrap().frames_out[frix])
    }
}

/// Extracts scope data for a database.
///
/// Use `ScopeResult::default()` to get an initial state.
pub(crate) fn scope_check(result: &mut ScopeResult, segments: &SegmentSet, names: &Nameset) {
    result.incremental |= result.frame_index.is_empty();
    result.incremental &= segments.options.incremental;
    result.generation += 1;
    let gen = result.generation;
    let mut ssrq = VecDeque::new();
    // process all segments in parallel to get new scope results or identify
    // reusable ones
    {
        let mut prev = HashMap::default();
        for (sid, ssr) in result.segments.iter().enumerate() {
            prev.insert(SegmentId(sid as u32), ssr.clone());
        }
        for sref in segments.segments(..) {
            let segments2 = segments.clone();
            let names = names.clone();
            let id = sref.id;
            let osr = prev.get(&id).and_then(Option::clone);
            ssrq.push_back(segments.exec.exec(sref.bytes(), move || {
                let sref = segments2.segment(id);
                if let Some(old_res) = osr {
                    if old_res.name_usage.valid(&names) && Arc::ptr_eq(&old_res.source, &sref) {
                        return None;
                    }
                }
                if segments2.options.trace_recalc {
                    println!("scopeck({:?})", parser::guess_buffer_name(&sref.buffer));
                }
                Some(Arc::new(scope_check_single(&segments2, &names, sref)))
            }));
        }
    }

    // now update the hashtable
    let mut stale_ids = HashSet::default();
    let mut to_add = Vec::new();

    for (sid, res) in result.segments.iter().enumerate() {
        if res.is_some() {
            stale_ids.insert(SegmentId(sid as u32));
        }
    }

    for sref in segments.segments(..) {
        match ssrq.pop_front().unwrap().wait() {
            Some(scoperes) => {
                to_add.push(scoperes);
            }
            None => {
                stale_ids.remove(&sref.id);
            }
        }
    }

    for stale_id in stale_ids {
        let oseg = result.segments[stale_id.0 as usize].take().unwrap();
        let sref = SegmentRef {
            segment: &oseg.source,
            id: stale_id,
        };
        for frame in &oseg.frames_out {
            let label = sref.statement(frame.valid.start.index).label();
            result
                .frame_index
                .remove(label)
                .expect("check_label_dup should prevent this");
        }
    }

    for res_new in to_add {
        let seg_index = res_new.id.0 as usize;
        if seg_index >= result.segments.len() {
            result.segments.resize(seg_index + 1, None);
        }

        let sref = segments.segment(res_new.id);
        for (index, frame) in res_new.frames_out.iter().enumerate() {
            let label = sref.statement(frame.valid.start.index).label().into();
            let old = result.frame_index.insert(label, (gen, seg_index, index));
            assert!(old.is_none(), "check_label_dup should prevent this");
        }

        result.segments[seg_index] = Some(res_new);
    }
}

/// A [`Frame`] reference in the context of a [`Database`].
/// This allows the values in the [`Frame`] to be resolved,
#[derive(Copy, Clone, Debug)]
pub struct FrameRef<'a> {
    db: &'a Database,
    frame: &'a Frame,
}

impl std::ops::Deref for FrameRef<'_> {
    type Target = Frame;

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl Frame {
    /// Iterates over the floating hypotheses for this frame.
    pub fn floating(&self) -> impl Iterator<Item = StatementAddress> + '_ {
        self.hypotheses.iter().filter_map(move |hyp| {
            if let Hyp::Floating(sa, _, _) = hyp {
                Some(*sa)
            } else {
                None
            }
        })
    }
}

impl<'a> FrameRef<'a> {
    /// Iterates over the essential hypotheses for this frame.
    pub fn essentials(self) -> impl Iterator<Item = (Label, &'a Formula)> {
        let FrameRef { db, frame } = self;
        frame.hypotheses.iter().filter_map(move |hyp| {
            if let Hyp::Essential(sa, _) = hyp {
                let sref = db.parse_result().statement(*sa);
                let label = db
                    .name_result()
                    .lookup_label(sref.label())
                    .map_or_else(Label::default, |l| l.atom);
                let formula = db.stmt_parse_result().get_formula(&sref)?;
                Some((label, formula))
            } else {
                None
            }
        })
    }

    /// Iterates over the floating hypotheses for this frame.
    pub fn floating(self) -> impl Iterator<Item = Label> + 'a {
        self.frame.floating().map(move |sa| {
            let sref = self.db.parse_result().statement(sa);
            self.db
                .name_result()
                .lookup_label(sref.label())
                .map_or_else(Label::default, |l| l.atom)
        })
    }
}

impl Database {
    /// Returns the frame for the given statement label
    #[must_use]
    pub fn get_frame(&self, label: Label) -> Option<FrameRef<'_>> {
        let token = self.name_result().atom_name(label);
        let frame = self.scope_result().get(token)?;
        Some(frame.as_ref(self))
    }
}

/// Handle to scope results which can fetch frames while tracking dependencies.
#[derive(Debug)]
pub struct ScopeReader<'a> {
    result: &'a ScopeResult,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl<'a> ScopeReader<'a> {
    /// Open a new read handle for a scope result set.
    #[must_use]
    pub fn new(res: &ScopeResult) -> ScopeReader<'_> {
        ScopeReader {
            result: res,
            incremental: res.incremental,
            found: HashSet::default(),
            not_found: HashSet::default(),
        }
    }

    /// Close a read handle, reporting the list of used frames.
    #[must_use]
    #[allow(clippy::missing_const_for_fn)] // clippy#14294
    pub fn into_usage(self) -> ScopeUsage {
        ScopeUsage {
            generation: self.result.generation,
            incremental: self.incremental,
            found: self.found,
            not_found: self.not_found,
        }
    }

    /// Fetch a frame, recording usage for later change tracking.
    pub fn get(&mut self, name: TokenPtr<'_>) -> Option<&'a Frame> {
        let out = self.result.get(name);
        if self.incremental {
            if let Some(frame) = out {
                self.found.insert(frame.label_atom);
            } else {
                self.not_found.insert(name.into());
            }
        }
        out
    }
}

/// Holds a list of frames read during the lifetime of a `ScopeReader`.
#[derive(Debug)]
pub struct ScopeUsage {
    generation: usize,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl ScopeUsage {
    /// Checks if any of the frames used by a `ScopeReader` have potentially
    /// changed since they were read.
    #[must_use]
    pub fn valid(&self, name: &Nameset, res: &ScopeResult) -> bool {
        (self.incremental || res.generation <= self.generation)
            && self
                .found
                .iter()
                .all(|&atom| match res.frame_index.get(name.atom_name(atom)) {
                    None => false,
                    Some(&(gen, _segid, _frix)) => gen <= self.generation,
                })
            && self
                .not_found
                .iter()
                .all(|name| !res.frame_index.contains_key(name))
    }
}
