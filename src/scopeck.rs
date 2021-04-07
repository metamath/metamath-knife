//! This module calculates 3 things which are related only by the fact that they
//! can be done at the same time:
//!
//! 1. For `$c $v $f` and labelled statements (`$e $f $a $p`): Check for
//! duplication
//!
//! 1. For `$e $d $f $a $p`: Check that all used math symbols are active in
//! scope
//!
//! 1. For `$a $p`: Compute the frame
//!
//! Rules of precedence for error detection and recovery:
//!
//! 1. Math symbols and labels are actually in separate namespaces.  We warn
//! about collisions but otherwise do nothing.  Variables have responsibility
//! for the warning.
//!
//! 1. When two definitions have overlapping live ranges, the earlier one wins.
//!
//! 1. Constant/nested variable collisions are special because they don't
//! involve scope overlaps. The constant wins, the variable must notify.
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
use crate::nameck::Atom;
use crate::nameck::NameReader;
use crate::nameck::Nameset;
use crate::nameck::NameUsage;
use crate::parser;
use crate::parser::Comparer;
use crate::parser::copy_token;
use crate::parser::GlobalRange;
use crate::parser::NO_STATEMENT;
use crate::parser::Segment;
use crate::parser::SegmentId;
use crate::parser::SegmentOrder;
use crate::parser::SegmentRef;
use crate::parser::StatementAddress;
use crate::parser::StatementIndex;
use crate::parser::StatementRef;
use crate::parser::StatementType;
use crate::parser::SymbolType;
use crate::parser::Token;
use crate::parser::TokenAddress;
use crate::parser::TokenPtr;
use crate::parser::TokenRef;
use crate::segment_set::SegmentSet;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::ops::Range;
use std::sync::Arc;
use crate::util::fast_extend;
use crate::util::HashMap;
use crate::util::HashSet;
use crate::util::new_map;
use crate::util::new_set;
use crate::util::ptr_eq;

/// Information on a `$v` active in the local or global scope.
#[derive(Clone,Copy)]
struct LocalVarInfo {
    /// Definition location
    start: TokenAddress,
    /// Exclusive end of the valid range
    end: StatementIndex,
    /// Atom for the variable name
    atom: Atom,
}

/// Information on a `$f` active in scope
#[derive(Copy,Clone,Debug,Default)]
struct LocalFloatInfo {
    valid: GlobalRange,
    typecode: Atom,
}

/// Information on a math symbol which has been determined to be valid in the
/// current scope
#[derive(Copy,Clone,Debug)]
enum CheckedToken<'a> {
    Const(TokenPtr<'a>, Atom),
    Var(TokenPtr<'a>, Atom, LocalFloatInfo),
}
use self::CheckedToken::*;

/// Information on a `$d` statement active in the local scope
#[derive(Clone,Debug)]
struct LocalDvInfo {
    valid: GlobalRange,
    vars: Vec<Atom>,
}

#[derive(Clone,Debug)]
struct LocalEssentialInfo<'a> {
    valid: GlobalRange,
    label: TokenPtr<'a>,
    string: Vec<CheckedToken<'a>>,
}

/// Semantic type for renamed variables.
///
/// Within each frame, variable names are replaced with small integers.
pub type VarIndex = usize;

/// A literal-variable pair, used in the frame expressions.
#[derive(Clone,Debug)]
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
#[derive(Clone,Debug)]
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

impl Default for VerifyExpr {
    fn default() -> VerifyExpr {
        VerifyExpr {
            typecode: Atom::default(),
            rump: 0..0,
            tail: Box::default(),
        }
    }
}

/// Representation of a hypothesis in a frame program.
#[derive(Clone,Debug)]
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
    pub fn address(&self) -> StatementAddress {
        match *self {
            Hyp::Essential(addr, _) => addr,
            Hyp::Floating(addr, _, _) => addr,
        }
    }

    /// Returns the typecode expected on the stack for this hypothesis.
    pub fn typecode(&self) -> Atom {
        match self {
            &Hyp::Essential(_, ref expr) => expr.typecode,
            &Hyp::Floating(_, _, typecode) => typecode,
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
#[derive(Clone,Debug,Default)]
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

fn push_diagnostic(state: &mut ScopeState, ix: StatementIndex, diag: Diagnostic) {
    state.diagnostics.entry(ix).or_insert(Vec::new()).push(diag);
}

/// Verifies that this is the true (first) use of a label.  The returned atom
/// will be meaningful only in incremental mode, but the `is_some` state is
/// always usable.
fn check_label_dup(state: &mut ScopeState, sref: StatementRef) -> Option<Atom> {
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
fn check_math_symbol(state: &mut ScopeState,
                     sref: StatementRef,
                     tref: TokenRef)
                     -> Option<(SymbolType, Atom)> {
    // active global definition?
    if let Some(sdef) = state.gnames.lookup_symbol(&tref) {
        if state.order.cmp(&sdef.address, &tref.address) == Ordering::Less {
            return Some((sdef.stype, sdef.atom));
        }
    }

    // active local definition?
    if let Some(local_slot) = state.local_vars.get(tref.slice).and_then(|slot| slot.last()) {
        if check_endpoint(sref.index(), local_slot.end) {
            return Some((SymbolType::Variable, local_slot.atom));
        }
    }

    push_diagnostic(state,
                    sref.index(),
                    Diagnostic::NotActiveSymbol(tref.index()));
    None
}

/// Find the active typecode for a variable.
fn lookup_float<'a>(state: &mut ScopeState<'a>,
                    sref: StatementRef<'a>,
                    tref: TokenRef<'a>)
                    -> Option<LocalFloatInfo> {
    // active global definition?
    if let Some(fdef) = state.gnames.lookup_float(&tref) {
        if state.order.cmp(&fdef.address, &sref.address()) == Ordering::Less {
            return Some(LocalFloatInfo {
                valid: fdef.address.unbounded_range(),
                typecode: fdef.typecode_atom,
            });
        }
    }

    // active local definition?
    if let Some(&local_slot) = state.local_floats.get(tref.slice).and_then(|slot| slot.last()) {
        if check_endpoint(sref.index(), local_slot.valid.end) {
            return Some(local_slot);
        }
    }

    None
}

/// Given a math string, verify that all tokens are active, all variables have
/// typecodes, and the head is a constant.
fn check_eap<'a>(state: &mut ScopeState<'a>,
                 sref: StatementRef<'a>)
                 -> Option<Vec<CheckedToken<'a>>> {
    let mut bad = false;
    let mut out = Vec::with_capacity(sref.math_len() as usize);

    for tref in sref.math_iter() {
        match check_math_symbol(state, sref, tref) {
            None => bad = true,
            Some((SymbolType::Constant, atom)) => {
                out.push(Const(tref.slice, atom));
            }
            Some((SymbolType::Variable, atom)) => {
                if tref.index() == 0 {
                    push_diagnostic(state, sref.index(), Diagnostic::ExprNotConstantPrefix(0));
                    bad = true;
                } else {
                    match lookup_float(state, sref, tref) {
                        None => {
                            push_diagnostic(state,
                                            sref.index(),
                                            Diagnostic::VariableMissingFloat(tref.index()));
                            bad = true;
                        }
                        Some(lfi) => out.push(Var(tref.slice, atom, lfi)),
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
fn construct_stub_frame(state: &mut ScopeState,
                        sref: StatementRef,
                        latom: Atom,
                        expr: &[CheckedToken]) {
    let mut iter = expr.iter();
    let typecode = match iter.next().expect("parser checks $eap token count") {
        &Const(_, typecode) => typecode,
        _ => unreachable!(),
    };
    let mut mvars = Vec::new();
    let mut conststr = Vec::new();

    for &ctok in iter {
        match ctok {
            Const(tref, _) => {
                conststr.extend_from_slice(tref);
                *conststr.last_mut().unwrap() |= 0x80;
            }
            Var(tref, atom, _) => {
                conststr.extend_from_slice(tref);
                *conststr.last_mut().unwrap() |= 0x80;
                mvars.push(atom);
            }
        }
    }

    state.frames_out.push(Frame {
        stype: sref.statement_type(),
        label_atom: latom,
        valid: sref.scope_range(),
        hypotheses: Box::default(),
        target: VerifyExpr {
            typecode: typecode,
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
/// This is not part of ScopeState due to incompatible borrowing constraints.
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
fn scan_expression(iframe: &mut InchoateFrame, expr: &[CheckedToken]) -> VerifyExpr {
    let mut iter = expr.iter();
    let head = match iter.next().expect("parser checks $eap token count") {
        &Const(_, head) => head,
        _ => unreachable!(),
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
                let index = iframe.variables.get(&atom).map(|&(x, _)| x).unwrap_or_else(|| {
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
        typecode: head.to_owned(),
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
        let index = match iframe.variables.get(&varatom).map(|&(x, _)| x) {
            Some(mvarindex) => mvarindex,
            None => {
                // it's not a mandatory variable and so we don't need $f info,
                // but it still needs to be indexed.
                let index = iframe.variables.len();
                iframe.var_list.push(varatom);
                iframe.optional_dv.push(Bitset::new());
                iframe.variables.insert(varatom, (index, Default::default()));
                index
            }
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
fn construct_full_frame<'a>(state: &mut ScopeState<'a>,
                            sref: StatementRef<'a>,
                            label_atom: Atom,
                            expr: &[CheckedToken<'a>]) {
    state.local_essen.retain(|hyp| check_endpoint(sref.index(), hyp.valid.end));
    state.local_dv.retain(|hyp| check_endpoint(sref.index(), hyp.valid.end));
    // local_essen and local_dv now contain only things still in scope

    // collect mandatory variables
    let mut iframe = InchoateFrame {
        variables: new_map(),
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

    for &(_, ref vars) in state.gnames.lookup_global_dv() {
        scan_dv(&mut iframe, &vars)
    }

    for dv in &state.local_dv {
        scan_dv(&mut iframe, &dv.vars);
    }

    state.frames_out.push(Frame {
        stype: sref.statement_type(),
        label_atom: label_atom,
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

fn scope_check_constant(state: &mut ScopeState, sref: StatementRef) {
    if sref.in_group() {
        // nested $c are ignored by smetamath3, the parser generates a
        // diagnostic

        // assert!(sref.statement.diagnostics.len() > 0);
        return;
    }

    for tref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(&tref) {
            push_diagnostic(state,
                            sref.index(),
                            Diagnostic::SymbolDuplicatesLabel(tref.index(), ldef.address));
        }

        if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
            if cdef.address != tref.address {
                push_diagnostic(state,
                                sref.index(),
                                Diagnostic::SymbolRedeclared(tref.index(), cdef.address));
            }
        }
    }
}

fn scope_check_dv<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut used = new_map();
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
                    push_diagnostic(state,
                                    sref.index(),
                                    Diagnostic::DjRepeatedVariable(tref.index(), previx));
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
            vars: vars,
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
                label: sref.label(),
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

    let latom = match check_label_dup(state, sref) {
        None => return,
        Some(a) => a,
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
        push_diagnostic(state,
                        sref.index(),
                        Diagnostic::FloatRedeclared(prev.valid.start));
        return;
    }

    // record the $f; global $f are tracked by nameck but must still be verified
    // here
    if sref.in_group() {
        state.local_floats
            .entry(copy_token(&var_tok))
            .or_insert(Vec::new())
            .push(LocalFloatInfo {
                typecode: const_at,
                valid: sref.scope_range(),
            });
    }

    let expr = [Const(&const_tok, const_at), Var(&var_tok, var_at, LocalFloatInfo::default())];
    construct_stub_frame(state, sref, latom, &expr);
}

fn check_endpoint(cur: StatementIndex, end: StatementIndex) -> bool {
    end == NO_STATEMENT || cur < end
}

// factored out to make a useful borrow scope
fn maybe_add_local_var(state: &mut ScopeState,
                       sref: StatementRef,
                       tref: TokenRef)
                       -> Option<TokenAddress> {
    let lv_slot = state.local_vars.entry(copy_token(&tref)).or_insert(Vec::new());

    if let Some(lv_most_recent) = lv_slot.last() {
        if check_endpoint(sref.index(), lv_most_recent.end) {
            return Some(lv_most_recent.start);
        }
    }

    lv_slot.push(LocalVarInfo {
        start: tref.address,
        end: sref.scope_range().end,
        atom: state.nameset.get_atom(&tref),
    });
    None
}

fn scope_check_variable(state: &mut ScopeState, sref: StatementRef) {
    for tref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(&tref) {
            push_diagnostic(state,
                            sref.index(),
                            Diagnostic::SymbolDuplicatesLabel(tref.index(), ldef.address));
        }

        if !sref.in_group() {
            // top level $v, may conflict with a prior $c
            if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
                if cdef.address != tref.address {
                    push_diagnostic(state,
                                    sref.index(),
                                    Diagnostic::SymbolRedeclared(tref.index(), cdef.address));
                }
            }
        } else {
            // nested $v, may conflict with an outer scope $v, top level $v/$c,
            // or a _later_ $c
            if let Some(cdef) = state.gnames.lookup_symbol(&tref) {
                if state.order.cmp(&cdef.address, &tref.address) == Ordering::Less {
                    push_diagnostic(state,
                                    sref.index(),
                                    Diagnostic::SymbolRedeclared(tref.index(), cdef.address));
                    continue;
                } else if cdef.stype == SymbolType::Constant {
                    push_diagnostic(state,
                                    sref.index(),
                                    Diagnostic::VariableRedeclaredAsConstant(tref.index(),
                                                                             cdef.address));
                    continue;
                }
            }

            // recorded in local state here
            if let Some(prev_addr) = maybe_add_local_var(state, sref, tref) {
                // local/local conflict
                push_diagnostic(state,
                                sref.index(),
                                Diagnostic::SymbolRedeclared(tref.index(), prev_addr));
            }
        }
    }
}

/// Data generated by the scope checking process for a segment.
struct SegmentScopeResult {
    id: SegmentId,
    source: Arc<Segment>,
    name_usage: NameUsage,
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    frames_out: Vec<Frame>,
}

/// Runs scope checking for a single segment.
fn scope_check_single(sset: &SegmentSet, names: &Nameset, seg: SegmentRef) -> SegmentScopeResult {
    let mut state = ScopeState {
        diagnostics: new_map(),
        order: &sset.order,
        nameset: names,
        gnames: NameReader::new(names),
        local_vars: new_map(),
        local_floats: new_map(),
        local_dv: Vec::new(),
        local_essen: Vec::new(),
        frames_out: Vec::new(),
    };

    for sref in seg {
        match sref.statement_type() {
            StatementType::Axiom => scope_check_assert(&mut state, sref),
            StatementType::Constant => scope_check_constant(&mut state, sref),
            StatementType::Disjoint => scope_check_dv(&mut state, sref),
            StatementType::Essential => scope_check_essential(&mut state, sref),
            StatementType::Floating => scope_check_float(&mut state, sref),
            StatementType::Provable => scope_check_assert(&mut state, sref),
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
#[derive(Default, Clone)]
pub struct ScopeResult {
    incremental: bool,
    generation: usize,
    segments: Vec<Option<Arc<SegmentScopeResult>>>,
    frame_index: HashMap<Token, (usize, usize, usize)>,
}

impl ScopeResult {
    /// Returns a list of errors that were generated during the scope
    /// computation.
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sid, ssro) in self.segments.iter().enumerate() {
            if let &Some(ref ssr) = ssro {
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
    pub fn get(&self, name: TokenPtr) -> Option<&Frame> {
        self.frame_index
            .get(name)
            .map(|&(_gen, segid, frix)| &self.segments[segid].as_ref().unwrap().frames_out[frix])
    }
}

/// Extracts scope data for a database.
///
/// Use `ScopeResult::default()` to get an initial state.
pub fn scope_check(result: &mut ScopeResult, segments: &Arc<SegmentSet>, names: &Arc<Nameset>) {
    result.incremental |= result.frame_index.is_empty();
    result.incremental &= segments.options.incremental;
    result.generation += 1;
    let gen = result.generation;
    let mut ssrq = VecDeque::new();
    // process all segments in parallel to get new scope results or identify
    // reusable ones
    {
        let mut prev = new_map();
        for (sid, &ref ssr) in result.segments.iter().enumerate() {
            prev.insert(SegmentId(sid as u32), ssr.clone());
        }
        for sref in segments.segments() {
            let segments2 = segments.clone();
            let names = names.clone();
            let id = sref.id;
            let osr = prev.get(&id).and_then(|x| x.clone());
            ssrq.push_back(segments.exec.exec(sref.bytes(), move || {
                let sref = segments2.segment(id);
                if let Some(old_res) = osr {
                    if old_res.name_usage.valid(&names) &&
                       ptr_eq::<Segment>(&old_res.source, &sref) {
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
    let mut stale_ids = new_set();
    let mut to_add = Vec::new();

    for (sid, res) in result.segments.iter().enumerate() {
        if res.is_some() {
            stale_ids.insert(SegmentId(sid as u32));
        }
    }

    for sref in segments.segments() {
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
            result.frame_index.remove(label).expect("check_label_dup should prevent this");
        }
    }

    for res_new in to_add {
        let seg_index = res_new.id.0 as usize;
        if seg_index >= result.segments.len() {
            result.segments.resize(seg_index + 1, None);
        }

        let sref = segments.segment(res_new.id);
        for (index, frame) in res_new.frames_out.iter().enumerate() {
            let label = copy_token(sref.statement(frame.valid.start.index).label());
            let old = result.frame_index.insert(label, (gen, seg_index, index));
            assert!(old.is_none(), "check_label_dup should prevent this");
        }

        result.segments[seg_index] = Some(res_new);
    }
}

/// Handle to scope results which can fetch frames while tracking dependencies.
pub struct ScopeReader<'a> {
    result: &'a ScopeResult,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl<'a> ScopeReader<'a> {
    /// Open a new read handle for a scope result set.
    pub fn new(res: &ScopeResult) -> ScopeReader {
        ScopeReader {
            result: res,
            incremental: res.incremental,
            found: new_set(),
            not_found: new_set(),
        }
    }

    /// Close a read handle, reporting the list of used frames.
    pub fn into_usage(self) -> ScopeUsage {
        ScopeUsage {
            generation: self.result.generation,
            incremental: self.incremental,
            found: self.found,
            not_found: self.not_found,
        }
    }

    /// Fetch a frame, recording usage for later change tracking.
    pub fn get(&mut self, name: TokenPtr) -> Option<&'a Frame> {
        let out = self.result.get(name);
        if self.incremental {
            if let Some(frame) = out {
                self.found.insert(frame.label_atom);
            } else {
                self.not_found.insert(copy_token(name));
            }
        }
        out
    }
}

/// Holds a list of frames read during the lifetime of a `ScopeReader`.
pub struct ScopeUsage {
    generation: usize,
    incremental: bool,
    found: HashSet<Atom>,
    not_found: HashSet<Token>,
}

impl ScopeUsage {
    /// Checks if any of the frames used by a `ScopeReader` have potentially
    /// changed since they were read.
    pub fn valid(&self, name: &Nameset, res: &ScopeResult) -> bool {
        (self.incremental || res.generation <= self.generation) &&
        self.found.iter().all(|&atom| match res.frame_index.get(name.atom_name(atom)) {
            None => false,
            Some(&(gen, _segid, _frix)) => gen <= self.generation,
        }) && self.not_found.iter().all(|name| !res.frame_index.contains_key(name))
    }
}
