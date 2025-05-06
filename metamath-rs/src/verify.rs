//! The proof verifier itself.
//!
//! This is structured as an analysis pass, however it does not have any outputs
//! beyond the error indications.  In particular, it does not generate parsed
//! proofs as a side effect; the proof parser will need to be a separate module.
//!
//! The majority of time spent verifying proofs is spent checking steps, which
//! can be regarded as a kind of interpreter.  While checking each step, there
//! is a stack of known results; each step is an operation which pops zero or
//! more results off the stack, does local checks, and pushes a new result.
//! This module has been written such that it does not allocate memory during
//! nominal operation.  Memory is reused from one proof to the next, and
//! intermediate results are handled as slices in a long-lived buffer.
//!
//! Results are densely represented as byte strings, using the high bit to mark
//! the end of each token.  Since most math tokens are shorter than 4 bytes,
//! this saves memory operations over an atom-based approach; but measurements
//! of the actual speed of the atom approach would not be unwelcome.
//!
//! More speculatively, strings could be represented as their universal hash
//! values, using a concatenable universal hash such as polynomial evaluation
//! mod 2^61-1 (a very convenient Mersenne prime).  This would eliminate all
//! branches, and all branch mispredicts, in the memcpy and memcmp parts of this
//! code, at the expense of making scopeck even more useless to other consumers
//! than it is now.

use crate::bit_set::Bitset;
use crate::diag::Diagnostic;
use crate::nameck::{Atom, Nameset};
use crate::scopeck::{
    self, ExprFragment, Frame, Hyp::*, ScopeReader, ScopeResult, ScopeUsage, VerifyExpr,
};
use crate::segment::{Comparer, Segment, SegmentOrder, SegmentRef};
use crate::segment_set::SegmentSet;
use crate::statement::{SegmentId, Span, StatementAddress, TokenPtr, NO_STATEMENT};
use crate::util::{fast_clear, fast_extend, HashMap};
use crate::{parser, Database, StatementRef, StatementType};
use std::mem;
use std::ops::Range;
use std::sync::Arc;

// Proofs are very fragile and there are very few situations where errors are
// recoverable, so we bail out using Result on any error.
macro_rules! try_assert {
    ( $cond:expr , $($arg:tt)+ ) => {
        if !$cond {
            return Err($($arg)+)
        }
    }
}

/// Preparing a step means that it can be referenced using a varint in a
/// compressed proof.  Compressed steps are either saved prior
/// results/hypotheses, which are copied directly onto the stack, or previously
/// proved assertions which require substitution before use.
enum PreparedStep<'a, D> {
    Hyp(Bitset, Atom, Range<usize>, D),
    Assert(&'a Frame),
}
use self::PreparedStep::*;

/// An entry on the stack.
///
/// This is notionally just a string of math symbols, but DV
/// checking is faster if we track disjoint variables as a bit vector, and the
/// typecode is not realignable so it can be profitably separated.
///
/// This type would be Copy except for the fact that the bitset can require
/// overflow storage :(.
#[derive(Clone, Debug)]
pub struct StackSlot {
    vars: Bitset,
    code: Atom,
    expr: Range<usize>,
}

/// A constructor trait for plugging in to the verifier, to collect extra data during the
/// verification pass
pub trait ProofBuilder {
    /// The data type being generated
    type Item: Clone;
    /// The hyp gathering type
    type Accum: Default;

    /// Add a new hyp to the accumulation type
    fn push(&mut self, hyps: &mut Self::Accum, hyp: Self::Item);

    /// Create a proof data node from a statement, the data for the hypotheses,
    /// and the compressed constant string
    fn build(
        &mut self,
        addr: StatementAddress,
        hyps: Self::Accum,
        pool: &[u8],
        expr: Range<usize>,
    ) -> Self::Item;
}

/// The "null" proof builder, which creates no extra data. This
/// is used for one-shot verification, where no extra data beyond the stack
/// information is needed.
impl ProofBuilder for () {
    type Item = ();
    type Accum = ();

    fn push(&mut self, (): &mut (), (): ()) {}

    fn build(&mut self, _: StatementAddress, (): (), _: &[u8], _: Range<usize>) {}
}

/// Working memory used by the verifier on a segment.  This expands for the
/// first few proofs and the rest can be handled without allocation.
struct VerifyState<'a, P: ProofBuilder> {
    /// Segment we are working on
    this_seg: SegmentRef<'a>,
    /// Segment order oracle
    order: &'a SegmentOrder,
    /// Atom name oracle, used for hypotheses
    nameset: &'a Nameset,
    /// Used to access previously proved assertions
    scoper: ScopeReader<'a>,
    /// Used to produce proof trees as a side effect of verification
    builder: &'a mut P,
    /// The extended frame we are working on
    cur_frame: &'a Frame,
    /// Steps which can be invoked in the current proof, grows on every Z
    prepared: Vec<PreparedStep<'a, P::Item>>,
    /// Stack of active subtrees
    stack: Vec<(P::Item, StackSlot)>,
    /// Buffer for math strings of subtrees and hypotheses; shared to reduce
    /// actual copying when a hypothesis or saved step is recalled
    stack_buffer: Vec<u8>,
    /// Scratch space used only when checking the final step
    temp_buffer: Vec<u8>,
    /// Scratch space used for a substitution mapping while invoking a prior
    /// assertion
    subst_info: Vec<(Range<usize>, Bitset)>,
    /// Tracks mandatory and optional variables in use in the current proof
    var2bit: HashMap<Atom, usize>,
    /// Disjoint variable conditions in the current extended frame
    dv_map: &'a [Bitset],
}

type Result<T> = std::result::Result<T, Diagnostic>;

/// Variables are added lazily to the extended frame.  All variables which are
/// associated with hypotheses or $d constraints are numbered by scopeck, but if
/// a dummy variable is used in a proof without a $d constraint it won't be
/// discovered until we get here, and a number needs to be assigned to it.
/// Unfortunately this does mean that it'll be outside the valid range of `dv_map`
/// and `dv_map` checks need to guard against that.
fn map_var<P: ProofBuilder>(state: &mut VerifyState<'_, P>, token: Atom) -> usize {
    let nbit = state.var2bit.len();
    // actually, it _might not_ break anything to have a single variable index
    // allocated by scopeck for all non-$d-ed variables.  after all, they aren't
    // observably disjoint.
    *state.var2bit.entry(token).or_insert(nbit)
}

// the initial hypotheses are accessed directly from the initial extended frame
// to avoid having to look up their pseudo-frames by name; also, $e statements
// no longer have pseudo-frames, so this is the only way to prepare an $e
fn prepare_hypothesis<P: ProofBuilder>(state: &mut VerifyState<'_, P>, hyp: &scopeck::Hyp) {
    let mut vars = Bitset::new();
    let tos = state.stack_buffer.len();
    match *hyp {
        Floating(_addr, var_index, _typecode) => {
            fast_extend(
                &mut state.stack_buffer,
                state.nameset.atom_name(state.cur_frame.var_list[var_index]),
            );
            *state.stack_buffer.last_mut().unwrap() |= 0x80;
            vars.set_bit(var_index); // and we have prior knowledge it's identity mapped
        }
        Essential(_addr, ref expr) => {
            // this is the first of many subtle variations on the "interpret an
            // ExprFragment" theme in this module.
            for part in &*expr.tail {
                fast_extend(
                    &mut state.stack_buffer,
                    &state.cur_frame.const_pool[part.prefix.clone()],
                );
                fast_extend(
                    &mut state.stack_buffer,
                    state.nameset.atom_name(state.cur_frame.var_list[part.var]),
                );
                *state.stack_buffer.last_mut().unwrap() |= 0x80;
                vars.set_bit(part.var); // and we have prior knowledge it's identity mapped
            }
            fast_extend(
                &mut state.stack_buffer,
                &state.cur_frame.const_pool[expr.rump.clone()],
            );
        }
    }

    let n_tos = state.stack_buffer.len();

    state.prepared.push(Hyp(
        vars,
        hyp.typecode(),
        tos..n_tos,
        state.builder.build(
            hyp.address(),
            Default::default(),
            &state.stack_buffer,
            tos..n_tos,
        ),
    ));
}

/// Adds a named $e hypothesis to the prepared array.  These are not kept in the
/// frame array due to infrequent use, so other measures are needed.  This is
/// not normally used by compressed proofs.
///
/// This is used as a fallback when looking up a $e in the assertion hashtable
/// fails.
fn prepare_named_hyp<P: ProofBuilder>(state: &mut VerifyState<'_, P>, label: TokenPtr<'_>) -> bool {
    for hyp in &*state.cur_frame.hypotheses {
        if let Essential(addr, _) = *hyp {
            assert!(addr.segment_id == state.this_seg.id);
            // we don't allow $e statements to be valid across segments, so this
            // can be done as a local lookup in this_seg.  Since we always
            // invalidate the VerifySegment if the current segment has changed
            // in any way, we don't even need to track dependencies here.
            if state.this_seg.statement(addr.index).label() == label {
                prepare_hypothesis(state, hyp);
                return true;
            }
        }
    }

    // Assertion not found, but it might be a local label (checked later)
    false
}

#[derive(Default, Clone, Copy)]
struct StepParse<'a> {
    // The local label for later backreference, or None for not present
    fwdref: Option<TokenPtr<'a>>,
    // The explicit hypothesis reference, or None for not present
    hyptok: Option<TokenPtr<'a>>,
    // The backreference label, or None if it was sucessfully identified as a thm reference
    // and added to the prepared list
    label: Option<TokenPtr<'a>>,
}

/// Used for named step references.  For NORMAL proofs this is immediately
/// before `execute_step`, but for COMPRESSED proofs all used steps are prepared
/// ahead of time, and assigned sequential numbers for later use.
#[allow(clippy::manual_let_else)] // false positive, clippy#10296
fn prepare_step<'a, P: ProofBuilder>(
    state: &mut VerifyState<'_, P>,
    label: TokenPtr<'a>,
    label_span: Option<Span>,
) -> Result<StepParse<'a>> {
    let mut out = StepParse::default();

    // it's either an assertion or a hypothesis.  $f hyps have pseudo-frames
    // which this function can use, $e don't and need to be looked up in the
    // local hyp list after the frame lookup fails
    let frame = if let Some(fp) = state.scoper.get(label) {
        fp
    } else {
        let Some(label_span) = label_span else {
            try_assert!(
                prepare_named_hyp(state, label),
                Diagnostic::StepMissing(label.into())
            );
            return Ok(out);
        };

        // The above handles the "fast path", for normal and compressed proofs.
        // For packed/explicit...
        let (fwdref, hyptok, label) = match (
            label.iter().position(|&x| x == b':'),
            label.iter().position(|&x| x == b'='),
        ) {
            (None, None) => (None, None, label),
            (Some(m), None) => (Some(&label[..m]), None, &label[m + 1..]),
            (None, Some(n)) => (None, Some(&label[..n]), &label[n + 1..]),
            (Some(m), Some(n)) => {
                if m < n {
                    (Some(&label[..m]), Some(&label[m + 1..n]), &label[n + 1..])
                } else {
                    (Some(&label[n + 1..m]), Some(&label[..n]), &label[n + 1..])
                }
            }
        };
        out.fwdref = fwdref;
        out.hyptok = hyptok;
        if let Some(x) = fwdref {
            try_assert!(
                state.scoper.get(x).is_none(),
                Diagnostic::LocalLabelAmbiguous(label_span)
            );
        }
        if let Some(fp) = state.scoper.get(label) {
            fp
        } else {
            if !prepare_named_hyp(state, label) {
                out.label = Some(label);
            }
            return Ok(out);
        }
    };

    // disallow circular reasoning
    let valid = frame.valid;
    let pos = state.cur_frame.valid.start;
    try_assert!(
        state.order.lt(&valid.start, &pos),
        Diagnostic::StepUsedBeforeDefinition(label.into())
    );

    try_assert!(
        valid.end == NO_STATEMENT
            || pos.segment_id == valid.start.segment_id && pos.index < valid.end,
        Diagnostic::StepUsedAfterScope(label.into())
    );

    if frame.stype.is_assertion() {
        state.prepared.push(Assert(frame));
    } else {
        let mut vars = Bitset::new();

        for &var in &*frame.var_list {
            vars.set_bit(map_var(state, var));
        }

        let old_top = state.stack_buffer.len();
        fast_extend(&mut state.stack_buffer, &frame.stub_expr);
        let new_top = state.stack_buffer.len();
        state.prepared.push(Hyp(
            vars,
            frame.target.typecode,
            old_top..new_top,
            state.builder.build(
                valid.start,
                Default::default(),
                &state.stack_buffer,
                old_top..new_top,
            ),
        ));
    }

    Ok(out)
}

// perform a substitution after it has been built in `vars`, appending to
// `target`
#[inline(always)]
fn do_substitute(
    target: &mut Vec<u8>,
    frame: &Frame,
    expr: &VerifyExpr,
    vars: &[(Range<usize>, Bitset)],
) {
    for part in &*expr.tail {
        fast_extend(target, &frame.const_pool[part.prefix.clone()]);
        target.extend_from_within(vars[part.var].0.clone());
    }
    fast_extend(target, &frame.const_pool[expr.rump.clone()]);
}

// like a substitution and equality check, but in one pass
#[inline(always)]
fn do_substitute_eq(
    mut compare: &[u8],
    frame: &Frame,
    expr: &VerifyExpr,
    vars: &[(Range<usize>, Bitset)],
    var_buffer: &[u8],
) -> bool {
    fn step(compare: &mut &[u8], slice: &[u8]) -> bool {
        let len = slice.len();
        if (*compare).len() < len {
            return true;
        }
        if slice != &(*compare)[0..len] {
            return true;
        }
        *compare = &(*compare)[len..];
        false
    }

    for part in &*expr.tail {
        if step(&mut compare, &frame.const_pool[part.prefix.clone()]) {
            return false;
        }
        if step(&mut compare, &var_buffer[vars[part.var].0.clone()]) {
            return false;
        }
    }

    if step(&mut compare, &frame.const_pool[expr.rump.clone()]) {
        return false;
    }

    compare.is_empty()
}

// substitute with the _names_ of variables, for the final "did we prove what we
// claimed we would" check
fn do_substitute_raw(target: &mut Vec<u8>, frame: &Frame, nameset: &Nameset) {
    for part in &*frame.target.tail {
        fast_extend(target, &frame.const_pool[part.prefix.clone()]);
        fast_extend(target, nameset.atom_name(frame.var_list[part.var]));
        *target.last_mut().unwrap() |= 0x80;
    }
    fast_extend(target, &frame.const_pool[frame.target.rump.clone()]);
}

// generate a bitmask for a substituted expression
#[inline(always)]
fn do_substitute_vars(expr: &[ExprFragment], vars: &[(Range<usize>, Bitset)]) -> Bitset {
    let mut out = Bitset::new();
    for part in expr {
        out |= &vars[part.var].1;
    }
    out
}

/// Process the hypotheses of the assertion we're about to apply.  `$f` hyps
/// allow the caller to define a replacement for a variable; `$e` hyps are
/// logical hypotheses that must have been proved; the result is then
/// substituted and pushed.
///
/// Since a variable must be `$f`-declared before it can appear in an `$e` (or
/// else we'll ignore the `$e`), and that logical file order is reflected in
/// the stack order of the hypotheses, we can do this in one pass.
#[inline(always)]
fn process_hyp<P: ProofBuilder>(
    state: &mut VerifyState<'_, P>,
    datavec: &mut P::Accum,
    frame: &Frame,
    ix: usize,
    hyp: &scopeck::Hyp,
) -> Result<()> {
    let (ref data, ref slot): (P::Item, StackSlot) = state.stack[ix];
    state.builder.push(datavec, data.clone());
    match *hyp {
        Floating(_addr, var_index, typecode) => {
            try_assert!(slot.code == typecode, Diagnostic::StepFloatWrongType);
            state.subst_info[var_index] = (slot.expr.clone(), slot.vars.clone());
        }
        Essential(_addr, ref expr) => {
            try_assert!(slot.code == expr.typecode, Diagnostic::StepEssenWrongType);
            try_assert!(
                do_substitute_eq(
                    &state.stack_buffer[slot.expr.clone()],
                    frame,
                    expr,
                    &state.subst_info,
                    &state.stack_buffer
                ),
                Diagnostic::StepEssenWrong
            );
        }
    }
    Ok(())
}

/// This is the main "VM" function, and responsible for ~30% of CPU time during
/// a one-shot verify operation.
#[inline(always)]
fn execute_step<P: ProofBuilder>(
    state: &mut VerifyState<'_, P>,
    index: usize,
    explicit: Option<&mut Vec<Option<TokenPtr<'_>>>>,
) -> Result<()> {
    let fref = match *state
        .prepared
        .get(index)
        .ok_or(Diagnostic::StepOutOfRange)?
    {
        Hyp(ref vars, code, ref expr, ref data) => {
            // hypotheses/saved steps are the easy case.  unfortunately, this is
            // also a very unpredictable branch
            state.stack.push((
                data.clone(),
                StackSlot {
                    vars: vars.clone(),
                    code,
                    expr: expr.clone(),
                },
            ));
            return Ok(());
        }
        Assert(fref) => fref,
    };

    let sbase = state
        .stack
        .len()
        .checked_sub(fref.hypotheses.len())
        .ok_or(Diagnostic::ProofUnderflow)?;

    while state.subst_info.len() < fref.mandatory_count {
        // this is mildly unhygenic, since slots corresponding to $e hyps won't get cleared, but
        // scopeck shouldn't generate references to them
        state.subst_info.push((0..0, Bitset::new()));
    }

    let mut datavec = Default::default();

    // This branch is optimized out of compressed proof processing
    if let Some(explicit_stack) = explicit {
        // The hypotheses are probably in the right order, so check that first
        let mut in_order = true;
        for (ix, hyp) in fref.hypotheses.iter().enumerate() {
            if let Some(tok) = explicit_stack[sbase + ix] {
                if state
                    .nameset
                    .lookup_label(tok)
                    .ok_or_else(|| Diagnostic::BadExplicitLabel(tok.into()))?
                    .address
                    != hyp.address()
                {
                    in_order = false;
                    break;
                }
            }
        }
        if in_order {
            for (ix, hyp) in fref.hypotheses.iter().enumerate() {
                process_hyp(state, &mut datavec, fref, sbase + ix, hyp)?;
            }
        } else {
            // Otherwise, we need to reorder hypotheses

            let mut assn_hyps: Vec<Option<usize>> = vec![None; fref.hypotheses.len()];
            // Assign all explicit hyps
            for (ix, &ex) in explicit_stack[sbase..].iter().enumerate() {
                if let Some(tok) = ex {
                    let addr = state.nameset.lookup_label(tok).unwrap().address;
                    let hyp_ix = (fref
                        .hypotheses
                        .iter()
                        .position(|hyp| hyp.address() == addr)
                        .ok_or_else(|| Diagnostic::BadExplicitLabel(tok.into())))?;
                    try_assert!(
                        assn_hyps[hyp_ix].is_none(),
                        Diagnostic::DuplicateExplicitLabel(tok.into())
                    );
                    assn_hyps[hyp_ix] = Some(ix);
                }
            }
            // assign all the remaining hyps
            for (ix, ex) in explicit_stack[sbase..].iter().enumerate() {
                if ex.is_none() {
                    *assn_hyps.iter_mut().find(|slot| slot.is_none()).unwrap() = Some(ix);
                }
            }

            for (ix, slot) in assn_hyps.iter().enumerate() {
                process_hyp(
                    state,
                    &mut datavec,
                    fref,
                    sbase + ix,
                    &fref.hypotheses[slot.unwrap()],
                )?;
            }
        }

        explicit_stack.truncate(sbase);
    } else {
        for (ix, hyp) in fref.hypotheses.iter().enumerate() {
            process_hyp(state, &mut datavec, fref, sbase + ix, hyp)?;
        }
    }

    // replace the hypotheses on the stack with the substituted target
    // expression.  does not physically remove the hypotheses from the stack
    // pool, because they might have been saved steps or hypotheses, and
    // deciding whether we need to move anything would swamp any savings, anyway
    // - remember that this function is largely a branch predictor benchmark
    let old_top = state.stack_buffer.len();
    do_substitute(
        &mut state.stack_buffer,
        fref,
        &fref.target,
        &state.subst_info,
    );
    let new_top = state.stack_buffer.len();

    state.stack.truncate(sbase);
    state.stack.push((
        state.builder.build(
            fref.valid.start,
            datavec,
            &state.stack_buffer,
            old_top..new_top,
        ),
        StackSlot {
            code: fref.target.typecode,
            vars: do_substitute_vars(&fref.target.tail, &state.subst_info),
            expr: old_top..new_top,
        },
    ));

    // check $d constraints on the used assertion now that the dust has settled.
    // Remember that we might have variable indexes allocated during the proof
    // that are out of range for dv_map
    for &(ix1, ix2) in &*fref.mandatory_dv {
        for var1 in &state.subst_info[ix1].1 {
            for var2 in &state.subst_info[ix2].1 {
                try_assert!(
                    var1 < state.dv_map.len() && state.dv_map[var1].has_bit(var2),
                    Diagnostic::ProofDvViolation
                );
            }
        }
    }

    Ok(())
}

fn finalize_step<P: ProofBuilder>(state: &mut VerifyState<'_, P>) -> Result<P::Item> {
    // if we get here, it's a valid proof, but was it the _right_ valid proof?
    try_assert!(state.stack.len() <= 1, Diagnostic::ProofExcessEnd);
    let (data, tos) = state.stack.last().ok_or(Diagnostic::ProofNoSteps)?;

    try_assert!(
        tos.code == state.cur_frame.target.typecode,
        Diagnostic::ProofWrongTypeEnd
    );

    fast_clear(&mut state.temp_buffer);
    do_substitute_raw(&mut state.temp_buffer, state.cur_frame, state.nameset);

    try_assert!(
        state.stack_buffer[tos.expr.clone()] == state.temp_buffer[..],
        Diagnostic::ProofWrongExprEnd
    );

    Ok(data.clone())
}

fn save_step<P: ProofBuilder>(state: &mut VerifyState<'_, P>) {
    let (data, top) = state
        .stack
        .last()
        .expect("can_save should prevent getting here");
    state.prepared.push(Hyp(
        top.vars.clone(),
        top.code,
        top.expr.clone(),
        data.clone(),
    ));
}

// proofs are not self-synchronizing, so it's not likely to get >1 usable error
fn verify_proof<'a, P: ProofBuilder>(
    state: &mut VerifyState<'a, P>,
    stmt: StatementRef<'a>,
) -> Result<P::Item> {
    // clear, but do not free memory
    state.stack.clear();
    fast_clear(&mut state.stack_buffer);
    state.prepared.clear();
    state.var2bit.clear();
    state.dv_map = &state.cur_frame.optional_dv;
    // temp_buffer is cleared before use; subst_info should be overwritten
    // before use if scopeck is working correctly

    // use scopeck-assigned numbers for mandatory variables and optional
    // variables with active $d constraints.  optional variables without active
    // $d constraints are numbered on demand by map_var
    for (index, &tokr) in state.cur_frame.var_list.iter().enumerate() {
        state.var2bit.insert(tokr, index);
    }

    if stmt.proof_len() > 0 && stmt.proof_slice_at(0) == b"(" {
        // this is a compressed proof
        let mut i = 1;

        // compressed proofs preload the hypotheses so they don't need to (but
        // are not forbidden to) reference them by name
        for hyp in &*state.cur_frame.hypotheses {
            prepare_hypothesis(state, hyp);
        }

        // parse and prepare the label list before the ')'
        loop {
            try_assert!(i < stmt.proof_len(), Diagnostic::ProofUnterminatedRoster);
            let chunk = stmt.proof_slice_at(i);
            i += 1;

            if chunk == b")" {
                break;
            }

            prepare_step(state, chunk, None)?;
        }

        // after ) is a packed list of varints.  decode them and execute the
        // corresponding steps.  the varint decoder is surprisingly CPU-heavy,
        // presumably due to branch overhead
        let mut k = 0usize;
        let mut can_save = false;
        while i < stmt.proof_len() {
            let chunk = stmt.proof_slice_at(i);
            for &ch in chunk {
                if (b'A'..=b'T').contains(&ch) {
                    k = k * 20 + (ch - b'A') as usize;
                    execute_step(state, k, None)?;
                    k = 0;
                    can_save = true;
                } else if (b'U'..=b'Y').contains(&ch) {
                    k = k * 5 + 1 + (ch - b'U') as usize;
                    try_assert!(
                        k < (u32::MAX as usize / 20) - 1,
                        Diagnostic::ProofMalformedVarint
                    );
                    can_save = false;
                } else if ch == b'Z' {
                    try_assert!(can_save, Diagnostic::ProofInvalidSave);
                    save_step(state);
                    can_save = false;
                } else if ch == b'?' {
                    try_assert!(k == 0, Diagnostic::ProofMalformedVarint);
                    return Err(Diagnostic::ProofIncomplete);
                }
            }
            i += 1;
        }

        try_assert!(k == 0, Diagnostic::ProofMalformedVarint);
    } else {
        let mut count = 0;
        let mut backrefs: HashMap<TokenPtr<'_>, usize> = HashMap::default();
        let mut explicit_stack: Option<Vec<Option<TokenPtr<'a>>>> = None;

        // NORMAL mode proofs are just a list of steps, with no saving provision
        for i in 0..stmt.proof_len() {
            let span = stmt.proof_span(i);
            let chunk = stmt.proof_slice_at(i);
            try_assert!(chunk != b"?", Diagnostic::ProofIncomplete);
            let step = prepare_step(state, chunk, Some(span))?;
            if let Some(label) = step.label {
                try_assert!(step.fwdref.is_none(), Diagnostic::ChainBackref(span));
                let &ix = backrefs
                    .get(label)
                    .ok_or_else(|| Diagnostic::StepMissing(label.into()))?;
                execute_step(state, ix, explicit_stack.as_mut())?;
            } else {
                execute_step(state, count, explicit_stack.as_mut())?;
                if let Some(fwdref) = step.fwdref {
                    state.prepared.pop();
                    save_step(state);
                    try_assert!(
                        backrefs.insert(fwdref, count).is_none(),
                        Diagnostic::LocalLabelDuplicate(span)
                    );
                }
                count += 1;
            }
            if step.hyptok.is_some() {
                if explicit_stack.is_none() {
                    // lazy initialization so that we don't need to maintain
                    // this parallel stack if we are not in explicit mode
                    explicit_stack = Some(vec![None; state.stack.len() - 1]);
                }
                explicit_stack.as_mut().unwrap().push(step.hyptok);
            }
        }
    }

    finalize_step(state)
}

/// Stored result of running the verifier on a segment.
#[derive(Debug)]
struct VerifySegment {
    source: Arc<Segment>,
    scope_usage: ScopeUsage,
    diagnostics: HashMap<StatementAddress, Diagnostic>,
}

/// Analysis pass result for the verifier.
#[derive(Default, Clone, Debug)]
pub struct VerifyResult {
    segments: HashMap<SegmentId, Arc<VerifySegment>>,
}

impl VerifyResult {
    /// Report errors found during database verification.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for vsr in self.segments.values() {
            for (&sa, diag) in &vsr.diagnostics {
                out.push((sa, diag.clone()));
            }
        }
        out
    }
}

/// Driver which verifies each statement in a segment.
fn verify_segment(
    sset: &SegmentSet,
    nset: &Nameset,
    scopes: &ScopeResult,
    sid: SegmentId,
) -> VerifySegment {
    let mut diagnostics = HashMap::default();
    let dummy_frame = Frame::default();
    let sref = sset.segment(sid);
    let mut state = VerifyState {
        this_seg: sref,
        scoper: ScopeReader::new(scopes),
        nameset: nset,
        builder: &mut (),
        order: &sset.order,
        cur_frame: &dummy_frame,
        stack: Vec::new(),
        stack_buffer: Vec::new(),
        prepared: Vec::new(),
        temp_buffer: Vec::new(),
        subst_info: Vec::new(),
        var2bit: HashMap::default(),
        dv_map: &dummy_frame.optional_dv,
    };
    // use the _same_ VerifyState so that memory can be reused
    for stmt in sref {
        // only intend to check $p statements
        if stmt.statement_type() == StatementType::Provable {
            // no valid frame -> no use checking
            // may wish to record a secondary error?
            if let Some(frame) = state.scoper.get(stmt.label()) {
                state.cur_frame = frame;
                if let Err(diag) = verify_proof(&mut state, stmt) {
                    diagnostics.insert(stmt.address(), diag);
                }
            }
        }
    }
    VerifySegment {
        source: (*sref).clone(),
        diagnostics,
        scope_usage: state.scoper.into_usage(),
    }
}

/// Calculates or updates the verification result for a database.
pub(crate) fn verify(
    result: &mut VerifyResult,
    segments: &Arc<SegmentSet>,
    nset: &Arc<Nameset>,
    scope: &Arc<ScopeResult>,
) {
    let old = mem::take(&mut result.segments);
    let mut ssrq = Vec::new();
    for sref in segments.segments(..) {
        let segments2 = segments.clone();
        let nset = nset.clone();
        let scope = scope.clone();
        let id = sref.id;
        let old_res_o = old.get(&id).cloned();
        ssrq.push(segments.exec.exec(sref.bytes(), move || {
            let sref = segments2.segment(id);
            if let Some(old_res) = old_res_o {
                if old_res.scope_usage.valid(&nset, &scope) && Arc::ptr_eq(&old_res.source, &sref) {
                    return (id, old_res);
                }
            }
            if segments2.options.trace_recalc {
                println!("verify({:?})", parser::guess_buffer_name(&sref.buffer));
            }
            (id, Arc::new(verify_segment(&segments2, &nset, &scope, id)))
        }))
    }

    result.segments.clear();
    for promise in ssrq {
        let (id, arc) = promise.wait();
        result.segments.insert(id, arc);
    }
}

impl Database {
    /// Parse a single $p statement, returning the result of the given
    /// proof builder, or an error if the proof is faulty
    pub fn verify_one<P: ProofBuilder>(
        &self,
        builder: &mut P,
        stmt: StatementRef<'_>,
    ) -> Result<P::Item> {
        let dummy_frame = Frame::default();
        let mut state = VerifyState {
            this_seg: stmt.segment(),
            scoper: ScopeReader::new(self.scope_result()),
            nameset: self.name_result(),
            builder,
            order: &self.parse_result().order,
            cur_frame: &dummy_frame,
            stack: Vec::new(),
            stack_buffer: Vec::new(),
            prepared: Vec::new(),
            temp_buffer: Vec::new(),
            subst_info: Vec::new(),
            var2bit: HashMap::default(),
            dv_map: &dummy_frame.optional_dv,
        };

        assert!(stmt.statement_type() == StatementType::Provable);
        let frame = state.scoper.get(stmt.label()).unwrap();
        state.cur_frame = frame;
        verify_proof(&mut state, stmt)
    }
}
