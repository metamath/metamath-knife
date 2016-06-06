use bit_set::Bitset;
use diag::Diagnostic;
use nameck::Atom;
use nameck::Nameset;
use parser::Comparer;
use parser::NO_STATEMENT;
use parser::SegmentId;
use parser::SegmentOrder;
use parser::StatementAddress;
use parser::StatementRef;
use parser::StatementType;
use parser::TokenPtr;
use scopeck::ExprFragment;
use scopeck::Frame;
use scopeck::ScopeReader;
use scopeck::ScopeResult;
use segment_set::SegmentSet;
use std::cmp::Ordering;
use std::ops::Range;
use std::sync::Arc;
use std::u32;
use std::usize;
use util::fast_clear;
use util::fast_extend;
use util::fast_truncate;
use util::HashMap;
use util::new_map;

enum PreparedStep<'a> {
    Hyp(Bitset, Atom, Range<usize>),
    Assert(&'a Frame),
}

struct StackSlot {
    vars: Bitset,
    code: Atom,
    expr: Range<usize>,
}

struct VerifyState<'a> {
    order: &'a SegmentOrder,
    nameset: &'a Nameset,
    scoper: ScopeReader<'a>,
    cur_frame: &'a Frame,
    prepared: Vec<PreparedStep<'a>>,
    prep_buffer: Vec<u8>,
    stack: Vec<StackSlot>,
    stack_buffer: Vec<u8>,
    temp_buffer: Vec<u8>,
    subst_info: Vec<(Range<usize>, Bitset)>,
    var2bit: HashMap<Atom, usize>,
    dv_map: &'a [Bitset],
}

fn map_var<'a>(state: &mut VerifyState<'a>, token: Atom) -> usize {
    let nbit = state.var2bit.len();
    *state.var2bit.entry(token).or_insert(nbit)
}

// the initial hypotheses are accessed directly to avoid having to look up their names
fn prepare_hypotheses(state: &mut VerifyState) {
    for hyp in &state.cur_frame.hypotheses {
        let mut vars = Bitset::new();
        let tos = state.prep_buffer.len();

        for part in &hyp.expr.tail {
            match *part {
                ExprFragment::Var(ix) => {
                    fast_extend(&mut state.prep_buffer, state.nameset.atom_name(state.cur_frame.var_list[ix]));
                    vars.set_bit(ix); // and we have prior knowledge it's identity mapped
                    state.prep_buffer.push(b' ');
                }
                ExprFragment::Constant(ref string) => {
                    fast_extend(&mut state.prep_buffer,
                                &state.cur_frame.const_pool[string.clone()]);
                }
            }
        }

        let ntos = state.prep_buffer.len();
        state.prepared.push(PreparedStep::Hyp(vars, hyp.expr.typecode, tos..ntos));
    }
}

fn prepare_step(state: &mut VerifyState, label: TokenPtr) -> Option<Diagnostic> {
    let frame = match state.scoper.get(label) {
        Some(fp) => fp,
        None => return Some(Diagnostic::StepMissing(label.to_owned())),
    };

    let valid = frame.valid;
    let pos = state.cur_frame.valid.start;
    if state.order.cmp(&pos, &valid.start) != Ordering::Greater {
        return Some(Diagnostic::StepUsedBeforeDefinition(label.to_owned()));
    }

    if valid.end != NO_STATEMENT {
        if pos.segment_id != valid.start.segment_id || pos.index >= valid.end {
            return Some(Diagnostic::StepUsedAfterScope(label.to_owned()));
        }
    }

    if frame.stype == StatementType::Axiom || frame.stype == StatementType::Provable {
        state.prepared.push(PreparedStep::Assert(frame));
    } else {
        let mut vars = Bitset::new();

        for &var in &frame.var_list {
            vars.set_bit(map_var(state, var));
        }

        let tos = state.prep_buffer.len();
        fast_extend(&mut state.prep_buffer, &frame.stub_expr);
        let ntos = state.prep_buffer.len();
        state.prepared
            .push(PreparedStep::Hyp(vars, frame.target.typecode, tos..ntos));
    }

    return None;
}

fn do_substitute(target: &mut Vec<u8>,
                 frame: &Frame,
                 expr: &[ExprFragment],
                 vars: &[(Range<usize>, Bitset)],
                 var_buffer: &[u8]) {
    for part in expr {
        match *part {
            ExprFragment::Var(ix) => {
                fast_extend(target, &var_buffer[vars[ix].0.clone()]);
            }
            ExprFragment::Constant(ref string) => {
                fast_extend(target, &frame.const_pool[string.clone()]);
            }
        }
    }
}

fn do_substitute_raw(target: &mut Vec<u8>, frame: &Frame, nameset: &Nameset) {
    for part in &frame.target.tail {
        match *part {
            ExprFragment::Var(ix) => {
                fast_extend(target, nameset.atom_name(frame.var_list[ix]));
                target.push(b' ');
            }
            ExprFragment::Constant(ref string) => {
                fast_extend(target, &frame.const_pool[string.clone()]);
            }
        }
    }
}

fn do_substitute_vars(expr: &[ExprFragment], vars: &[(Range<usize>, Bitset)]) -> Bitset {
    let mut out = Bitset::new();
    for part in expr {
        match *part {
            ExprFragment::Var(ix) => out |= &vars[ix].1,
            ExprFragment::Constant(_) => {}
        }
    }
    out
}

fn execute_step(state: &mut VerifyState, index: usize) -> Option<Diagnostic> {
    if index >= state.prepared.len() {
        return Some(Diagnostic::StepOutOfRange);
    }

    let fref = match state.prepared[index] {
        PreparedStep::Hyp(ref vars, code, ref expr) => {
            let tos = state.stack_buffer.len();
            fast_extend(&mut state.stack_buffer, &state.prep_buffer[expr.clone()]);
            let ntos = state.stack_buffer.len();
            state.stack.push(StackSlot {
                vars: vars.clone(),
                code: code,
                expr: tos..ntos,
            });
            return None;
        }
        PreparedStep::Assert(fref) => fref,
    };

    if state.stack.len() < fref.hypotheses.len() {
        return Some(Diagnostic::ProofUnderflow);
    }
    let sbase = state.stack.len() - fref.hypotheses.len();

    state.subst_info.clear();
    state.subst_info.resize(fref.mandatory_count, (0..0, Bitset::new()));

    // check $f, build substitution
    for (ix, hyp) in fref.hypotheses.iter().enumerate() {
        if hyp.is_float {
            let slot = &state.stack[sbase + ix];
            if slot.code != hyp.expr.typecode {
                return Some(Diagnostic::StepFloatWrongType);
            }
            state.subst_info[hyp.variable_index] = (slot.expr.clone(), slot.vars.clone());
        }
    }

    // check $e
    for (ix, hyp) in fref.hypotheses.iter().enumerate() {
        if !hyp.is_float {
            let slot = &state.stack[sbase + ix];
            if slot.code != hyp.expr.typecode {
                return Some(Diagnostic::StepEssenWrongType);
            }
            fast_clear(&mut state.temp_buffer);
            do_substitute(&mut state.temp_buffer,
                          fref,
                          &hyp.expr.tail,
                          &state.subst_info,
                          &state.stack_buffer);
            if state.stack_buffer[slot.expr.clone()] != state.temp_buffer[..] {
                return Some(Diagnostic::StepEssenWrong);
            }
        }
    }

    fast_clear(&mut state.temp_buffer);
    do_substitute(&mut state.temp_buffer,
                  fref,
                  &fref.target.tail,
                  &state.subst_info,
                  &state.stack_buffer);

    state.stack.truncate(sbase);
    fast_truncate(&mut state.stack_buffer,
                  if sbase == 0 {
                      0
                  } else {
                      state.stack[sbase - 1].expr.end
                  });
    let tos = state.stack_buffer.len();
    fast_extend(&mut state.stack_buffer, &state.temp_buffer);
    let ntos = state.stack_buffer.len();

    state.stack.push(StackSlot {
        code: fref.target.typecode,
        vars: do_substitute_vars(&fref.target.tail, &state.subst_info),
        expr: tos..ntos,
    });

    // check $d
    for &(ix1, ix2) in &fref.mandatory_dv {
        for var1 in &state.subst_info[ix1].1 {
            for var2 in &state.subst_info[ix2].1 {
                if var1 >= state.dv_map.len() || !state.dv_map[var1].has_bit(var2) {
                    return Some(Diagnostic::ProofDvViolation);
                }
            }
        }
    }

    return None;
}

fn finalize_step(state: &mut VerifyState) -> Option<Diagnostic> {
    if state.stack.len() == 0 {
        return Some(Diagnostic::ProofNoSteps);
    }
    if state.stack.len() > 1 {
        return Some(Diagnostic::ProofExcessEnd);
    }
    let tos = state.stack.last().unwrap();

    if tos.code != state.cur_frame.target.typecode {
        return Some(Diagnostic::ProofWrongTypeEnd);
    }

    fast_clear(&mut state.temp_buffer);
    do_substitute_raw(&mut state.temp_buffer, &state.cur_frame, state.nameset);

    if state.stack_buffer[tos.expr.clone()] != state.temp_buffer[..] {
        return Some(Diagnostic::ProofWrongExprEnd);
    }

    None
}

fn save_step(state: &mut VerifyState) {
    let top = state.stack.last().expect("can_save should prevent getting here");
    let tos = state.prep_buffer.len();
    fast_extend(&mut state.prep_buffer,
                &state.stack_buffer[top.expr.clone()]);
    let ntos = state.prep_buffer.len();
    state.prepared.push(PreparedStep::Hyp(top.vars.clone(), top.code, tos..ntos));
}

// proofs are not self-synchronizing, so it's not likely to get >1 usable error
fn verify_proof<'a>(statepp: &mut Option<VerifyState<'a>>,
                    sset: &'a SegmentSet,
                    nset: &'a Nameset,
                    scopes: ScopeReader<'a>,
                    stmt: StatementRef<'a>)
                    -> Option<Diagnostic> {
    // only intend to check $p statements
    if stmt.statement.stype != StatementType::Provable {
        return None;
    }

    // no valid frame -> no use checking
    // may wish to record a secondary error?
    let cur_frame = match scopes.get(stmt.label()) {
        None => return None,
        Some(x) => x,
    };

    if statepp.is_none() {
        *statepp = Some(VerifyState {
            scoper: scopes,
            nameset: nset,
            order: &sset.order,
            cur_frame: cur_frame,
            stack: Vec::new(),
            stack_buffer: Vec::new(),
            prepared: Vec::new(),
            prep_buffer: Vec::new(),
            temp_buffer: Vec::new(),
            subst_info: Vec::new(),
            var2bit: new_map(),
            dv_map: &cur_frame.optional_dv,
        });
    }
    let state = statepp.as_mut().unwrap();
    state.cur_frame = cur_frame;
    state.stack.clear();
    fast_clear(&mut state.stack_buffer);
    state.prepared.clear();
    fast_clear(&mut state.prep_buffer);
    state.var2bit.clear();
    state.dv_map = &cur_frame.optional_dv;
    // temp_buffer and subst_info are cleared before use

    for (index, &tokr) in cur_frame.var_list.iter().enumerate() {
        state.var2bit.insert(tokr, index);
    }

    if stmt.proof_slice_at(0) == b"(" {
        let mut i = 1;

        prepare_hypotheses(state);

        loop {
            if i >= stmt.proof_len() {
                return Some(Diagnostic::ProofUnterminatedRoster);
            }
            let chunk = stmt.proof_slice_at(i);
            i += 1;

            if chunk == b")" {
                break;
            }

            if let Some(err) = prepare_step(state, chunk) {
                return Some(err);
            }
        }

        let mut k = 0usize;
        let mut can_save = false;
        while i < stmt.proof_len() {
            let chunk = stmt.proof_slice_at(i);
            for &ch in chunk {
                if ch >= b'A' && ch <= b'T' {
                    k = k * 20 + (ch - b'A') as usize;
                    if let Some(err) = execute_step(state, k) {
                        return Some(err);
                    }
                    k = 0;
                    can_save = true;
                } else if ch >= b'U' && ch <= b'Y' {
                    k = k * 5 + 1 + (ch - b'U') as usize;
                    if k >= (u32::max_value() as usize / 20) - 1 {
                        return Some(Diagnostic::ProofMalformedVarint);
                    }
                    can_save = false;
                } else if ch == b'Z' {
                    if !can_save {
                        return Some(Diagnostic::ProofInvalidSave);
                    }
                    save_step(state);
                    can_save = false;
                } else if ch == b'?' {
                    if k > 0 {
                        return Some(Diagnostic::ProofMalformedVarint);
                    }
                    return Some(Diagnostic::ProofIncomplete);
                }
            }
            i += 1;
        }

        if k > 0 {
            return Some(Diagnostic::ProofMalformedVarint);
        }
    } else {
        let mut count = 0;
        for i in 0..stmt.proof_len() {
            let chunk = stmt.proof_slice_at(i);
            if chunk == b"?" {
                return Some(Diagnostic::ProofIncomplete);
            } else {
                if let Some(err) = prepare_step(state, chunk) {
                    return Some(err);
                }
                if let Some(err) = execute_step(state, count) {
                    return Some(err);
                }
                count += 1;
            }
        }
    }

    if let Some(err) = finalize_step(state) {
        return Some(err);
    }

    return None;
}

struct VerifySegment {
    diagnostics: HashMap<StatementAddress, Diagnostic>,
}

pub struct VerifyResult {
    segments: HashMap<SegmentId, Arc<VerifySegment>>,
}

impl VerifyResult {
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for vsr in self.segments.values() {
            for (&sa, &ref diag) in &vsr.diagnostics {
                out.push((sa, diag.clone()));
            }
        }
        out
    }
}

fn verify_segment(sset: &SegmentSet, nset: &Nameset, scopes: &ScopeResult, sid: SegmentId) -> VerifySegment {
    let reader = ScopeReader::new(scopes);
    let mut out = VerifySegment { diagnostics: new_map() };
    let mut state = None;
    for stmt in sset.segment(sid).statement_iter() {
        if let Some(diag) = verify_proof(&mut state, sset, nset, reader, stmt) {
            out.diagnostics.insert(stmt.address(), diag);
        }
    }
    out
}

pub fn verify(segments: &SegmentSet, nset: &Nameset, scope: &ScopeResult) -> VerifyResult {
    let mut out = VerifyResult { segments: new_map() };
    for sref in segments.segments() {
        out.segments.insert(sref.id, Arc::new(verify_segment(segments, nset, scope, sref.id)));
    }
    out
}
