use bit_set::Bitset;
use diag::Diagnostic;
use nameck::NameReader;
use nameck::Nameset;
use parser::Comparer;
use parser::GlobalRange;
use parser::NO_STATEMENT;
use parser::SegmentId;
use parser::SegmentOrder;
use parser::SegmentRef;
use parser::StatementAddress;
use parser::StatementIndex;
use parser::StatementRef;
use parser::StatementType;
use parser::SymbolType;
use parser::Token;
use parser::TokenAddress;
use parser::TokenPtr;
use parser::TokenRef;
use segment_set::SegmentSet;
use std::cmp::Ordering;
use std::ops::Range;
use std::sync::Arc;
use util::fast_extend;
use util::HashMap;
use util::new_map;

// This module calculates 3 things which are related only by the fact that they can be done
// at the same time:
//
// 1. For $c $v $f and labelled statements ($e $f $a $p): Check for duplication
//
// 2. For $e $d $f $a $p: Check that all used math symbols are active in scope
//
// 3. For $a $p: Compute the frame

// Rules of precedence for error detection and recovery:
//
// 1. Math symbols and labels are actually in separate namespaces.  We warn about collisions but
// otherwise do nothing.  Variables have responsibility for the warning.
//
// 2. When two definitions have overlapping live ranges, the earlier one wins.
//
// 3. Constant/nested variable collisions are special because they don't involve scope overlaps.
// The constant wins, the variable must notify.

#[derive(Clone,Copy)]
struct LocalVarInfo {
    start: TokenAddress,
    end: StatementIndex,
}

#[derive(Copy,Clone,Debug,Default)]
struct LocalFloatInfo<'a> {
    valid: GlobalRange,
    typecode: TokenPtr<'a>,
    label: TokenPtr<'a>,
}

#[derive(Copy,Clone,Debug)]
enum CheckedToken<'a> {
    Const(TokenPtr<'a>),
    Var(TokenPtr<'a>, LocalFloatInfo<'a>),
}

#[derive(Clone,Debug)]
struct LocalDvInfo<'a> {
    valid: GlobalRange,
    vars: Vec<TokenPtr<'a>>,
}

#[derive(Clone,Debug)]
struct LocalEssentialInfo<'a> {
    valid: GlobalRange,
    label: TokenPtr<'a>,
    string: Vec<CheckedToken<'a>>,
}

pub type VarIndex = usize;

#[derive(Clone,Debug)]
pub enum ExprFragment {
    Var(VarIndex),
    Constant(Range<usize>),
}

#[derive(Clone,Debug)]
pub struct VerifyExpr {
    pub typecode: Token,
    pub tail: Vec<ExprFragment>,
}

#[derive(Clone,Debug)]
pub struct Hyp {
    pub address: StatementAddress,
    pub is_float: bool,
    pub variable_index: VarIndex,
    pub expr: VerifyExpr,
}

#[derive(Clone,Debug)]
pub struct Frame {
    pub label: Token,
    pub stype: StatementType,
    pub valid: GlobalRange,
    pub const_pool: Vec<u8>,
    pub hypotheses: Vec<Hyp>,
    pub target: VerifyExpr,
    pub stub_expr: Vec<u8>,
    pub var_list: Vec<Token>,
    pub mandatory_count: usize,
    pub mandatory_dv: Vec<(VarIndex, VarIndex)>,
    pub optional_dv: Vec<Bitset>,
}

struct ScopeState<'a> {
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    // segment: &'a Segment,
    order: &'a SegmentOrder,
    gnames: NameReader<'a>,
    local_vars: HashMap<Token, Vec<LocalVarInfo>>,
    local_floats: HashMap<Token, Vec<LocalFloatInfo<'a>>>,
    local_dv: Vec<LocalDvInfo<'a>>,
    local_essen: Vec<LocalEssentialInfo<'a>>,
    frames_out: Vec<Frame>,
}

fn push_diagnostic(state: &mut ScopeState, ix: StatementIndex, diag: Diagnostic) {
    state.diagnostics.entry(ix).or_insert(Vec::new()).push(diag);
}

fn check_label_dup(state: &mut ScopeState, sref: StatementRef) -> bool {
    // is the label unique in the database?
    if let Some(def) = state.gnames.lookup_label(sref.label()) {
        if def.address != sref.address() {
            push_diagnostic(state, sref.index, Diagnostic::DuplicateLabel(def.address));
            return false;
        }
    }
    true
}

fn check_math_symbol(state: &mut ScopeState,
                     sref: StatementRef,
                     tref: TokenRef)
                     -> Option<SymbolType> {
    // active global definition?
    if let Some(sdef) = state.gnames.lookup_symbol(tref.slice) {
        if state.order.cmp(&sdef.address, &tref.address) == Ordering::Less {
            return Some(sdef.stype);
        }
    }

    // active local definition?
    if let Some(local_slot) = state.local_vars.get(tref.slice).and_then(|slot| slot.last()) {
        if check_endpoint(sref.index, local_slot.end) {
            return Some(SymbolType::Variable);
        }
    }

    push_diagnostic(state, sref.index, Diagnostic::NotActiveSymbol(tref.index()));
    return None;
}

fn lookup_float<'a>(state: &mut ScopeState<'a>,
                    sref: StatementRef<'a>,
                    tref: TokenRef<'a>)
                    -> Option<LocalFloatInfo<'a>> {
    // active global definition?
    if let Some(fdef) = state.gnames.lookup_float(tref.slice) {
        if state.order.cmp(&fdef.address, &sref.address()) == Ordering::Less {
            return Some(LocalFloatInfo {
                valid: fdef.address.unbounded_range(),
                typecode: &fdef.typecode,
                label: &fdef.label,
            });
        }
    }

    // active local definition?
    if let Some(local_slot) = state.local_floats.get(tref.slice).and_then(|slot| slot.last()) {
        if check_endpoint(sref.index, local_slot.valid.end) {
            return Some(*local_slot);
        }
    }

    None
}

fn check_eap<'a, 'b>(state: &'b mut ScopeState<'a>,
                     sref: StatementRef<'a>)
                     -> Option<Vec<CheckedToken<'a>>> {
    // does the math string consist of active tokens, where the first is a constant
    // and all variables have typecodes in scope?
    let mut bad = false;
    let mut out = Vec::new();

    for tref in sref.math_iter() {
        match check_math_symbol(state, sref, tref) {
            None => {
                bad = true;
            }
            Some(SymbolType::Constant) => {
                out.push(CheckedToken::Const(tref.slice));
            }
            Some(SymbolType::Variable) => {
                if tref.index() == 0 {
                    push_diagnostic(state, sref.index, Diagnostic::ExprNotConstantPrefix(0));
                    bad = true;
                } else {
                    match lookup_float(state, sref, tref) {
                        None => {
                            push_diagnostic(state,
                                            sref.index,
                                            Diagnostic::VariableMissingFloat(tref.index()));
                            bad = true;
                        }
                        Some(lfi) => out.push(CheckedToken::Var(tref.slice, lfi)),
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

fn construct_stub_frame(state: &mut ScopeState, sref: StatementRef, expr: &[CheckedToken]) {
    // gets data for $e and $f statements; these are not frames but they
    // are referenced by proofs using a frame-like structure
    let mut iter = expr.iter();
    let typecode = match iter.next().expect("parser checks $eap token count") {
        &CheckedToken::Const(tptr) => tptr,
        _ => unreachable!(),
    };
    let mut mvars = Vec::new();
    let mut conststr = Vec::new();

    while let Some(ctok) = iter.next() {
        match *ctok {
            CheckedToken::Const(tref) => {
                conststr.extend_from_slice(tref);
                conststr.push(b' ');
            }
            CheckedToken::Var(tref, _) => {
                conststr.extend_from_slice(tref);
                conststr.push(b' ');
                mvars.push(tref.to_owned());
            }
        }
    }

    state.frames_out.push(Frame {
        label: sref.label().to_owned(),
        stype: sref.statement.stype,
        valid: sref.scope_range(),
        hypotheses: Vec::new(),
        target: VerifyExpr {
            typecode: typecode.to_owned(),
            tail: Vec::new(),
        },
        const_pool: Vec::new(),
        stub_expr: conststr,
        mandatory_count: mvars.len(),
        var_list: mvars,
        mandatory_dv: Vec::new(),
        optional_dv: Vec::new(),
    });
}

struct InchoateFrame<'a> {
    variables: HashMap<TokenPtr<'a>, (VarIndex, LocalFloatInfo<'a>)>,
    var_list: Vec<Token>,
    mandatory_count: usize,
    mandatory_dv: Vec<(VarIndex, VarIndex)>,
    optional_dv: Vec<Bitset>,
    const_pool: Vec<u8>,
}

fn scan_expression<'a>(iframe: &mut InchoateFrame<'a>, expr: &[CheckedToken<'a>]) -> VerifyExpr {
    let mut iter = expr.iter();
    let head = match iter.next().expect("parser checks $eap token count") {
        &CheckedToken::Const(tptr) => tptr,
        _ => unreachable!(),
    };
    let mut open_const = iframe.const_pool.len();
    let mut tail = Vec::new();

    while let Some(ctok) = iter.next() {
        match *ctok {
            CheckedToken::Const(tref) => {
                fast_extend(&mut iframe.const_pool, tref);
                iframe.const_pool.push(b' ');
            }
            CheckedToken::Var(tref, lfi) => {
                if open_const != iframe.const_pool.len() {
                    tail.push(ExprFragment::Constant(open_const .. iframe.const_pool.len()));
                    open_const = iframe.const_pool.len();
                }

                let index = match iframe.variables.get(&tref).map(|&(x, _)| x) {
                    Some(mvarindex) => mvarindex,
                    None => {
                        let index = iframe.variables.len();
                        iframe.var_list.push(tref.to_owned());
                        iframe.optional_dv.push(Bitset::new());
                        iframe.variables.insert(tref, (index, lfi));
                        index
                    }
                };
                tail.push(ExprFragment::Var(index));
            }
        }
    }

    if open_const != iframe.const_pool.len() {
        tail.push(ExprFragment::Constant(open_const .. iframe.const_pool.len()));
    }

    VerifyExpr {
        typecode: head.to_owned(),
        tail: tail,
    }
}

fn scan_dv<'a>(iframe: &mut InchoateFrame<'a>, var_set: &[TokenPtr<'a>]) {
    // any variable encountered for the first time in a dv is an optional
    // variable, but we already checked validity in scope_check_dv
    let mut var_ids = Vec::with_capacity(var_set.len());

    for &vartok in var_set {
        let index = match iframe.variables.get(vartok).map(|&(x, _)| x) {
            Some(mvarindex) => mvarindex,
            None => {
                let index = iframe.variables.len();
                iframe.var_list.push(vartok.to_owned());
                iframe.optional_dv.push(Bitset::new());
                iframe.variables.insert(vartok, (index, Default::default()));
                index
            }
        };
        var_ids.push(index);
    }

    for (leftpos, &leftid) in var_ids.iter().enumerate() {
        for &rightid in &var_ids[leftpos + 1..] {
            if !iframe.optional_dv[leftid].has_bit(rightid) {
                iframe.optional_dv[leftid].set_bit(rightid);
                iframe.optional_dv[rightid].set_bit(leftid);
                if leftid < iframe.mandatory_count && rightid < iframe.mandatory_count {
                    iframe.mandatory_dv.push((leftid, rightid));
                }
            }
        }
    }
}

fn construct_full_frame<'a>(state: &mut ScopeState<'a>,
                            sref: StatementRef<'a>,
                            expr: &[CheckedToken<'a>]) {
    state.local_essen.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
    state.local_dv.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
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
        hyps.push(Hyp {
            address: ess.valid.start,
            is_float: false,
            variable_index: 0,
            expr: scanned,
        });
    }

    let scan_res = scan_expression(&mut iframe, expr);

    // include any mandatory $f hyps
    for &(index, ref lfi) in iframe.variables.values() {
        hyps.push(Hyp {
            address: lfi.valid.start,
            is_float: true,
            variable_index: index,
            expr: VerifyExpr {
                typecode: lfi.typecode.to_owned(),
                tail: vec![ExprFragment::Var(index)],
            },
        })
    }

    hyps.sort_by(|h1, h2| state.order.cmp(&h1.address, &h2.address));
    iframe.mandatory_count = iframe.var_list.len();

    for &ref dv in &state.gnames.lookup_global_dv() {
        scan_dv(&mut iframe, &dv.vars)
    }

    for &ref dv in &state.local_dv {
        scan_dv(&mut iframe, &dv.vars);
    }

    state.frames_out.push(Frame {
        label: sref.label().to_owned(),
        stype: sref.statement.stype,
        valid: sref.address().unbounded_range(),
        hypotheses: hyps,
        target: scan_res,
        stub_expr: Vec::new(),
        const_pool: iframe.const_pool,
        var_list: iframe.var_list,
        mandatory_count: iframe.mandatory_count,
        mandatory_dv: iframe.mandatory_dv,
        optional_dv: iframe.optional_dv,
    });
}

fn scope_check_axiom<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if !check_label_dup(state, sref) {
        return;
    }
    if let Some(expr) = check_eap(state, sref) {
        construct_full_frame(state, sref, &expr);
    }
}

fn scope_check_constant(state: &mut ScopeState, sref: StatementRef) {
    if sref.statement.group != NO_STATEMENT {
        assert!(sref.statement.diagnostics.len() > 0);
        return;
    }

    for tokref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(tokref.slice) {
            push_diagnostic(state,
                            sref.index,
                            Diagnostic::SymbolDuplicatesLabel(tokref.index(), ldef.address));
        }

        if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
            if cdef.address != tokref.address {
                push_diagnostic(state,
                                sref.index,
                                Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
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
            None => {
                bad = true;
            }
            Some(SymbolType::Constant) => {
                push_diagnostic(state, sref.index, Diagnostic::DjNotVariable(tref.index()));
                bad = true;
            }
            _ => {
                if let Some(&previx) = used.get(tref.slice) {
                    push_diagnostic(state,
                                    sref.index,
                                    Diagnostic::DjRepeatedVariable(tref.index(), previx));
                    bad = true;
                    continue;
                }

                used.insert(tref.slice, tref.index());
                vars.push(tref.slice);
            }
        }
    }

    if bad {
        return;
    }

    state.local_dv.push(LocalDvInfo {
        valid: sref.scope_range(),
        vars: vars,
    });
}

fn scope_check_essential<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if !check_label_dup(state, sref) {
        return;
    }
    if let Some(expr) = check_eap(state, sref) {
        construct_stub_frame(state, sref, &expr);
        state.local_essen.push(LocalEssentialInfo {
            valid: sref.scope_range(),
            label: sref.label(),
            string: expr,
        });
    }
}

fn scope_check_float<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut bad = false;
    assert!(sref.math_len() == 2);
    let const_tok = sref.math_at(0);
    let var_tok = sref.math_at(1);

    if !check_label_dup(state, sref) {
        return;
    }

    match check_math_symbol(state, sref, const_tok) {
        None => {
            bad = true;
        }
        Some(SymbolType::Constant) => {}
        Some(SymbolType::Variable) => {
            push_diagnostic(state, sref.index, Diagnostic::FloatNotConstant(0));
            bad = true;
        }
    }

    match check_math_symbol(state, sref, var_tok) {
        None => {
            bad = true;
        }
        Some(SymbolType::Variable) => {}
        _ => {
            push_diagnostic(state, sref.index, Diagnostic::FloatNotVariable(1));
            bad = true;
        }
    }

    if bad {
        return;
    }

    if let Some(prev) = lookup_float(state, sref, sref.math_at(1)) {
        push_diagnostic(state,
                        sref.index,
                        Diagnostic::FloatRedeclared(prev.valid.start));
        return;
    }

    // record the $f
    if sref.statement.group_end != NO_STATEMENT {
        state.local_floats
            .entry(var_tok.slice.to_owned())
            .or_insert(Vec::new())
            .push(LocalFloatInfo {
                typecode: const_tok.slice,
                label: sref.label(),
                valid: sref.scope_range(),
            });
    }

    construct_stub_frame(state,
                         sref,
                         &[CheckedToken::Const(const_tok.slice),
                           CheckedToken::Var(var_tok.slice, LocalFloatInfo::default())]);
}

fn check_endpoint(cur: StatementIndex, end: StatementIndex) -> bool {
    end == NO_STATEMENT || cur < end
}

// factored out to make a useful borrow scope
fn maybe_add_local_var(state: &mut ScopeState,
                       sref: StatementRef,
                       tokref: TokenRef)
                       -> Option<TokenAddress> {
    let lv_slot = state.local_vars.entry(tokref.slice.to_owned()).or_insert(Vec::new());

    if let Some(lv_most_recent) = lv_slot.last() {
        if check_endpoint(sref.index, lv_most_recent.end) {
            return Some(lv_most_recent.start);
        }
    }

    lv_slot.push(LocalVarInfo {
        start: tokref.address,
        end: sref.statement.group_end,
    });
    None
}

fn scope_check_provable<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if !check_label_dup(state, sref) {
        return;
    }
    if let Some(expr) = check_eap(state, sref) {
        construct_full_frame(state, sref, &expr);
    }
}

fn scope_check_variable(state: &mut ScopeState, sref: StatementRef) {
    for tokref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(tokref.slice) {
            push_diagnostic(state,
                            sref.index,
                            Diagnostic::SymbolDuplicatesLabel(tokref.index(), ldef.address));
        }

        if sref.statement.group == NO_STATEMENT {
            // top level $v, may conflict with a prior $c
            if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
                if cdef.address != tokref.address {
                    push_diagnostic(state,
                                    sref.index,
                                    Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
                }
            }
        } else {
            // nested $v, may conflict with an outer scope $v, top level $v/$c, or a _later_ $c
            if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
                if state.order.cmp(&cdef.address, &tokref.address) == Ordering::Less {
                    push_diagnostic(state,
                                    sref.index,
                                    Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
                    continue;
                } else if cdef.stype == SymbolType::Constant {
                    push_diagnostic(state,
                                    sref.index,
                                    Diagnostic::VariableRedeclaredAsConstant(tokref.index(),
                                                                             cdef.address));
                    continue;
                }
            }

            if let Some(prev_addr) = maybe_add_local_var(state, sref, tokref) {
                // local/local conflict
                push_diagnostic(state,
                                sref.index,
                                Diagnostic::SymbolRedeclared(tokref.index(), prev_addr));
            }
        }
    }
}

pub struct SegmentScopeResult {
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    frames_out: Vec<Frame>,
}

pub fn scope_check_single(names: &Nameset, seg: SegmentRef) -> SegmentScopeResult {
    let mut state = ScopeState {
        diagnostics: new_map(),
        order: &names.order,
        gnames: NameReader::new(names),
        local_vars: new_map(),
        local_floats: new_map(),
        local_dv: Vec::new(),
        local_essen: Vec::new(),
        frames_out: Vec::new(),
    };

    for sref in seg.statement_iter() {
        match sref.statement.stype {
            StatementType::Axiom => scope_check_axiom(&mut state, sref),
            StatementType::Constant => scope_check_constant(&mut state, sref),
            StatementType::Disjoint => scope_check_dv(&mut state, sref),
            StatementType::Essential => scope_check_essential(&mut state, sref),
            StatementType::Floating => scope_check_float(&mut state, sref),
            StatementType::Provable => scope_check_provable(&mut state, sref),
            StatementType::Variable => scope_check_variable(&mut state, sref),
            _ => {}
        }
    }

    SegmentScopeResult {
        diagnostics: state.diagnostics,
        frames_out: state.frames_out,
    }
}

pub struct ScopeResult {
    segments: Vec<(SegmentId, Arc<SegmentScopeResult>)>,
    frame_index: HashMap<Token, (usize, usize)>,
}

impl ScopeResult {
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for &(sid, ref ssr) in &self.segments {
            for (&six, &ref diag) in &ssr.diagnostics {
                for &ref d in diag {
                    out.push((StatementAddress::new(sid, six), d.clone()));
                }
            }
        }
        out
    }
}

pub fn scope_check(segments: &SegmentSet, names: &Nameset) -> ScopeResult {
    let mut out = ScopeResult {
        segments: Vec::new(),
        frame_index: new_map(),
    };
    for sref in segments.segments() {
        let ssr = Arc::new(scope_check_single(names, sref));
        let six = out.segments.len();
        out.segments.push((sref.id, ssr.clone()));

        for (index, frame) in ssr.frames_out.iter().enumerate() {
            let old = out.frame_index.insert(frame.label.clone(), (six, index));
            assert!(old.is_none(), "check_label_dup should prevent this");
        }
    }
    out
}

#[derive(Clone,Copy)]
pub struct ScopeReader<'a> {
    result: &'a ScopeResult,
}

impl<'a> ScopeReader<'a> {
    pub fn new(res: &'a ScopeResult) -> ScopeReader<'a> {
        ScopeReader { result: res }
    }

    pub fn get(&self, name: TokenPtr) -> Option<&'a Frame> {
        match self.result.frame_index.get(name) {
            None => None,
            Some(&(six, frix)) => Some(&self.result.segments[six].1.frames_out[frix]),
        }
    }
}
