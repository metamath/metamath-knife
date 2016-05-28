use nameck::NameReader;
use nameck::Nameset;
use parser::Comparer;
use parser::Diagnostic;
use parser::GlobalRange;
use parser::SegmentRef;
use parser::StatementAddress;
use parser::StatementRef;
use parser::StatementIndex;
use parser::StatementType;
use parser::SymbolType;
use parser::SegmentOrder;
use parser::Token;
use parser::TokenAddress;
use parser::TokenPtr;
use parser::TokenRef;
use parser::NO_STATEMENT;
use std::collections::HashMap;
use std::cmp::Ordering;
use std::mem;

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

#[derive(Copy,Clone,Debug)]
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

pub type MandVarIndex = usize;

#[derive(Clone,Debug)]
pub enum ExprFragment {
    Var(MandVarIndex),
    Constant(Vec<u8>),
}

#[derive(Clone,Debug)]
pub struct VerifyExpr {
    pub typecode: Token,
    pub tail: Vec<ExprFragment>,
}

#[derive(Clone,Debug)]
pub struct Hyp {
    pub address: StatementAddress,
    pub label: Token,
    pub is_float: bool,
    pub variable_index: MandVarIndex,
    pub expr: VerifyExpr,
}

#[derive(Clone,Debug)]
pub struct Frame {
    pub stype: StatementType,
    pub valid: GlobalRange,
    pub hypotheses: Vec<Hyp>,
    pub target: VerifyExpr,
    pub mandatory_vars: Vec<Token>,
    pub mandatory_dv: Vec<(MandVarIndex, MandVarIndex)>,
    pub optional_dv: Vec<(Token, Token)>,
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

fn check_math_symbol(state: &mut ScopeState, sref: StatementRef, tref: TokenRef) -> Option<SymbolType> {
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
    return None
}

fn lookup_float<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>, tref: TokenRef<'a>) -> Option<LocalFloatInfo<'a>> {
    // active global definition?
    if let Some(fdef) = state.gnames.lookup_float(tref.slice) {
        if state.order.cmp(&fdef.address, &sref.address()) == Ordering::Less {
            return Some(LocalFloatInfo { valid: fdef.address.unbounded_range(), typecode: &fdef.typecode, label: &fdef.label });
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

fn check_eap<'a,'b>(state: &'b mut ScopeState<'a>, sref: StatementRef<'a>) -> Option<Vec<CheckedToken<'a>>> {
    // does the math string consist of active tokens, where the first is a constant and all variables have typecodes in scope?
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
                            push_diagnostic(state, sref.index, Diagnostic::VariableMissingFloat(tref.index()));
                            bad = true;
                        }
                        Some(lfi) => {
                            out.push(CheckedToken::Var(tref.slice, lfi))
                        }
                    }
                }
            }
        }
    }

    if bad { None } else { Some(out) }
}

fn construct_stub_frame(state: &mut ScopeState, sref: StatementRef) {
    // gets data for $e and $f statements; these are not frames but they are referenced by proofs using a frame-like structure
    let mut mathi = sref.math_iter();
    let typecode_tr = mathi.next().expect("parser checks $e token count");
    let typecode = typecode_tr.slice.to_owned();
    let expr : Vec<_> = mathi.map(|tref| {
        ExprFragment::Constant(tref.slice.to_owned())
    }).collect();

    state.frames_out.push(Frame {
       stype: sref.statement.stype,
       valid: sref.scope_range(),
       hypotheses: Vec::new(),
       target: VerifyExpr {
           typecode: typecode,
           tail: expr,
       },
       mandatory_vars: Vec::new(),
       mandatory_dv: Vec::new(),
       optional_dv: Vec::new(),
    });
}

struct InchoateFrame<'a> {
    variables: HashMap<TokenPtr<'a>, (MandVarIndex, LocalFloatInfo<'a>)>,
    var_list: Vec<Token>,
    mandatory_dv: Vec<(MandVarIndex, MandVarIndex)>,
    optional_dv: Vec<(Token, Token)>,
}

fn scan_expression<'a>(iframe: &mut InchoateFrame<'a>, expr: &[CheckedToken<'a>]) -> VerifyExpr {
    let mut iter = expr.iter();
    let head = match iter.next().expect("parser checks $eap token count") {
        &CheckedToken::Const(tptr) => tptr,
        _ => unreachable!(),
    };
    let mut open_const = Vec::new();
    let mut tail = Vec::new();

    while let Some(ctok) = iter.next() {
        match *ctok {
            CheckedToken::Const(tref) => {
                open_const.extend_from_slice(tref);
                open_const.push(b' ');
            }
            CheckedToken::Var(tref, lfi) => {
                if !open_const.is_empty() {
                    tail.push(ExprFragment::Constant(mem::replace(&mut open_const, Vec::new())));
                }

                let index = match iframe.variables.get(&tref).map(|&(x,_)| x) {
                    Some(mvarindex) => mvarindex,
                    None => {
                        let index = iframe.variables.len();
                        iframe.var_list.push(tref.to_owned());
                        iframe.variables.insert(tref, (index, lfi));
                        index
                    }
                };
                tail.push(ExprFragment::Var(index));
            }
        }
    }

    if !open_const.is_empty() {
        tail.push(ExprFragment::Constant(mem::replace(&mut open_const, Vec::new())));
    }

    VerifyExpr {
        typecode: head.to_owned(),
        tail: tail
    }
}

fn scan_dv<'a>(iframe: &mut InchoateFrame<'a>, var_set: &[TokenPtr<'a>]) {
    for (lefti, &lefttok) in var_set.iter().enumerate() {
        let leftmvi = iframe.variables.get(&lefttok).map(|&(ix,_)| ix);
        for &righttok in &var_set[lefti + 1 ..] {
            if let Some(leftix) = leftmvi {
                if let Some(rightix) = iframe.variables.get(&righttok).map(|&(ix,_)| ix) {
                    iframe.mandatory_dv.push((leftix, rightix));
                }
            }
            iframe.optional_dv.push((lefttok.to_owned(), righttok.to_owned()));
        }
    }
}

fn construct_full_frame<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>, expr: &[CheckedToken<'a>]) {
    state.local_essen.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
    state.local_dv.retain(|hyp| check_endpoint(sref.index, hyp.valid.end));
    // local_essen and local_dv now contain only things still in scope

    // collect mandatory variables
    let mut iframe = InchoateFrame { variables: HashMap::new(), var_list: Vec::new(), optional_dv: Vec::new(), mandatory_dv: Vec::new() };
    let mut hyps = Vec::new();

    for ess in &state.local_essen {
        let scanned = scan_expression(&mut iframe, &ess.string);
        hyps.push(Hyp {
            address: ess.valid.start,
            label: ess.label.to_owned(),
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
            label: lfi.label.to_owned(),
            is_float: true,
            variable_index: index,
            expr: VerifyExpr { typecode: lfi.typecode.to_owned(), tail: vec![ExprFragment::Var(index)] },
        })
    }

    hyps.sort_by(|h1, h2| state.order.cmp(&h1.address, &h2.address));

    for &ref dv in &state.gnames.lookup_global_dv() {
        scan_dv(&mut iframe, &dv.vars)
    }

    for &ref dv in &state.local_dv {
        scan_dv(&mut iframe, &dv.vars);
    }

    state.frames_out.push(Frame {
        stype: sref.statement.stype,
        valid: sref.scope_range(),
        hypotheses: hyps,
        target: scan_res,
        mandatory_vars: iframe.var_list,
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
    if sref.statement.group == NO_STATEMENT {
        assert!(sref.statement.diagnostics.len() > 0);
        return;
    }

    for tokref in sref.math_iter() {
        if let Some(ldef) = state.gnames.lookup_label(tokref.slice) {
            push_diagnostic(state, sref.index, Diagnostic::SymbolDuplicatesLabel(tokref.index(), ldef.address));
        }

        if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
            if cdef.address != tokref.address {
                push_diagnostic(state, sref.index, Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
            }
        }
    }
}

fn scope_check_dv<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut used = HashMap::new();
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
                    push_diagnostic(state, sref.index, Diagnostic::DjRepeatedVariable(tref.index(), previx));
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

    state.local_dv.push(LocalDvInfo { valid: sref.scope_range(), vars: vars });
}

fn scope_check_essential<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    if !check_label_dup(state, sref) {
        return;
    }
    if let Some(expr) = check_eap(state, sref) {
        construct_stub_frame(state, sref);
        state.local_essen.push(LocalEssentialInfo {
            valid: sref.scope_range(), label: sref.label(), string: expr,
        });
    }
}

fn scope_check_float<'a>(state: &mut ScopeState<'a>, sref: StatementRef<'a>) {
    let mut bad = false;
    assert!(sref.math_len() == 2);
    let const_tok = sref.math_at(0);
    let var_tok = sref.math_at(1);

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
        push_diagnostic(state, sref.index, Diagnostic::FloatRedeclared(prev.valid.start));
        return;
    }

    // record the $f
    if sref.statement.group_end != NO_STATEMENT {
        state.local_floats.entry(var_tok.slice.to_owned()).or_insert(Vec::new()).push(LocalFloatInfo {
            typecode: const_tok.slice, label: sref.label(), valid: sref.scope_range()
        });
    }

    construct_stub_frame(state, sref);
}

fn check_endpoint(cur: StatementIndex, end: StatementIndex) -> bool {
    end == NO_STATEMENT || cur < end
}

// factored out to make a useful borrow scope
fn maybe_add_local_var(state: &mut ScopeState, sref: StatementRef, tokref: TokenRef) -> Option<TokenAddress> {
    let lv_slot = state.local_vars.entry(tokref.slice.to_owned()).or_insert(Vec::new());

    if let Some(lv_most_recent) = lv_slot.last() {
        if check_endpoint(sref.index, lv_most_recent.end) {
            return Some(lv_most_recent.start);
        }
    }

    lv_slot.push(LocalVarInfo { start: tokref.address, end: sref.statement.group_end });
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
            push_diagnostic(state, sref.index, Diagnostic::SymbolDuplicatesLabel(tokref.index(), ldef.address));
        }

        if sref.statement.group == NO_STATEMENT {
            // top level $v, may conflict with a prior $c
            if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
                if cdef.address != tokref.address {
                    push_diagnostic(state, sref.index, Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
                }
            }
        } else {
            // nested $v, may conflict with an outer scope $v, top level $v/$c, or a _later_ $c
            if let Some(cdef) = state.gnames.lookup_symbol(tokref.slice) {
                if state.order.cmp(&cdef.address, &tokref.address) == Ordering::Less {
                    push_diagnostic(state, sref.index, Diagnostic::SymbolRedeclared(tokref.index(), cdef.address));
                    continue;
                } else if cdef.stype == SymbolType::Constant {
                    push_diagnostic(state, sref.index, Diagnostic::VariableRedeclaredAsConstant(tokref.index(), cdef.address));
                    continue;
                }
            }

            if let Some(prev_addr) = maybe_add_local_var(state, sref, tokref) {
                // local/local conflict
                push_diagnostic(state, sref.index, Diagnostic::SymbolRedeclared(tokref.index(), prev_addr));
            }
        }
    }
}

pub fn scope_check(_names: &Nameset, _seg: SegmentRef) {
    let mut _state: ScopeState = unimplemented!();

    for sref in _seg.statement_iter() {
        match sref.statement.stype {
            StatementType::Axiom => scope_check_axiom(&mut _state, sref),
            StatementType::Constant => scope_check_constant(&mut _state, sref),
            StatementType::Disjoint => scope_check_dv(&mut _state, sref),
            StatementType::Essential => scope_check_essential(&mut _state, sref),
            StatementType::Floating => scope_check_float(&mut _state, sref),
            StatementType::Provable => scope_check_provable(&mut _state, sref),
            StatementType::Variable => scope_check_variable(&mut _state, sref),
            _ => {}
        }
    }
}
