use nameck::NameReader;
use nameck::Nameset;
use parser::Diagnostic;
use parser::SegmentRef;
use parser::StatementAddress;
use parser::StatementRef;
use parser::StatementIndex;
use parser::StatementType;
use parser::SymbolType;
use parser::SegmentOrder;
use parser::Token;
use parser::TokenAddress;
use parser::TokenRef;
use parser::NO_STATEMENT;
use std::collections::HashMap;
use std::cmp::Ordering;

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

#[derive(Clone,Debug)]
struct LocalFloatInfo {
    start: StatementAddress,
    end: StatementIndex,
    typecode: Token,
    label: Token,
}

struct ScopeState<'a> {
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    // segment: &'a Segment,
    order: &'a SegmentOrder,
    gnames: NameReader<'a>,
    local_vars: HashMap<Token, Vec<LocalVarInfo>>,
    local_floats: HashMap<Token, Vec<LocalFloatInfo>>,
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
        if state.order.cmp_3(sdef.address, tref.address) == Ordering::Less {
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

fn lookup_float(state: &mut ScopeState, sref: StatementRef, tref: TokenRef) -> Option<LocalFloatInfo> {
    // active global definition?
    if let Some(fdef) = state.gnames.lookup_float(tref.slice) {
        if state.order.cmp_2(fdef.address, sref.address()) == Ordering::Less {
            return Some(LocalFloatInfo { start: fdef.address, typecode: fdef.typecode, label: fdef.label.clone(), end: NO_STATEMENT });
        }
    }

    // active local definition?
    if let Some(local_slot) = state.local_floats.get(tref.slice).and_then(|slot| slot.last()) {
        if check_endpoint(sref.index, local_slot.end) {
            return Some(local_slot.clone()); // TODO shouldn't allocate
        }
    }

    None
}

fn check_eap(state: &mut ScopeState, sref: StatementRef) -> bool {
    // does the math string consist of active tokens, where the first is a constant and all variables have typecodes in scope?
    let mut bad = false;

    for tref in sref.math_iter() {
        match check_math_symbol(state, sref, tref) {
            None => {
                bad = true;
            }
            Some(SymbolType::Constant) => {
            }
            _ => {
                if tref.index() == 0 {
                    push_diagnostic(state, sref.index, Diagnostic::ExprNotConstantPrefix(0));
                    bad = true;
                } else if lookup_float(state, sref, tref).is_none() {
                    push_diagnostic(state, sref.index, Diagnostic::VariableMissingFloat(tref.index()));
                    bad = true;
                }
            }
        }
    }

    !bad
}

fn scope_check_axiom(state: &mut ScopeState, sref: StatementRef) {
    if !check_label_dup(state, sref) {
        return;
    }
    if !check_eap(state, sref) {
        return;
    }
    // TODO spit out a frame
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

fn scope_check_dv(state: &mut ScopeState, sref: StatementRef) {
    let mut used = HashMap::new();
    let mut bad = false;

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
            }
        }
    }

    if bad {
        return;
    }

    // TODO: record the dv somewhere it can be used for frame-building
}

fn scope_check_essential(state: &mut ScopeState, sref: StatementRef) {
    if !check_label_dup(state, sref) {
        return;
    }
    if !check_eap(state, sref) {
        return;
    }
    // TODO spit out a frame
}

fn scope_check_float(state: &mut ScopeState, sref: StatementRef) {
    let mut bad = false;
    assert!(sref.math_len() == 2);
    let const_tok = sref.math_at(0);
    let var_tok = sref.math_at(1);

    match check_math_symbol(state, sref, const_tok) {
        None => {
            bad = true;
        }
        Some(SymbolType::Constant) => {}
        _ => {
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
        push_diagnostic(state, sref.index, Diagnostic::FloatRedeclared(prev.start));
        return;
    }

    // record the $f

    state.local_floats.entry(var_tok.slice.to_owned()).or_insert(Vec::new()).push(LocalFloatInfo {
        typecode: const_tok.slice.to_owned(), label: sref.label().to_owned(), start: sref.address(), end: sref.statement.group_end
    });
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

fn scope_check_provable(state: &mut ScopeState, sref: StatementRef) {
    if !check_label_dup(state, sref) {
        return;
    }
    if !check_eap(state, sref) {
        return;
    }
    // TODO spit out a frame
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
                if state.order.cmp_3(cdef.address, tokref.address) == Ordering::Less {
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

pub fn scope_check(_names: &Nameset, seg: SegmentRef) {
    let mut state: ScopeState = unimplemented!();

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
}
