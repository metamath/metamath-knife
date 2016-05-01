use nameck::NameReader;
use nameck::Nameset;
use parser::Diagnostic;
use parser::Segment;
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

struct LocalVarInfo {
    start: TokenAddress,
    end: StatementIndex,
}

struct ScopeState<'a> {
    diagnostics: HashMap<StatementIndex, Vec<Diagnostic>>,
    // segment: &'a Segment,
    order: &'a SegmentOrder,
    gnames: NameReader<'a>,
    local_vars: HashMap<Token, Vec<LocalVarInfo>>,
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

fn check_eap(state: &mut ScopeState, sref: StatementRef) {
    // does the math string consist of active tokens, where the first is a constant and all variables have typecodes in scope?
    unimplemented!()
}

fn scope_check_axiom(state: &mut ScopeState, sref: StatementRef) {
    check_label_dup(state, sref);
    check_eap(state, sref);
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

pub fn scope_check(_names: &Nameset, seg: &Segment) {
    let mut state: ScopeState = unimplemented!();

    for sref in seg.statement_iter() {
        match sref.statement.stype {
            StatementType::Axiom => scope_check_axiom(&mut state, sref),
            StatementType::Constant => scope_check_constant(&mut state, sref),
            StatementType::Disjoint => {
                // check math string, including $f (?)
            }
            StatementType::Essential => {
                check_label_dup(&mut state, sref);
                check_eap(&mut state, sref);
                // push on hyp stack
            }
            StatementType::Floating => {
                check_label_dup(&mut state, sref);
                // check $f duplication
                // check variables active in scope
                // push on hyp stack
            }
            StatementType::Provable => {
                check_label_dup(&mut state, sref);
                check_eap(&mut state, sref);
                // spit out a frame
            }
            StatementType::Variable => scope_check_variable(&mut state, sref),
            _ => {}
        }
    }
}
