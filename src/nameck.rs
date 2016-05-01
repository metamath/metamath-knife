// TODO experiment with FNV hashers, etc.
use std::collections::{HashMap, HashSet};
use parser::{GlobalRange, Segment, SegmentId, StatementAddress, SymbolType, Token, TokenAddress, TokenIndex};
// An earlier version of this module was tasked with detecting duplicate symbol errors;
// current task is just lookup

// pub struct Atom(u32);

struct GlobalDvInfo {
    valid: GlobalRange,
    vars: Vec<Token>,
}

struct SymbolInfo {
    stype: SymbolType,
    valid: GlobalRange,
    ordinal: TokenIndex,
}

struct FloatInfo {
    valid: GlobalRange,
    label: Token,
    ttype: Token,
}

pub struct Nameset {
    // next_atom: u32,
    // unused_atoms: Vec<Atom>,
    segments: HashSet<SegmentId>,
    dv_info: Vec<GlobalDvInfo>,
    symbols: HashMap<Token, Vec<SymbolInfo>>,
    float_types: HashMap<Token, Vec<FloatInfo>>,
}

pub fn add_parsed_segment(set: &mut Nameset, seg: &Segment) {
    if set.segments.contains(&seg.id) {
        return;
    }

    set.segments.insert(seg.id);

    for &ref symdef in &seg.symbols {
        set.symbols.entry(symdef.name.clone()).or_insert(Vec::new()).push(SymbolInfo {
           stype: symdef.stype, valid: symdef.valid, ordinal: symdef.ordinal,
        });
    }

    for &ref floatdef in &seg.floats {
        set.float_types.entry(floatdef.name.clone()).or_insert(Vec::new()).push(FloatInfo {
           valid: floatdef.valid, label: floatdef.label.clone(), ttype: floatdef.type_.clone(),
        });
    }

    for &ref dvdef in &seg.global_dvs {
        set.dv_info.push(GlobalDvInfo {
            valid: dvdef.valid, vars: dvdef.vars.clone()
        })
    }
}

pub struct NameReader<'a> {
    nameset: &'a Nameset,
}

pub struct LookupLabel {
    /// Address of topmost statement with this label
    pub address: StatementAddress,
}

pub struct LookupSymbol {
    pub stype: SymbolType,
    /// Address of topmost global $c/$v with this token
    pub address: TokenAddress,
    /// Address of topmost global $c, if any
    pub const_address: Option<TokenAddress>,
}

// TODO without allocating
pub struct LookupFloat {
    pub address: StatementAddress,
    pub label: Token,
    pub typecode: Token,
}

impl<'a> NameReader<'a> {
    pub fn new() -> Self {
        unimplemented!()
    }

    // TODO: add versions which fetch less data, to reduce dep tracking overhead
    pub fn lookup_label(&mut self, _label: &[u8]) -> Option<LookupLabel> {
        unimplemented!()
    }

    pub fn lookup_symbol(&mut self, _symbol: &[u8]) -> Option<LookupSymbol> {
        unimplemented!()
    }

    // TODO: consider merging this with lookup_symbol
    pub fn lookup_float(&mut self, _symbol: &[u8]) -> Option<LookupFloat> {
        unimplemented!()
    }
}