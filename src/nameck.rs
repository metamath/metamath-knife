// TODO experiment with FNV hashers, etc.
use std::collections::{HashMap, HashSet};
use parser::{GlobalRange, Segment, SegmentId, SegmentRef, StatementAddress, SymbolType, Token, TokenAddress, TokenIndex};
// An earlier version of this module was tasked with detecting duplicate symbol errors;
// current task is just lookup

// pub struct Atom(u32);

struct GlobalDvInfo {
    address: StatementAddress,
    vars: Vec<Token>,
}

struct LabelInfo {
    address: StatementAddress,
}

struct SymbolInfo {
    stype: SymbolType,
    address: StatementAddress,
    ordinal: TokenIndex,
}

struct FloatInfo {
    address: StatementAddress,
    label: Token,
    typecode: Token,
}

pub struct Nameset {
    // next_atom: u32,
    // unused_atoms: Vec<Atom>,
    segments: HashSet<SegmentId>,
    dv_info: Vec<GlobalDvInfo>,
    symbols: HashMap<Token, Vec<SymbolInfo>>,
    float_types: HashMap<Token, Vec<FloatInfo>>,
}

pub fn add_parsed_segment(set: &mut Nameset, seg: SegmentRef) {
    if set.segments.contains(&seg.id) {
        return;
    }

    set.segments.insert(seg.id);

    for &ref symdef in &seg.segment.symbols {
        set.symbols.entry(symdef.name.clone()).or_insert(Vec::new()).push(SymbolInfo {
            address: StatementAddress { segment_id: seg.id, index: symdef.start },
            stype: symdef.stype, ordinal: symdef.ordinal,
        });
    }

    for &ref floatdef in &seg.segment.floats {
        set.float_types.entry(floatdef.name.clone()).or_insert(Vec::new()).push(FloatInfo {
            address: StatementAddress { segment_id: seg.id, index: floatdef.start },
            label: floatdef.label.clone(), typecode: floatdef.typecode.clone(),
        });
    }

    for &ref dvdef in &seg.segment.global_dvs {
        set.dv_info.push(GlobalDvInfo {
            address: StatementAddress { segment_id: seg.id, index: dvdef.start },
            vars: dvdef.vars.clone()
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