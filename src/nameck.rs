// TODO experiment with FNV hashers, etc.
use std::collections::HashMap;
use std::cmp::Ordering;
use std::sync::Arc;
use parser::{Comparer, Segment, SegmentId, SegmentOrder, StatementAddress, SymbolType, Token, TokenAddress, TokenPtr};
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
    address: TokenAddress,
}

struct FloatInfo {
    address: StatementAddress,
    label: Token,
    typecode: Token,
}

pub struct Nameset {
    // next_atom: u32,
    // unused_atoms: Vec<Atom>,
    order: Arc<SegmentOrder>,
    segments: HashMap<SegmentId, Arc<Segment>>,
    dv_info: Vec<GlobalDvInfo>,
    labels: HashMap<Token, Vec<LabelInfo>>,
    symbols: HashMap<Token, Vec<SymbolInfo>>,
    float_types: HashMap<Token, Vec<FloatInfo>>,
}

pub fn add_parsed_segment(set: &mut Nameset, id: SegmentId, seg: Arc<Segment>) {
    if set.segments.contains_key(&id) {
        return;
    }

    set.segments.insert(id, seg.clone());

    for &ref symdef in &seg.symbols {
        set.symbols.entry(symdef.name.clone()).or_insert(Vec::new()).push(SymbolInfo {
            address: TokenAddress {
                statement: StatementAddress { segment_id: id, index: symdef.start },
                token_index: symdef.ordinal,
            }, stype: symdef.stype,
        });
    }

    for &ref labdef in &seg.labels {
        set.labels.entry(labdef.label.clone()).or_insert(Vec::new()).push(LabelInfo {
            address: StatementAddress { segment_id: id, index: labdef.index },
        });
    }

    for &ref floatdef in &seg.floats {
        set.float_types.entry(floatdef.name.clone()).or_insert(Vec::new()).push(FloatInfo {
            address: StatementAddress { segment_id: id, index: floatdef.start },
            label: floatdef.label.clone(), typecode: floatdef.typecode.clone(),
        });
    }

    for &ref dvdef in &seg.global_dvs {
        set.dv_info.push(GlobalDvInfo {
            address: StatementAddress { segment_id: id, index: dvdef.start },
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

pub struct LookupFloat<'a> {
    // again, topmost global float
    pub address: StatementAddress,
    pub label: TokenPtr<'a>,
    pub typecode: TokenPtr<'a>,
}

pub struct LookupGlobalDv<'a> {
    pub address: StatementAddress,
    // TODO allocate less
    pub vars: Vec<TokenPtr<'a>>,
}

fn unvector<T>(vec: Option<&Vec<T>>) -> &[T] {
    vec.map(|v| &v[..]).unwrap_or_default()
}


fn min_by<I, CP, GK, K>(iter: I, compare: CP, mut get_key: GK) -> Option<I::Item>
                    where I: IntoIterator, CP: Comparer<K>, GK: FnMut(&I::Item) -> K
{
    iter.into_iter().fold(None, |best, item| {
        match best {
            None => Some(item),
            Some(pbest) => if compare.cmp(&get_key(&item), &get_key(&pbest)) == Ordering::Less {
                Some(item)
            } else {
                Some(pbest)
            }
        }
    })
}

impl<'a> NameReader<'a> {
    pub fn new(nameset: &'a Nameset) -> Self {
        NameReader { nameset: nameset }
    }

    // TODO: add versions which fetch less data, to reduce dep tracking overhead
    pub fn lookup_label(&mut self, label: TokenPtr) -> Option<LookupLabel> {
        let lis = unvector(self.nameset.labels.get(label));
        min_by(lis, &*self.nameset.order, |li| li.address).map(|limin| LookupLabel {
            address: limin.address
        })
    }

    pub fn lookup_symbol(&mut self, symbol: TokenPtr) -> Option<LookupSymbol> {
        let sis = unvector(self.nameset.symbols.get(symbol));
        let min_any = min_by(sis, &*self.nameset.order, |x| x.address);
        let min_const = min_by(sis.iter().filter(|x| x.stype == SymbolType::Constant), &*self.nameset.order, |x| x.address);
        min_any.map(|simin| LookupSymbol {
            stype: simin.stype,
            address: simin.address,
            const_address: min_const.map(|si| si.address),
        })
    }

    // TODO: consider merging this with lookup_symbol
    pub fn lookup_float(&mut self, symbol: TokenPtr) -> Option<LookupFloat<'a>> {
        let fis = unvector(self.nameset.float_types.get(symbol));
        min_by(fis, &*self.nameset.order, |x| x.address).map(|fimin| {
            LookupFloat {
                address: fimin.address,
                label: &fimin.label,
                typecode: &fimin.typecode,
            }
        })
    }

    pub fn lookup_global_dv(&mut self) -> Vec<LookupGlobalDv> {
        self.nameset.dv_info.iter().map(|dvinfo| LookupGlobalDv {
            address: dvinfo.address, vars: dvinfo.vars.iter().map(|x| x as TokenPtr).collect(),
        }).collect()
    }
}