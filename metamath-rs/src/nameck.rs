//! Analysis pass which builds the name to definition index.
//!
//! This is an analysis pass and should not be invoked directly; it is intended
//! to be instantiated through `Database`.  It is not considered a stable API,
//! although a stable wrapper may be added in `Database`.
//!
//! Scope check needs the ability to look up math symbols and statement labels
//! to ensure that they are declared exactly once, and to find the float data
//! for variables.  This pass constructs the hash tables which are used for
//! that.
//!
//! The nameset keeps a global generation number and a generation for each
//! object which can be looked up.  In an analysis pass, you can use
//! `NameReader` to automatically record which objects you have referenced;
//! `NameUsage` can then be used to automatically determine if any of them have
//! changed and if you need to recalculate downstream.
//!
//! The nameset is also responsible for maintaining the `Atom` table.

use crate::database::DbOptions;
use crate::segment::Comparer;
use crate::segment::Segment;
use crate::segment::SegmentOrder;
use crate::segment::SegmentRef;
use crate::segment_set::SegmentSet;
use crate::statement::SegmentId;
use crate::statement::StatementAddress;
use crate::statement::SymbolType;
use crate::statement::Token;
use crate::statement::TokenAddress;
use crate::statement::TokenPtr;
use crate::util::HashMap;
use crate::util::HashSet;
use crate::StatementRef;
use std::borrow::Borrow;
use std::hash::Hash;
use std::sync::Arc;

// An earlier version of this module was tasked with detecting duplicate symbol errors;
// current task is just lookup

/// Opacified number representing a single math symbol.
///
/// An Atom is assigned for every math symbol in the database; Atoms are not
/// lifetime-tracked or ever reused, so they are efficient to handle, but since
/// they cannot be reused when a database is rewritten from scratch this does
/// limit the number of math symbols which can be used in the lifetime of a
/// `database::Database` instance to 2^32-1.
///
/// Atoms are _only_ assigned for names which have been defined in the database,
/// so when checking references it is possible to encounter a name which matches
/// no atom (such a name is necessarily undefined).  It is also possible to
/// match an atom, but then discover the atom is undefined; for instance if it
/// _was_ used in a previous version of the database, but is no longer.  To
/// preserve incremental evaluation hygiene, you must not distinguish these
/// cases.
///
/// Presently, atoms are also allocated for _statement labels_ if `incremental`
/// is true, but not if `incremental` is false.  This is likely to change with
/// [more sophisticated incremental processing][INC]; when this happens, expect
/// a new type like `LAtom` for labels, with `Atom` for symbols only.
///
/// [INC]: https://github.com/sorear/smetamath-rs/issues/11
#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Default, Hash)]
pub struct Atom(u32);

// currently we use Vecs for a lot of things in the index.  we might consider
// changing it to make it more compact in memory, to the end of making database
// clone even cheaper.
type NameSlot<A, V> = Vec<(A, V)>;

// helper functions for handling the name index
fn slot_insert<A, C, V>(slot: &mut NameSlot<A, V>, comparer: &C, address: A, value: V)
where
    C: Comparer<A>,
{
    slot.push((address, value));
    slot.sort_by(|x, y| comparer.cmp(&x.0, &y.0));
}

fn slot_remove<A: Eq, V>(slot: &mut NameSlot<A, V>, address: &A) {
    slot.retain(|x| x.0 != *address);
}

fn autoviv<K: Hash + Eq, V: Default>(map: &mut HashMap<K, V>, key: K) -> &mut V {
    map.entry(key).or_default()
}

fn deviv<K, Q, V, F>(map: &mut HashMap<K, V>, key: &Q, fun: F)
where
    F: FnOnce(&mut V),
    K: Borrow<Q> + Hash + Eq,
    Q: ?Sized + Hash + Eq,
    V: Default + Eq,
{
    let kill = match map.get_mut(key) {
        None => false,
        Some(rval) => {
            fun(rval);
            *rval == Default::default()
        }
    };
    if kill {
        map.remove(key);
    }
}

// that which we keep in the hash slot for math symbols
#[derive(Default, PartialEq, Eq, Debug, Clone)]
struct SymbolInfo {
    atom: Atom,
    // generation is used for recalc tracking
    generation: usize,
    // all=$c $v  constant=$c only (overlaps with all)  float=$f
    all: NameSlot<TokenAddress, SymbolType>,
    constant: NameSlot<TokenAddress, ()>,
    float: NameSlot<StatementAddress, (Token, Token, Atom)>,
}

#[derive(Default, PartialEq, Eq, Debug, Clone)]
struct LabelInfo {
    atom: Atom,
    generation: usize,
    labels: NameSlot<StatementAddress, ()>,
}

#[derive(Default, Debug, Clone)]
struct AtomTable {
    table: HashMap<Token, Atom>,
    reverse: Vec<Token>,
}

fn intern(table: &mut AtomTable, tok: TokenPtr<'_>) -> Atom {
    let next = Atom(table.table.len() as u32 + 1);
    assert!(next.0 < u32::MAX, "atom table overflowed");
    if let Some(&atom) = table.table.get(tok) {
        return atom;
    }
    table.table.insert(tok.into(), next);
    if table.reverse.is_empty() {
        table.reverse.push(Token::default());
    }
    table.reverse.push(tok.into());
    next
}

/// Calculated index mapping names to definitions in a database.
///
/// To extract data from a nameset object, construct a `NameReader` and use the
/// methods thereon.  The reader can then be used at any later time to check
/// recalculation.
#[derive(Default, Debug, Clone)]
pub struct Nameset {
    atom_table: AtomTable,
    options: Arc<DbOptions>,
    order: Arc<SegmentOrder>,

    generation: usize,
    dv_gen: usize,
    segments: HashMap<SegmentId, Arc<Segment>>,
    dv_info: NameSlot<StatementAddress, Vec<Atom>>,
    labels: HashMap<Token, LabelInfo>,
    symbols: HashMap<Token, SymbolInfo>,
}

impl Nameset {
    /// Called by Database to construct a new empty index.
    #[must_use]
    pub fn new() -> Nameset {
        Nameset::default()
    }

    /// Called by Database to bring the index up to date with segment changes.
    pub(crate) fn update(&mut self, segs: &SegmentSet) {
        self.order = segs.order.clone();
        self.generation = self.generation.checked_add(1).unwrap();
        self.options = segs.options.clone();

        // if we still have the exact same segment, keep it.  else remove the
        // old versions and add the new ones.  we are likely to optimize the
        // 1-element case harder in NameSlot later on, so remove first to avoid
        // being temporarily 2x

        let mut keys_to_remove = Vec::new();
        for (&seg_id, seg) in &self.segments {
            if segs
                .segment_opt(seg_id)
                .is_none_or(|sref| !Arc::ptr_eq(sref.segment, seg))
            {
                keys_to_remove.push(seg_id);
            }
        }

        for seg_id in keys_to_remove {
            self.remove_segment(seg_id);
        }

        for sref in segs.segments(..) {
            self.add_segment(sref.id, sref.segment);
        }
    }

    fn add_segment(&mut self, id: SegmentId, segment: &Arc<Segment>) {
        if self.segments.contains_key(&id) {
            return;
        }

        // for each entity in the segment that we're adding: find the slot, bump
        // the generation, add it

        self.segments.insert(id, segment.clone());
        let sref = SegmentRef { segment, id };

        for symdef in &segment.symbols {
            let slot = autoviv(&mut self.symbols, symdef.name.clone());
            slot.generation = self.generation;
            if slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, &symdef.name);
            }
            let address = TokenAddress::new3(id, symdef.start, symdef.ordinal);
            slot_insert(&mut slot.all, &*self.order, address, symdef.stype);
            if symdef.stype == SymbolType::Constant {
                slot_insert(&mut slot.constant, &*self.order, address, ());
            }
        }

        for lsymdef in &segment.local_vars {
            let name = &sref.statement(lsymdef.index).math_at(lsymdef.ordinal);
            intern(&mut self.atom_table, name);
        }

        for labdef in &segment.labels {
            let labelr = sref.statement(labdef.index).label();
            let label = labelr.into();
            let slot = autoviv(&mut self.labels, label);
            slot.generation = self.generation;
            if self.options.incremental && slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, labelr);
            }
            slot_insert(
                &mut slot.labels,
                &*self.order,
                StatementAddress::new(id, labdef.index),
                (),
            );
        }

        for floatdef in &segment.floats {
            let slot = autoviv(&mut self.symbols, floatdef.name.clone());
            slot.generation = self.generation;
            if slot.atom == Atom::default() {
                slot.atom = intern(&mut self.atom_table, &floatdef.name);
            }
            let address = StatementAddress::new(id, floatdef.start);
            let tcatom = intern(&mut self.atom_table, &floatdef.typecode);
            slot_insert(
                &mut slot.float,
                &*self.order,
                address,
                (floatdef.label.clone(), floatdef.typecode.clone(), tcatom),
            );
        }

        for dvdef in &segment.global_dvs {
            let vars = dvdef
                .vars
                .iter()
                .map(|v| intern(&mut self.atom_table, v))
                .collect();
            self.dv_gen = self.generation;
            slot_insert(
                &mut self.dv_info,
                &*self.order,
                StatementAddress::new(id, dvdef.start),
                vars,
            );
        }
    }

    fn remove_segment(&mut self, id: SegmentId) {
        // the reverse of add_segment, except we still bump the generation,
        // don't roll it back
        if let Some(seg) = self.segments.remove(&id) {
            let sref = SegmentRef { segment: &seg, id };
            let gen = self.generation;
            for symdef in &seg.symbols {
                deviv(&mut self.symbols, &symdef.name, |slot| {
                    let address = TokenAddress::new3(id, symdef.start, symdef.ordinal);
                    slot.generation = gen;
                    slot_remove(&mut slot.all, &address);
                    slot_remove(&mut slot.constant, &address);
                });
            }

            for labdef in &seg.labels {
                let label = sref.statement(labdef.index).label();
                deviv(&mut self.labels, label, |slot| {
                    slot.generation = gen;
                    slot_remove(&mut slot.labels, &StatementAddress::new(id, labdef.index));
                });
            }

            for floatdef in &seg.floats {
                deviv(&mut self.symbols, &floatdef.name, |slot| {
                    let address = StatementAddress::new(id, floatdef.start);
                    slot.generation = gen;
                    slot_remove(&mut slot.float, &address);
                });
            }

            for dvdef in &seg.global_dvs {
                self.dv_gen = gen;
                slot_remove(&mut self.dv_info, &StatementAddress::new(id, dvdef.start));
            }
        }
    }

    /// Given a name which is known to represent a defined atom, get the atom.
    ///
    /// If you don't know about the name, use [`lookup_symbol`](Self::lookup_symbol) instead.
    #[must_use]
    #[track_caller]
    pub fn get_atom(&self, name: TokenPtr<'_>) -> Atom {
        *self
            .atom_table
            .table
            .get(name)
            .expect("please only use get_atom for local $v")
    }

    /// Map atoms back to names.
    ///
    /// Since atoms never change over the lifetime of a database container, it
    /// is not necessary to track the dependencies, which is why this lives here
    /// and not on `NameReader`.
    #[must_use]
    pub fn atom_name(&self, atom: Atom) -> TokenPtr<'_> {
        &self.atom_table.reverse[atom.0 as usize]
    }

    /// Looks up the address and atom for a statement label.
    #[must_use]
    pub fn lookup_label(&self, label: TokenPtr<'_>) -> Option<LookupLabel> {
        self.labels.get(label).and_then(|lslot| {
            lslot.labels.first().map(|&(addr, ())| LookupLabel {
                atom: lslot.atom,
                address: addr,
            })
        })
    }

    /// Looks up the address and type for a math symbol.
    #[must_use]
    pub fn lookup_symbol(&self, symbol: TokenPtr<'_>) -> Option<LookupSymbol> {
        self.symbols.get(symbol).and_then(|syminfo| {
            syminfo.all.first().map(|&(addr, stype)| LookupSymbol {
                stype,
                atom: syminfo.atom,
                address: addr,
                const_address: syminfo.constant.first().map(|&(addr, ())| addr),
            })
        })
    }

    /// Looks up the float declaration for a math symbol.
    #[must_use]
    pub fn lookup_float(&self, symbol: TokenPtr<'_>) -> Option<LookupFloatOwned> {
        if let Some(syminfo) = self.symbols.get(symbol) {
            syminfo
                .float
                .first()
                .map(|(addr, (label, _, tcatom))| LookupFloatOwned {
                    statement_atom: self.get_atom(label),
                    address: *addr,
                    typecode_atom: *tcatom,
                })
        } else {
            None
        }
    }

    /// Looks up the label declaration for an atom representing a label.
    /// Atoms are only created and provided for existing labels, so this always returns a value
    #[must_use]
    pub fn lookup_label_by_atom(&self, label_atom: Atom) -> LookupLabel {
        self.lookup_label(self.atom_name(label_atom))
            .expect("Unknown label atom")
    }

    /// Looks up up the address and type for an atom representing a math symbol.
    /// Atoms are only created and provided for existing symbol, so this always returns a value
    #[must_use]
    pub fn lookup_symbol_by_atom(&self, symbol_atom: Atom) -> LookupSymbol {
        self.lookup_symbol(self.atom_name(symbol_atom))
            .expect("Unknown symbol atom")
    }

    /// Looks up the float declaration for an atom representing a math symbol.
    /// Atoms are only created and provided for existing symbol, so this always returns a value
    #[must_use]
    pub fn lookup_float_by_atom(&self, symbol_atom: Atom) -> LookupFloatOwned {
        self.lookup_float(self.atom_name(symbol_atom))
            .expect("Unknown symbol atom")
    }

    /// Looks up the atom from a $f statement.
    #[must_use]
    pub fn var_atom(&self, sref: StatementRef<'_>) -> Option<Atom> {
        self.lookup_symbol(&sref.math_at(1))
            .map(|lookup| lookup.atom)
    }

    /// The name of a statement - utility function to easily print statement names
    #[must_use]
    pub fn statement_name(&self, sref: &StatementRef<'_>) -> TokenPtr<'_> {
        self.atom_name(
            self.lookup_label(sref.label())
                .map_or_else(Atom::default, |l| l.atom),
        )
    }
}

/// A reference to a nameset which can read name mappings while tracking
/// dependencies.
#[derive(Debug)]
pub struct NameReader<'a> {
    nameset: &'a Nameset,
    incremental: bool,
    found_symbol: HashSet<Atom>,
    not_found_symbol: HashSet<Token>,
    found_label: HashSet<Atom>,
    not_found_label: HashSet<Token>,
}

/// Usage data extracted from a `NameReader` at cycle end.
#[derive(Debug)]
pub struct NameUsage {
    generation: usize,
    incremental: bool,
    found_symbol: HashSet<Atom>,
    not_found_symbol: HashSet<Token>,
    found_label: HashSet<Atom>,
    not_found_label: HashSet<Token>,
}

/// A representation of the data which is recorded for each label.
#[derive(Copy, Clone, Debug)]
pub struct LookupLabel {
    /// Address of topmost statement with this label.
    pub address: StatementAddress,
    /// Atom assigned to this label; only valid if incremental=true in options.
    pub atom: Atom,
}

/// A representation of that which is stored for each math symbol.
#[derive(Copy, Clone, Debug)]
pub struct LookupSymbol {
    /// The type of the symbol's topmost defintion.
    pub stype: SymbolType,
    /// The atom assigned to this symbol; unlike for labels, this is always
    /// valid.
    pub atom: Atom,
    /// Address of topmost global $c/$v with this token.
    pub address: TokenAddress,
    /// Address of topmost global $c, if any.
    pub const_address: Option<TokenAddress>,
}

/// A representation of that which is stored for each variable in relation to
/// global $f statements.  All fields apply to the topmost such statement.
#[derive(Clone, Copy, Debug)]
pub struct LookupFloatOwned {
    /// Atom generated for the float statement
    pub statement_atom: Atom,
    /// Address of the $f statement.
    pub address: StatementAddress,
    /// Atom generated for the typecode.
    pub typecode_atom: Atom,
}

/// A representation of that which is stored for each variable in relation to
/// global $f statements.  All fields apply to the topmost such statement.
#[derive(Debug)]
pub struct LookupFloat<'a> {
    /// Address of the $f statement.
    pub address: StatementAddress,
    /// Label of the $f statement.
    pub label: TokenPtr<'a>,
    /// Typecode (the first constant in the $f).
    pub typecode: TokenPtr<'a>,
    /// Atom generated for the typecode.
    pub typecode_atom: Atom,
}

/// Data which can be fetched for each non-nested $d statement.  This is
/// deliberately not well optimized, as set.mm does not use non-nested $d.
#[derive(Debug)]
pub struct LookupGlobalDv<'a> {
    /// Address of the statement.
    pub address: StatementAddress,
    /// Atoms for variables in the statement.
    pub vars: &'a [Atom],
}

impl<'a> NameReader<'a> {
    /// Constructs a reading interface for a nameset and starts recording names
    /// used.
    #[must_use]
    pub fn new(nameset: &'a Nameset) -> Self {
        NameReader {
            nameset,
            incremental: nameset.options.incremental,
            found_symbol: HashSet::default(),
            not_found_symbol: HashSet::default(),
            found_label: HashSet::default(),
            not_found_label: HashSet::default(),
        }
    }

    /// Stops the reading process.  The returned usage object can be used to
    /// efficiently test for relevant updates.
    #[must_use]
    #[allow(clippy::missing_const_for_fn)] // clippy#14294
    pub fn into_usage(self) -> NameUsage {
        NameUsage {
            generation: self.nameset.generation,
            incremental: self.incremental,
            found_symbol: self.found_symbol,
            not_found_symbol: self.not_found_symbol,
            found_label: self.found_label,
            not_found_label: self.not_found_label,
        }
    }

    // TODO(sorear): add versions which fetch less data, to reduce dep tracking overhead

    /// Looks up the address and atom for a statement label.
    pub fn lookup_label(&mut self, label: TokenPtr<'_>) -> Option<LookupLabel> {
        let out = self.nameset.lookup_label(label);
        if self.incremental {
            if let Some(ref lookup) = out {
                self.found_label.insert(lookup.atom);
            } else {
                self.not_found_label.insert(label.into());
            }
        }
        out
    }

    /// Looks up the address and type for a math symbol.
    pub fn lookup_symbol(&mut self, symbol: TokenPtr<'_>) -> Option<LookupSymbol> {
        let out = self.nameset.lookup_symbol(symbol);
        if self.incremental {
            if let Some(ref lookup) = out {
                self.found_symbol.insert(lookup.atom);
            } else {
                self.not_found_symbol.insert(symbol.into());
            }
        }
        out
    }

    // TODO(sorear): consider merging this with lookup_symbol
    /// Looks up the float declaration for a math symbol.
    pub fn lookup_float(&mut self, symbol: TokenPtr<'_>) -> Option<LookupFloat<'a>> {
        if let Some(syminfo) = self.nameset.symbols.get(symbol) {
            if self.incremental {
                self.found_symbol.insert(syminfo.atom);
            }
            syminfo
                .float
                .first()
                .map(|&(addr, (ref label, ref typecode, tcatom))| LookupFloat {
                    address: addr,
                    label,
                    typecode,
                    typecode_atom: tcatom,
                })
        } else {
            if self.incremental {
                self.not_found_symbol.insert(symbol.into());
            }
            None
        }
    }

    /// Looks up the list of all global $d statements.
    #[inline]
    #[must_use]
    pub const fn lookup_global_dv(&self) -> &Vec<(StatementAddress, Vec<Atom>)> {
        &self.nameset.dv_info
    }
}

impl NameUsage {
    /// Check if there have been any observable changes since the usage was
    /// recorded.
    #[must_use]
    pub fn valid(&self, nameset: &Nameset) -> bool {
        if nameset.dv_gen > self.generation {
            // we don't track fine-grained global DV usage
            return false;
        }

        if !self.incremental && nameset.generation > self.generation {
            // not tracking fine-grained deps today
            return false;
        }

        for &atom in &self.found_symbol {
            match nameset.symbols.get(nameset.atom_name(atom)) {
                None => return false,
                Some(infop) => {
                    if infop.generation > self.generation {
                        return false;
                    }
                }
            }
        }

        for name in &self.not_found_symbol {
            if nameset.symbols.contains_key(name) {
                return false;
            }
        }

        for &atom in &self.found_label {
            match nameset.labels.get(nameset.atom_name(atom)) {
                None => return false,
                Some(infop) => {
                    if infop.generation > self.generation {
                        return false;
                    }
                }
            }
        }

        for name in &self.not_found_label {
            if nameset.labels.contains_key(name) {
                return false;
            }
        }

        true
    }
}
