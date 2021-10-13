//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.

// Possibly: Remove branch/leaf and keep only the optional leaf? (then final leaf = no next node id)

use crate::diag::Diagnostic;
use crate::formula::{Formula, FormulaBuilder, Label, Symbol, TypeCode};
use crate::nameck::{Atom, NameReader, Nameset};
use crate::parser::{
    as_str, copy_token, Segment, SegmentId, StatementAddress, StatementRef, StatementType,
    SymbolType, Token,
};
use crate::segment_set::SegmentSet;
use crate::util::{new_map, HashMap};
use log::{debug, warn};
use std::collections::hash_map::Entry;
use std::fmt;
use std::fmt::Formatter;
use std::sync::Arc;
use tinyvec::ArrayVec;

#[cfg(feature = "dot")]
use crate::export::ExportError;
#[cfg(feature = "dot")]
use dot_writer::{Attributes, Color, DotWriter, Shape};
#[cfg(feature = "dot")]
use std::fmt::Write;
#[cfg(feature = "dot")]
use std::fs::File;

/// An index to address [`GrammarNode`]'s
type NodeId = usize;

/// For the labels in DOT format
#[cfg(feature = "dot")]
fn as_string(node_id: NodeId) -> String {
    format!("{}", node_id)
}

/// For the labels in DOT format
#[cfg(feature = "dot")]
fn escape(str: &str) -> String {
    str.replace("\\", "\\\\ ").replace("\"", "\\\"")
}

/// The grammar tree represents a Moore/Mealy Machine, where each node is a state of the automaton,
/// and transitions are made between node based on the input tokens read from the math string to parse.
#[derive(Debug)]
struct GrammarTree(Vec<GrammarNode>);

impl GrammarTree {
    /// Create a new, empty branch node
    fn create_branch(&mut self) -> NodeId {
        self.0.push(GrammarNode::Branch { map: new_map() });
        self.0.len() - 1
    }

    /// Create a new leaf node, with the given [Reduce], and producing the given [Typecode]
    fn create_leaf(&mut self, reduce: Reduce, typecode: TypeCode) -> NodeId {
        self.0.push(GrammarNode::Leaf { reduce, typecode });
        self.0.len() - 1
    }

    /// Retrieves a [`GrammarNode`] structure, given its [`NodeId`].
    fn get(&self, node_id: NodeId) -> &GrammarNode {
        &self.0[node_id]
    }

    /// Retrieves a mutable [`GrammarNode`] structure, given its [`NodeId`].
    fn get_mut(&mut self, node_id: NodeId) -> &mut GrammarNode {
        &mut self.0[node_id]
    }

    /// Returns the total number of nodes in this grammar tree.
    fn len(&self) -> usize {
        self.0.len()
    }

    /// A utility function to return two nodes, one being a mutable one.
    /// This is used to avoid double-borrowing issues when copying grammar tree branches.
    fn get_two_nodes_mut(
        &mut self,
        from_node_id: NodeId,
        to_node_id: NodeId,
    ) -> (&GrammarNode, &mut GrammarNode) {
        if from_node_id < to_node_id {
            let slice = &mut self.0[from_node_id..=to_node_id];
            let (first_part, second_part) = slice.split_at_mut(to_node_id - from_node_id);
            (&first_part[0], &mut second_part[0])
        } else {
            let slice = &mut self.0[to_node_id..=from_node_id];
            let (first_part, second_part) = slice.split_at_mut(from_node_id - to_node_id);
            (&second_part[0], &mut first_part[0])
        }
    }

    // Copy all branches from `from_node` to `to_node`, adding the provided reduce on the way
    fn copy_branches(
        &mut self,
        copy_from_node_id: NodeId,
        copy_to_node_id: NodeId,
        add_reduce: Reduce,
    ) -> Result<(), NodeId> {
        match self.get_two_nodes_mut(copy_from_node_id, copy_to_node_id) {
            (
                GrammarNode::Branch { map },
                GrammarNode::Branch {
                    map: ref mut to_map,
                },
            ) => {
                for (&(stype, symbol), next_node) in map.iter() {
                    match to_map.entry((stype, symbol)) {
                        Entry::Occupied(_) => {
                            // Skip error here, do nothing for now...
                            //return Err(conflict_next_node.next_node_id);
                            //panic!("Conflict when copying constant grammar branches!");
                        }
                        Entry::Vacant(e) => {
                            if stype == SymbolType::Variable {
                                e.insert(next_node.with_offset_reduce(add_reduce));
                            } else {
                                e.insert(next_node.with_reduce(add_reduce));
                            }
                        }
                    }
                }
                Ok(())
            }
            _ => Err(copy_to_node_id),
        }
    }
}

/// The grammar built from the database's syntactic axioms
///
/// It is used to parse metamath statements into [Formula].
/// See [`StmtParse`] for getting the formula for statements from the database.
///
/// Example:
/// ```
/// use metamath_knife::database::{Database, DbOptions};
///
/// // Setup the required options
/// let mut options = DbOptions::default();
/// options.autosplit = true;
/// options.jobs = 8;
/// options.incremental = true;
///
/// // Create an empty database and load any file provided
/// let mut db = Database::new(options);
/// db.parse("set.mm".to_string(), vec![]);
/// let grammar = db.grammar_result();
/// ```
#[derive(Debug)]
pub struct Grammar {
    provable_type: TypeCode,
    logic_type: TypeCode,
    typecodes: Vec<TypeCode>,
    nodes: GrammarTree,
    root: NodeId, // The root of the Grammar tree
    diagnostics: HashMap<StatementAddress, Diagnostic>,
    debug: bool,
}

/// A `Reduce` step applies a completed grammar rule to some of the recent parse trees,
/// joining them together as one tree with a new root symbol.
///
/// - `label` is the syntax axiom being applied.
/// - `var_count` is the number of variables this syntax axiom requires. This tells how many of the parse trees will be joined.
/// - `offset` says how far in the stack of yet un-joined parse trees the reduce will join. The cases when this is non-zero are rare.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
struct Reduce {
    label: Label,
    var_count: u8,
    offset: u8,
    is_variable: bool,
}

impl Reduce {
    const fn new(label: Label, var_count: u8) -> Self {
        Reduce {
            label,
            var_count,
            offset: 0,
            is_variable: false,
        }
    }

    const fn new_variable(label: Label) -> Self {
        Reduce {
            label,
            var_count: 0,
            offset: 0,
            is_variable: true,
        }
    }
}

/// With the current implementation, up to 5 reduce steps can be done in a single transition.
/// This limit is hard-coded here.
type ReduceVec = ArrayVec<[Reduce; 5]>;

/// Builds a list of `reduce`s with a single entry.
fn single_reduce(r: Reduce) -> ReduceVec {
    let mut reduce_vec = ReduceVec::new();
    reduce_vec.push(r);
    reduce_vec
}

/// Increments the offets of the `reduce`s in the given list.
fn increment_offsets(rv: &mut ReduceVec) {
    for ref mut reduce in rv {
        reduce.offset += 1;
    }
}

#[derive(Clone, Copy, Debug)]
struct NextNode {
    next_node_id: NodeId,
    leaf_label: ReduceVec, // This deals with ambiguity in the grammar, performing one or several reduce then continuing
}

impl NextNode {
    fn new(next_node_id: NodeId) -> Self {
        NextNode {
            next_node_id,
            leaf_label: ReduceVec::new(),
        }
    }

    const fn new_with_reduce_vec(next_node_id: NodeId, leaf_label: ReduceVec) -> Self {
        NextNode {
            next_node_id,
            leaf_label,
        }
    }

    fn with_offset_reduce(&self, reduce: Reduce) -> Self {
        let mut r = reduce;
        r.offset += 1;
        let mut leaf_label = self.leaf_label;
        leaf_label.insert(0, r);
        NextNode {
            next_node_id: self.next_node_id,
            leaf_label,
        }
    }

    fn with_reduce(&self, reduce: Reduce) -> Self {
        let mut leaf_label = self.leaf_label;
        leaf_label.insert(0, reduce);
        NextNode {
            next_node_id: self.next_node_id,
            leaf_label,
        }
    }

    fn with_reduce_vec(&self, reduce_vec: &ReduceVec) -> Self {
        let mut leaf_label = self.leaf_label;
        for reduce in reduce_vec {
            leaf_label.push(*reduce);
        }
        NextNode {
            next_node_id: self.next_node_id,
            leaf_label,
        }
    }
}

#[derive(Clone, Debug)]
#[allow(variant_size_differences)]
enum GrammarNode {
    Leaf {
        reduce: Reduce,
        typecode: TypeCode,
    },
    Branch {
        // Table of choices leading to the next node when a constant/variable is encountered
        map: HashMap<(SymbolType, Atom), NextNode>,
    },
}

impl GrammarNode {
    /// Next node
    fn next_node(&self, symbol: Symbol, stype: SymbolType) -> Option<&NextNode> {
        match self {
            GrammarNode::Leaf { .. } => None,
            GrammarNode::Branch { map } => map.get(&(stype, symbol)),
        }
    }
}

struct GrammarNodeDebug<'a>(&'a GrammarNode, &'a Arc<Nameset>);
impl fmt::Debug for GrammarNodeDebug<'_> {
    /// Lists the contents of the grammar node
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let nset = self.1;
        match self.0 {
            GrammarNode::Leaf { reduce, typecode } => {
                write!(
                    f,
                    "Leaf {} {} ({} vars)",
                    as_str(nset.atom_name(*typecode)),
                    as_str(nset.atom_name(reduce.label)),
                    reduce.var_count
                )
            }
            GrammarNode::Branch { map } => {
                write!(f, "Branch {{")?;
                for (key, node) in map {
                    match key {
                        (SymbolType::Constant, symbol) => {
                            write!(
                                f,
                                "CST {}: {:?}",
                                as_str(nset.atom_name(*symbol)),
                                node.next_node_id
                            )?;
                            for reduce in node.leaf_label {
                                write!(
                                    f,
                                    "({:?} {})",
                                    as_str(nset.atom_name(reduce.label)),
                                    reduce.var_count
                                )?;
                            }
                            write!(f, ", ")?;
                        }
                        (SymbolType::Variable, typecode) => {
                            write!(
                                f,
                                "VAR {}: {:?}",
                                as_str(nset.atom_name(*typecode)),
                                node.next_node_id
                            )?;
                            for reduce in node.leaf_label {
                                write!(
                                    f,
                                    "({:?} {})",
                                    as_str(nset.atom_name(reduce.label)),
                                    reduce.var_count
                                )?;
                            }
                            write!(f, ", ")?;
                        }
                    }
                }
                write!(f, "}}")
            }
        }
    }
}

struct GrammarNodeIdDebug<'a>(&'a Grammar, NodeId, &'a Arc<Nameset>);
impl fmt::Debug for GrammarNodeIdDebug<'_> {
    /// Lists the contents of the grammar node, given the grammar and a node id
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let grammar = self.0;
        let node_id = self.1;
        let nset = self.2;
        write!(
            f,
            "{}: {:?}",
            node_id,
            GrammarNodeDebug(&grammar.nodes.0[node_id], nset)
        )
    }
}

impl Default for Grammar {
    fn default() -> Self {
        Grammar {
            provable_type: TypeCode::default(),
            logic_type: TypeCode::default(),
            typecodes: Vec::new(),
            nodes: GrammarTree(Vec::new()),
            root: 0,
            diagnostics: new_map(),
            debug: false,
        }
    }
}

impl Grammar {
    /// Initializes the grammar using the parser commands
    fn initialize(&mut self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) {
        for (_, command) in sset.parser_commands() {
            assert!(!command.is_empty(), "Empty parser command!");
            if &command[0].as_ref() == b"syntax" {
                if command.len() == 4 && &command[2].as_ref() == b"as" {
                    // syntax '|-' as 'wff';
                    self.provable_type = nset.lookup_symbol(&command[1]).unwrap().atom;
                    self.logic_type = nset.lookup_symbol(&command[3]).unwrap().atom;
                    self.typecodes.push(self.logic_type);
                } else if command.len() == 2 {
                    // syntax 'setvar';
                    self.typecodes
                        .push(nset.lookup_symbol(&command[1]).unwrap().atom);
                }
            }
        }
    }

    /// Returns a list of errors that were generated during the grammar
    /// computation.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sa, diag) in &self.diagnostics {
            out.push((*sa, diag.clone()));
        }
        out
    }

    /// Creates an "Ambiguous" diagnostic for the grammar
    /// The node given is the other node found with the same syntax.
    /// We're looking for any label in that branch.
    fn ambiguous(&self, start_node: NodeId, nset: &Arc<Nameset>) -> Diagnostic {
        let mut node = start_node;
        loop {
            match self.nodes.get(node) {
                GrammarNode::Branch { map, .. } => {
                    // It shall be safe to unwrap here, as we shall never insert a branch without a leaf
                    node = map.values().next().unwrap().next_node_id;
                }
                GrammarNode::Leaf { reduce, .. } => {
                    let sa = nset
                        .lookup_label(nset.atom_name(reduce.label))
                        .unwrap()
                        .address;
                    return Diagnostic::GrammarAmbiguous(sa);
                }
            }
        }
    }

    fn too_short(map: &HashMap<(SymbolType, Atom), NextNode>, nset: &Arc<Nameset>) -> Diagnostic {
        let expected_symbol = map.keys().find(|k| k.0 == SymbolType::Constant).unwrap().1;
        let expected_token = copy_token(nset.atom_name(expected_symbol));
        Diagnostic::ParsedStatementTooShort(expected_token)
    }

    /// Gets the map of a branch
    fn get_branch(&self, node_id: NodeId) -> &HashMap<(SymbolType, Atom), NextNode> {
        if let GrammarNode::Branch { map } = &self.nodes.get(node_id) {
            map
        } else {
            panic!("Expected branch for node {}!", node_id);
        }
    }

    /// Adds the symbol to the branch, providing the next node, and returns that next node
    fn add_branch(
        &mut self,
        to_node: NodeId,
        symbol: Symbol,
        stype: SymbolType,
        leaf: &NextNode,
    ) -> Result<NodeId, NodeId> {
        match self.nodes.get_mut(to_node) {
            GrammarNode::Leaf { .. } => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
            GrammarNode::Branch { map } => {
                if let Some(prev_node) = map.get(&(stype, symbol)) {
                    Err(prev_node.next_node_id)
                } else {
                    map.insert((stype, symbol), *leaf);
                    Ok(leaf.next_node_id)
                }
            }
        }
    }

    /// Adds the symbol to the branch, providing a reduce, and returns the next node
    fn add_branch_with_reduce(
        &mut self,
        to_node: NodeId,
        symbol: Symbol,
        stype: SymbolType,
        add_reduce: ReduceVec,
    ) -> Result<NodeId, NodeId> {
        match self.nodes.get_mut(to_node) {
            GrammarNode::Leaf { .. } => {
                Err(to_node) // Error: cannot add to a leaf node, `to_node` is the conflicting node
            }
            GrammarNode::Branch { map } => {
                match map.get(&(stype, symbol)) {
                    Some(prev_node) if prev_node.leaf_label == add_reduce => {
                        Ok(prev_node.next_node_id)
                    }
                    Some(prev_node) => Err(prev_node.next_node_id),
                    None => {
                        let new_node_id = self.nodes.create_branch();
                        // here we have to re-borrow from self after the creation,
                        // because the previous var_map and cst_map may not be valid pointers anymore
                        if let GrammarNode::Branch { map } = self.nodes.get_mut(to_node) {
                            map.insert(
                                (stype, symbol),
                                NextNode::new_with_reduce_vec(new_node_id, add_reduce),
                            );
                            Ok(new_node_id)
                        } else {
                            panic!("Shall not happen!");
                        }
                    }
                }
            }
        }
    }

    /// Build the parse tree, marking variables with their types
    fn add_axiom(
        &mut self,
        sref: &StatementRef<'_>,
        nset: &Arc<Nameset>,
        names: &mut NameReader<'_>,
        type_conversions: &mut Vec<(TypeCode, TypeCode, Label)>,
    ) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter().peekable();

        // Atom for this axiom's label.
        let this_label = names.lookup_label(sref.label()).unwrap().atom;
        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let this_typecode = nset.get_atom(tokens.next().unwrap().slice);

        // In case of a non-syntax axiom, skip it.
        if this_typecode == self.provable_type {
            return Ok(());
        }

        // Detect "type conversion" syntax axioms: ~cv for set.mm
        if sref.math_len() == 2 {
            let token_ptr = sref.math_at(1).slice;
            let symbol = names.lookup_symbol(token_ptr).unwrap();
            if symbol.stype == SymbolType::Variable {
                let from_typecode = match names.lookup_float(token_ptr) {
                    Some(lookup_float) => lookup_float.typecode_atom,
                    _ => {
                        return Err(Diagnostic::VariableMissingFloat(1));
                    }
                };
                type_conversions.push((from_typecode, this_typecode, this_label));
                return Ok(()); // we don't need to add the type conversion axiom itself to the grammar (or do we?)
            }
        }

        // We will add this syntax axiom to the grammar tree
        let mut node = self.root;
        let mut var_count = 0;
        while let Some(token) = tokens.next() {
            let symbol = names.lookup_symbol(token.slice).unwrap();
            let atom = match symbol.stype {
                SymbolType::Constant => symbol.atom,
                SymbolType::Variable => {
                    var_count += 1;
                    // We need a second lookup to find out the typecode of a floating variable...
                    // Ideally this information would be included in the LookupSymbol
                    names.lookup_float(token.slice).unwrap().typecode_atom
                }
            };
            match match &tokens.peek() {
                Some(_) => self.add_branch_with_reduce(node, atom, symbol.stype, ReduceVec::new()),
                None => {
                    let leaf_node_id = self
                        .nodes
                        .create_leaf(Reduce::new(this_label, var_count), this_typecode);
                    self.add_branch(node, atom, symbol.stype, &NextNode::new(leaf_node_id))
                }
            } {
                Ok(next_node) => {
                    node = next_node;
                }
                Err(conflict_node) => {
                    return Err(self.ambiguous(conflict_node, nset));
                }
            }
        }
        Ok(())
    }

    /// Add a floating variable node to the parse tree.
    fn add_floating(
        &mut self,
        sref: &StatementRef<'_>,
        nset: &Arc<Nameset>,
        names: &mut NameReader<'_>,
    ) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter();

        // Atom for this flaot's label.
        let this_label = names.lookup_label(sref.label()).unwrap().atom;
        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let this_typecode = nset.get_atom(tokens.next().unwrap().slice);

        // Float shall not be of the provable typecode.
        if this_typecode == self.provable_type {
            return Err(Diagnostic::GrammarProvableFloat);
        }

        // We will add this floating declaration to the grammar tree
        let leaf_node = self
            .nodes
            .create_leaf(Reduce::new_variable(this_label), this_typecode);

        // If is safe to unwrap here since parser has already checked.
        let token = tokens.next().unwrap();
        let symbol = names
            .lookup_symbol(token.slice)
            .ok_or(Diagnostic::FloatNotVariable(1))?;

        debug!(
            "========== Statement {:?} ==========",
            as_str(nset.statement_name(sref))
        );

        match self.nodes.get_mut(self.root) {
            // We ignore the ambiguity in floats, since they are actually frame dependent.
            GrammarNode::Branch { map } => {
                map.insert(
                    (SymbolType::Constant, symbol.atom),
                    NextNode::new(leaf_node),
                );
                Ok(())
                // match cst_map.insert(symbol.atom, NextNode::new(leaf_node)) {
                //     None => Ok(()),
                //     Some(_) => Err(self.ambiguous(conflict_node.next_node_id, nset)),
                // }
            }
            GrammarNode::Leaf { .. } => panic!("Root node shall be a branch node!"),
        }
    }

    /// Handle type conversion:
    /// Go through each node and everywhere there is
    /// `to_typecode` (`class`), put a `from_typecode` (`setvar`),
    /// pointing to a copy of the next node with a leaf to first do a `cv`
    #[allow(clippy::unnecessary_wraps)]
    fn perform_type_conversion(
        &mut self,
        from_typecode: TypeCode,
        to_typecode: TypeCode,
        label: Label,
        nset: &Arc<Nameset>,
    ) -> Result<(), Diagnostic> {
        let len = self.nodes.len();
        for node_id in 0..len {
            if let GrammarNode::Branch { map } = self.nodes.get(node_id) {
                if let Some(ref_next_node) = map.get(&(SymbolType::Variable, to_typecode)) {
                    let next_node_id = ref_next_node.next_node_id;
                    match map.get(&(SymbolType::Variable, from_typecode)) {
                        None => {
                            // No branch exist for the converted type: create one, with a leaf label.
                            debug!("Type Conv adding to {} node id {}", node_id, next_node_id);
                            debug!("{:?}", GrammarNodeIdDebug(self, node_id, nset));
                            let mut leaf_label = ref_next_node.leaf_label;
                            leaf_label.insert(0, Reduce::new(label, 1));
                            self.add_branch(
                                node_id,
                                from_typecode,
                                SymbolType::Variable,
                                &NextNode {
                                    next_node_id,
                                    leaf_label,
                                },
                            )
                            .unwrap();
                        }
                        Some(existing_next_node) => {
                            // A branch for the converted type already exist: add the conversion to that branch!
                            debug!(
                                "Type Conv copying to {} node id {}",
                                next_node_id, existing_next_node.next_node_id
                            );
                            debug!("{:?}", GrammarNodeIdDebug(self, next_node_id, nset));
                            debug!(
                                "{:?}",
                                GrammarNodeIdDebug(self, existing_next_node.next_node_id, nset)
                            );
                            let existing_next_node_id = existing_next_node.next_node_id;
                            self.nodes
                                .copy_branches(
                                    next_node_id,
                                    existing_next_node_id,
                                    Reduce::new(label, 1),
                                )
                                .unwrap();
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn next_var_node(&self, node_id: NodeId, typecode: TypeCode) -> Option<(NodeId, &ReduceVec)> {
        match self.nodes.get(node_id) {
            GrammarNode::Branch { map } => match map.get(&(SymbolType::Variable, typecode)) {
                Some(NextNode {
                    next_node_id,
                    leaf_label,
                }) => Some((*next_node_id, leaf_label)),
                _ => None,
            },
            GrammarNode::Leaf { .. } => None,
        }
    }

    /// Recursively clone the whole grammar tree starting from `add_from_node_id`
    // This implementation may needlessly duplicate some nodes: it creates new ones everytime,
    // not checking if a duplicate was already created and could be reused.
    // A cleverer implementation would store the duplicates created, for example in a hashmap,
    // and reuse them.
    // Branch nodes are recursively copied.
    // The `make_final` argument is a function building the final node from the reduce
    // of the found leaf node and the final typecode.
    fn clone_branches<F>(
        &mut self,
        add_from_node_id: NodeId,
        add_to_node_id: NodeId,
        nset: &Arc<Nameset>,
        mut stored_reduces: ReduceVec,
        make_final: F,
    ) where
        F: FnOnce(&ReduceVec, TypeCode) -> NextNode + Copy,
    {
        debug!("Clone {} to {}", add_from_node_id, add_to_node_id);
        debug!("{:?}", GrammarNodeIdDebug(self, add_from_node_id, nset));
        debug!("{:?}", GrammarNodeIdDebug(self, add_to_node_id, nset));
        let map = &self.get_branch(add_from_node_id).clone(); // can we prevent cloning here?
        for &stype in &[SymbolType::Constant, SymbolType::Variable] {
            if stype == SymbolType::Variable {
                increment_offsets(&mut stored_reduces);
            }
            for (&(stype2, symbol), next_node) in map {
                if stype != stype2 {
                    continue;
                }
                if next_node.next_node_id == add_to_node_id {
                    // avoid infinite recursion
                    continue;
                }
                if let GrammarNode::Leaf {
                    reduce: ref r,
                    typecode,
                } = *self.nodes.get(next_node.next_node_id)
                {
                    let mut reduce_vec = ReduceVec::new();
                    for reduce in stored_reduces {
                        reduce_vec.push(reduce);
                    }
                    reduce_vec.push(*r);
                    debug!(
                        "LEAF for {} to {} {:?}",
                        add_from_node_id, add_to_node_id, reduce_vec
                    );
                    let final_node = make_final(&reduce_vec, typecode);
                    match self.add_branch(add_to_node_id, symbol, stype, &final_node) {
                        Ok(_) => {}
                        Err(conflict_node_id) => {
                            debug!("Conflict Node = {}", conflict_node_id);
                            // conflict node id = 394 : CST={): 395, } VAR={}
                            // next_node_id = 16: CST={\/: 23, <->: 20, -/\: 35, /\: 26, ->: 17, \/_: 38, } VAR={}
                            // reduce = wbr 3
                            // expected result: 394 : CST={): 395, \/: (wbr 3) 23, <->: (wbr 3) 20, ...} VAR={}
                            self.clone_with_reduce_vec(
                                final_node.next_node_id,
                                conflict_node_id,
                                &reduce_vec,
                            );
                        }
                    }
                } else {
                    debug!(
                        "BRANCH for {} to {} {:?}",
                        add_from_node_id, add_to_node_id, next_node.leaf_label
                    );
                    let (new_next_node_id, new_stored_reduces) = match self.add_branch_with_reduce(
                        add_to_node_id,
                        symbol,
                        stype,
                        next_node.leaf_label,
                    ) {
                        Ok(new_next_node_id) => (new_next_node_id, stored_reduces),
                        Err(new_next_node_id) => {
                            let mut new_stored_reduces = stored_reduces;
                            // This is the case where there is already a branch, with a different reduce.
                            // In that case, we have to store the reduce until the copy is finished.
                            for reduce in next_node.leaf_label {
                                debug!(">> Storing {:?}", reduce);
                                new_stored_reduces.push(reduce);
                            }
                            (new_next_node_id, new_stored_reduces)
                        }
                    };
                    self.clone_branches(
                        next_node.next_node_id,
                        new_next_node_id,
                        nset,
                        new_stored_reduces,
                        make_final,
                    );
                }
            }
        }
    }

    // compare this with "copy_branches"!
    fn clone_with_reduce_vec(
        &mut self,
        add_from_node_id: NodeId,
        add_to_node_id: NodeId,
        reduce_vec: &ReduceVec,
    ) {
        if add_from_node_id == add_to_node_id {
            // nothing to clone here!
            return;
        }
        debug!(
            "Clone with reduce {} to {}",
            add_from_node_id, add_to_node_id
        );
        let map = &self.get_branch(add_from_node_id).clone(); // can we prevent cloning here?
        for (&(stype, symbol), next_node) in map {
            self.add_branch(
                add_to_node_id,
                symbol,
                stype,
                &next_node.with_reduce_vec(reduce_vec),
            )
            .expect("Double conflict!");
        }
    }

    /// Expand the tree at the given node, for the given symbol.  This means cloning/inserting from the root tree at that symbol, until a given typecode is obtained, into the given node
    /// This is used in order to ensure that a given sequence is in the grammar tree, like `<. <.`, which does not correspond to a single syntax axiom
    fn expand_tree(
        &mut self,
        to_node: NodeId,
        symbol: Symbol,
        stype: SymbolType,
        nset: &Arc<Nameset>,
    ) -> NodeId {
        let next_node_id_from_root = self
            .nodes
            .get(self.root)
            .next_node(symbol, stype)
            .expect("Expanded formula cannot be parsed from root node!")
            .next_node_id;
        let node_from_root = self.nodes.get(next_node_id_from_root).clone();
        let new_node_id = self
            .add_branch_with_reduce(to_node, symbol, stype, ReduceVec::new())
            .unwrap();
        self.clone_branches(
            next_node_id_from_root,
            new_node_id,
            nset,
            ReduceVec::new(),
            |rv, t| {
                node_from_root
                    .next_node(t, SymbolType::Variable)
                    .expect("Expanded node's typecode not available!")
                    .with_reduce_vec(rv)
            },
        );
        self.nodes
            .get(to_node)
            .next_node(symbol, stype)
            .unwrap()
            .next_node_id
    }

    /// Handle common prefixes (garden paths).
    /// For example in set.mm, ` (  A ` is a prefix common to ` ( A X. B ) ` and ` ( A e. B /\ T. ) `
    /// The first is a notation, but would "shadow" the second option.
    /// The command `garden_path ( A   =>   ( ph ;` handles this.
    ///
    // NOTE:
    //    Common prefix must be constant only, and both first differing symbols must be variables
    #[allow(clippy::unnecessary_wraps)]
    fn handle_common_prefixes(
        &mut self,
        prefix: &[Token],
        shadows: &[Token],
        nset: &Arc<Nameset>,
        names: &mut NameReader<'_>,
    ) -> Result<(), Diagnostic> {
        let mut node_id = self.root;
        let mut index = 0;

        // First we follow the tree to the common prefix
        loop {
            if prefix[index] != shadows[index] {
                break;
            }
            // TODO(tirix): use https://rust-lang.github.io/rfcs/2497-if-let-chains.html once it's out!
            if let GrammarNode::Branch { map } = self.nodes.get(node_id) {
                let prefix_symbol = nset.lookup_symbol(prefix[index].as_ref()).unwrap().atom;
                let next_node = map
                    .get(&(SymbolType::Constant, prefix_symbol))
                    .expect("Prefix cannot be parsed!");
                node_id = next_node.next_node_id;
                index += 1;
            } else {
                panic!("Leaf reached while parsing common prefixes!");
            }
        }

        // We note the typecode and next branch of the "shadowed" prefix
        let shadowed_typecode = names.lookup_float(&shadows[index]).unwrap().typecode_atom;
        let (shadowed_next_node, _) = self
            .next_var_node(node_id, shadowed_typecode)
            .expect("Shadowed prefix cannot be parsed!");

        // We note what comes after the shadowing typecode, both if we start from the prefix and if we start from the root
        let mut add_from_node_id = self.root;
        let mut shadowing_atom: Atom;
        let mut shadowing_stype;
        for token in &prefix[index..] {
            let lookup_symbol = names.lookup_symbol(token).unwrap();
            debug!(
                "Following prefix {}, at {} / {}",
                as_str(token),
                node_id,
                add_from_node_id
            );
            shadowing_stype = lookup_symbol.stype;
            shadowing_atom = match shadowing_stype {
                SymbolType::Constant => lookup_symbol.atom,
                SymbolType::Variable => names.lookup_float(token).unwrap().typecode_atom,
            };
            node_id = self
                .nodes
                .get(node_id)
                .next_node(shadowing_atom, shadowing_stype)
                .expect("Prefix cannot be parsed!")
                .next_node_id;
            add_from_node_id = match self
                .nodes
                .get(add_from_node_id)
                .next_node(shadowing_atom, shadowing_stype)
            {
                Some(next_node) => next_node.next_node_id,
                None => self.expand_tree(add_from_node_id, shadowing_atom, shadowing_stype, nset),
            }
        }

        debug!("Shadowed token: {}", as_str(&shadows[index]));
        debug!(
            "Handle shadowed next node {}, typecode {:?}",
            shadowed_next_node, shadowed_typecode
        );
        debug!(
            "Handle shadowed next node from root {}, typecode {:?}",
            add_from_node_id, shadowed_typecode
        );
        debug!("Handle shadowing next node {}", node_id);

        // Then we copy each of the next branch of the shadowed string to the shadowing branch
        // If the next node is a leaf, instead, we add a leaf label, and point to the next
        let make_final = |rv: &ReduceVec, _| NextNode {
            next_node_id: shadowed_next_node,
            leaf_label: *rv,
        };
        match self.nodes.get(add_from_node_id) {
            GrammarNode::Branch { .. } => {
                self.clone_branches(
                    add_from_node_id,
                    node_id,
                    nset,
                    ReduceVec::new(),
                    make_final,
                );
            }
            GrammarNode::Leaf { reduce, .. } => {
                let rv = single_reduce(*reduce);
                self.clone_with_reduce_vec(shadowed_next_node, node_id, &rv);
            }
        }

        Ok(())
    }

    /// Bake the lookahead into the grammar automaton.
    /// This handles casses like the ambiguity between ` ( x e. A /\ ph ) ` and ` ( x e. A |-> B ) `
    /// which share a common prefix, and can only be distinguished after the 5th token is read.
    /// This is dealt with by introducing branch nodes where the optional leaf is set,
    /// which lead to partial reduce.
    /// In the example case, at the 5th token `/\`, this method modifies the grammar tree
    /// by adding the optional "wcel" reduce to the corresponding tree node.
    ///
    /// Here is how the commands are to be included into the metamath file:
    /// `
    ///   $( Warn the parser about which particular formula prefixes are ambiguous $)
    ///   $( $j garden_path ( A   =>   ( ph ;
    ///         type_conversions;
    ///         garden_path ( x e. A   =>   ( ph ;
    ///         garden_path { <.   =>   { A ;
    ///         garden_path { <. <.   =>   { A ;
    ///   $)
    /// `
    fn handle_commands(
        &mut self,
        sset: &Arc<SegmentSet>,
        nset: &Arc<Nameset>,
        names: &mut NameReader<'_>,
        type_conversions: &[(TypeCode, TypeCode, Label)],
    ) -> Result<(), (StatementAddress, Diagnostic)> {
        for (address, command) in sset.parser_commands() {
            assert!(!command.is_empty(), "Empty parser command!");
            if &command[0].as_ref() == b"syntax" {
                if command.len() == 4 && &command[2].as_ref() == b"as" {
                    // syntax '|-' as 'wff';
                    self.provable_type = nset.lookup_symbol(&command[1]).unwrap().atom;
                    self.typecodes
                        .push(nset.lookup_symbol(&command[3]).unwrap().atom);
                } else if command.len() == 2 {
                    // syntax 'setvar';
                    self.typecodes
                        .push(nset.lookup_symbol(&command[1]).unwrap().atom);
                }
            }
            // Handle Ambiguous prefix commands
            if &command[0].as_ref() == b"garden_path" {
                let split_index = command
                    .iter()
                    .position(|t| t.as_ref() == b"=>")
                    .expect("'=>' not present in 'garden_path' command!");
                let (prefix, shadows) = command.split_at(split_index);
                if let Err(diag) =
                    self.handle_common_prefixes(&prefix[1..], &shadows[1..], nset, names)
                {
                    return Err((address, diag));
                }
            }
            // Handle replacement schemes
            if &command[0].as_ref() == b"type_conversions" {
                for (from_typecode, to_typecode, label) in type_conversions {
                    if let Err(diag) =
                        self.perform_type_conversion(*from_typecode, *to_typecode, *label, nset)
                    {
                        return Err((address, diag));
                    }
                }
            }
        }
        Ok(())
    }

    fn do_shift(
        &self,
        symbol_iter: &mut dyn Iterator<Item = (usize, Symbol)>,
        nset: &Arc<Nameset>,
    ) {
        if let Some((_ix, symbol)) = symbol_iter.next() {
            if self.debug {
                debug!("   SHIFT {:?}", as_str(nset.atom_name(symbol)));
            }
        }
    }

    fn do_reduce(formula_builder: &mut FormulaBuilder, reduce: Reduce, nset: &Arc<Nameset>) {
        debug!("   REDUCE {:?}", as_str(nset.atom_name(reduce.label)));
        formula_builder.reduce(
            reduce.label,
            reduce.var_count,
            reduce.offset,
            reduce.is_variable,
        );
        //formula_builder.dump(nset);
        debug!(
            " {:?} {} {}",
            as_str(nset.atom_name(reduce.label)),
            reduce.var_count,
            reduce.offset
        );
    }

    /// Parses the given list of symbols into a formula syntax tree.
    pub fn parse_formula(
        &self,
        symbol_iter: &mut dyn Iterator<Item = Symbol>,
        expected_typecodes: Box<[TypeCode]>,
        nset: &Arc<Nameset>,
    ) -> Result<Formula, Diagnostic> {
        struct StackElement {
            node_id: NodeId,
            expected_typecodes: Box<[TypeCode]>,
        }

        let mut formula_builder = FormulaBuilder::default();
        let mut symbol_enum = symbol_iter.enumerate().peekable();
        let mut ix;
        let mut e = StackElement {
            node_id: self.root,
            expected_typecodes,
        };
        let mut stack = vec![];
        loop {
            match *self.nodes.get(e.node_id) {
                GrammarNode::Leaf { reduce, typecode } => {
                    // We found a leaf: REDUCE
                    Self::do_reduce(&mut formula_builder, reduce, nset);

                    if e.expected_typecodes.contains(&typecode) {
                        // We found an expected typecode, pop from the stack and continue
                        if let Some(popped) = stack.pop() {
                            e = popped;
                            debug!(
                                " ++ Finished parsing formula, found typecode {:?}, back to {}",
                                as_str(nset.atom_name(typecode)),
                                e.node_id
                            );
                            let map = self.get_branch(e.node_id);
                            match map.get(&(SymbolType::Variable, typecode)) {
                                Some(NextNode {
                                    next_node_id,
                                    leaf_label,
                                }) => {
                                    // Found a sub-formula: First optionally REDUCE and continue
                                    for &reduce in leaf_label {
                                        Self::do_reduce(&mut formula_builder, reduce, nset);
                                    }

                                    e.node_id = *next_node_id;
                                    debug!("   Next Node: {:?}", e.node_id);
                                }
                                None => {
                                    debug!("TODO");
                                }
                            }
                        } else if symbol_enum.peek().is_none() {
                            // We popped the last element from the stack and we are at the end of the math string, success
                            return Ok(formula_builder.build(typecode));
                        } else {
                            // There are still symbols to parse, continue from root
                            let (next_node_id, leaf_label) =
                                self.next_var_node(self.root, typecode).unwrap(); // TODO(tirix): error case
                            for &reduce in leaf_label {
                                Self::do_reduce(&mut formula_builder, reduce, nset);
                            }
                            e.node_id = next_node_id;
                        }
                    } else {
                        // We have not found the expected typecode, continue from root
                        debug!(" ++ Wrong type obtained, continue.");
                        let (next_node_id, leaf_label) =
                            self.next_var_node(self.root, typecode).unwrap(); // TODO(tirix): error case
                        for &reduce in leaf_label {
                            Self::do_reduce(&mut formula_builder, reduce, nset);
                        }
                        e.node_id = next_node_id;
                    }
                }
                GrammarNode::Branch { ref map } => {
                    if let Some(&(index, symbol)) = symbol_enum.peek() {
                        ix = index as i32;
                        debug!("   {:?}", as_str(nset.atom_name(symbol)));

                        if let Some(NextNode {
                            next_node_id,
                            leaf_label,
                        }) = map.get(&(SymbolType::Constant, symbol))
                        {
                            // Found an atom matching one of our next nodes: First optionally REDUCE and continue
                            for &reduce in leaf_label {
                                Self::do_reduce(&mut formula_builder, reduce, nset);
                            }

                            // Found an atom matching one of our next nodes: SHIFT, to the next node
                            self.do_shift(&mut symbol_enum, nset);
                            e.node_id = *next_node_id;
                            debug!("   Next Node: {:?}", e.node_id);
                        } else {
                            // No matching constant, search among variables
                            if map.is_empty() || e.node_id == self.root {
                                return Err(Diagnostic::UnparseableStatement(ix));
                            }

                            debug!(
                                " ++ Not in CST map, push stack element and expect {:?}",
                                map.keys()
                            );
                            stack.push(e);
                            e = StackElement {
                                node_id: self.root,
                                expected_typecodes: map
                                    .keys()
                                    .filter_map(|k| match *k {
                                        (SymbolType::Variable, typecode) => Some(typecode),
                                        _ => None,
                                    })
                                    .collect(),
                            };
                        }
                    } else {
                        return Err(Grammar::too_short(map, nset));
                    }
                }
            }
        }
    }

    fn parse_statement(
        &self,
        sref: &StatementRef<'_>,
        nset: &Arc<Nameset>,
        names: &mut NameReader<'_>,
    ) -> Result<Option<Formula>, Diagnostic> {
        if sref.math_len() == 0 {
            return Err(Diagnostic::ParsedStatementNoTypeCode);
        }

        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let typecode = nset.get_atom(sref.math_at(0).slice);
        let mut expected_typecode = typecode;

        // Skip syntactic axioms
        if sref.statement_type() == StatementType::Axiom && expected_typecode != self.provable_type
        {
            return Ok(None);
        }

        // If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
        if expected_typecode == self.provable_type {
            expected_typecode = self.logic_type;
        }
        // At the time of writing, there are only 3 statements which are not provable but "syntactic theorems": weq, wel and bj-0

        debug!(
            "--------- Statement {:?} ---------",
            as_str(nset.statement_name(sref))
        );

        let mut symbol_iter = sref
            .math_iter()
            .skip(1)
            .map(|token| names.lookup_symbol(token.slice).unwrap().atom);
        let formula = self.parse_formula(&mut symbol_iter, Box::new([expected_typecode]), nset)?;
        Ok(Some(formula))
    }

    /// Returns the typecodes allowed in this grammar
    #[must_use]
    pub fn typecodes(&self) -> Box<[TypeCode]> {
        self.typecodes.clone().into_boxed_slice()
    }

    /// Lists the contents of the grammar's parse table. This can be used for debugging.
    pub fn dump(&self, nset: &Arc<Nameset>) {
        println!("Grammar tree has {:?} nodes.", self.nodes.len());
        for i in 0..self.nodes.len() {
            println!("{:?}", GrammarNodeIdDebug(self, i, nset));
        }
    }

    #[cfg(feature = "dot")]
    /// Exports the grammar tree in the "dot" format.
    /// See <https://www.graphviz.org/doc/info/lang.html>
    /// This dot file can then be converted to an SVG image using ` dot -Tsvg -o grammar.svg grammar.dot `
    pub fn export_dot(&self, nset: &Arc<Nameset>, write: &mut File) -> Result<(), ExportError> {
        let mut dot_writer = DotWriter::from(write);
        let mut digraph = dot_writer.digraph();
        for node_id in 0..self.nodes.len() {
            match &self.nodes.0[node_id] {
                GrammarNode::Leaf { reduce, .. } => {
                    digraph
                        .node_named(as_string(node_id))
                        .set_shape(Shape::Mdiamond)
                        .set_label(
                            format!(
                                "{} {}",
                                node_id,
                                escape(as_str(nset.atom_name(reduce.label)))
                            )
                            .as_str(),
                        ); // , escape(as_str(nset.atom_name(*typecode))), reduce.var_count
                }
                GrammarNode::Branch { map } => {
                    for (&key, node) in map {
                        let mut buf = String::new();
                        match key {
                            (SymbolType::Constant, symbol) => {
                                for reduce in node.leaf_label {
                                    if reduce.offset > 0 {
                                        write!(
                                            buf,
                                            "{}({}) / ",
                                            as_str(nset.atom_name(reduce.label)),
                                            reduce.offset
                                        )?;
                                    } else {
                                        write!(buf, "{} / ", as_str(nset.atom_name(reduce.label)))?;
                                    }
                                }
                                write!(buf, "{}", escape(as_str(nset.atom_name(symbol))).as_str())?;
                                digraph
                                    .edge(as_string(node_id), as_string(node.next_node_id))
                                    .attributes()
                                    .set_label(buf.as_str())
                                    .set_font("Courier");
                            }
                            (SymbolType::Variable, typecode) => {
                                buf.write_str(escape(as_str(nset.atom_name(typecode))).as_str())?;
                                for reduce in node.leaf_label {
                                    if reduce.offset > 0 {
                                        write!(
                                            buf,
                                            " / {}({})",
                                            as_str(nset.atom_name(reduce.label)),
                                            reduce.offset
                                        )?;
                                    } else {
                                        write!(buf, " / {}", as_str(nset.atom_name(reduce.label)))?;
                                    }
                                }
                                digraph
                                    .edge(as_string(node_id), as_string(node.next_node_id))
                                    .attributes()
                                    .set_label(buf.as_str())
                                    .set_color(Color::Blue)
                                    .set_font_color(Color::Blue);
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Called by [`crate::Database`] to build the grammar from the syntax axioms in the database.
///
/// The provided `sset`, and `nset` shall be the result of previous phases over the database.
/// The provided `grammar` will be updated with the results of the grammar build.
/// The grammar can then be used to parse the statements of the database (see [`parse_statements`]),
/// or to parse a single statement.
/// Use [`Grammar::default`] to get an initial state.
pub(crate) fn build_grammar<'a>(
    grammar: &mut Grammar,
    sset: &'a Arc<SegmentSet>,
    nset: &Arc<Nameset>,
) {
    // Read information about the grammar from the parser commands
    grammar.initialize(sset, nset);
    grammar.root = grammar.nodes.create_branch();

    let mut names = NameReader::new(nset);
    let mut type_conversions = Vec::new();

    // Build the initial grammar tree, just form syntax axioms and floats.
    let segments = sset.segments();
    assert!(!segments.is_empty(), "Parse returned no segment!");
    for segment in &segments {
        for sref in *segment {
            if let Err(diag) = match sref.statement_type() {
                StatementType::Axiom => {
                    grammar.add_axiom(&sref, nset, &mut names, &mut type_conversions)
                }
                StatementType::Floating => grammar.add_floating(&sref, nset, &mut names),
                _ => Ok(()),
            } {
                grammar.diagnostics.insert(sref.address(), diag);
            }
        }
    }

    // Post-treatement (type conversion and garden paths) as instructed by $j parser commands
    if let Err((address, diag)) = grammar.handle_commands(sset, nset, &mut names, &type_conversions)
    {
        grammar.diagnostics.insert(address, diag);
    }
}

/// The result of parsing all statements of the database with the language grammar
///
/// Example:
/// ```
/// use metamath_knife::database::{Database, DbOptions};
///
/// // Setup the required options
/// let mut options = DbOptions::default();
/// options.autosplit = true;
/// options.jobs = 8;
/// options.incremental = true;
///
/// // Create an empty database and load any file provided
/// let mut db = Database::new(options);
/// db.parse("set.mm".to_string(), vec![]);
/// let stmt_parse = db.stmt_parse_result();
/// ```
///
/// The parse tree for a given statement can then be obtained through [`StmtParse::get_formula`].
#[derive(Debug)]
pub struct StmtParse {
    segments: HashMap<SegmentId, Arc<StmtParseSegment>>,
}

impl Default for StmtParse {
    fn default() -> Self {
        StmtParse {
            segments: new_map(),
        }
    }
}

impl StmtParse {
    /// Returns a list of errors that were generated when parsing the database's statements.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sps in self.segments.values() {
            for (&sa, diag) in &sps.diagnostics {
                out.push((sa, diag.clone()));
            }
        }
        out
    }

    /// Check that printing parsed statements gives back the original formulas
    // TODO(tirix): this could be parallelized
    pub fn verify(
        &self,
        sset: &Arc<SegmentSet>,
        nset: &Arc<Nameset>,
    ) -> Result<(), (StatementAddress, Diagnostic)> {
        for sps in self.segments.values() {
            for (&sa, formula) in &sps.formulas {
                let sref = sset.statement(sa);
                let math_iter = sref
                    .math_iter()
                    .map(|token| nset.lookup_symbol(token.slice).unwrap().atom);
                let fmla_iter = formula.iter(sset, nset);
                if math_iter.ne(fmla_iter) {
                    return Err((sa, Diagnostic::FormulaVerificationFailed));
                }
            }
        }
        Ok(())
    }

    /// Writes down all formulas
    pub fn dump(&self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) {
        println!("Formula Dump:");
        for sps in self.segments.values() {
            for (&sa, formula) in &sps.formulas {
                let sref = sset.statement(sa);
                println!(
                    "{}: {}",
                    as_str(nset.statement_name(&sref)),
                    formula.display(sset, nset)
                );
            }
        }
    }

    /// Returns the formula for a given statement
    #[must_use]
    pub fn get_formula(&self, sref: &StatementRef<'_>) -> Option<&Formula> {
        let stmt_parse_segment = self.segments.get(&sref.segment().id)?;
        stmt_parse_segment.formulas.get(&sref.address())
    }
}

/// Data generated by the statement parsing process for a single segment.
#[derive(Debug)]
struct StmtParseSegment {
    _source: Arc<Segment>,
    diagnostics: HashMap<StatementAddress, Diagnostic>,
    formulas: HashMap<StatementAddress, Formula>,
}

/// Runs statement parsing for a single segment.
fn parse_statements_single<'a>(
    sset: &'a Arc<SegmentSet>,
    nset: &Arc<Nameset>,
    names: &mut NameReader<'_>,
    grammar: &Arc<Grammar>,
    sid: SegmentId,
) -> StmtParseSegment {
    let segment = sset.segment(sid);
    let mut diagnostics = new_map();
    let mut formulas = new_map();

    for sref in segment {
        match match sref.statement_type() {
            StatementType::Axiom | StatementType::Essential | StatementType::Provable => {
                grammar.parse_statement(&sref, nset, names)
            }
            _ => Ok(None),
        } {
            Err(diag) => {
                warn!(" FAILED to parse {}!", as_str(nset.statement_name(&sref)));
                diagnostics.insert(sref.address(), diag);
                break; // inserted here to stop at first error!
            }
            Ok(Some(formula)) => {
                formulas.insert(sref.address(), formula);
            }
            _ => {}
        }
    }

    StmtParseSegment {
        _source: (*segment).clone(),
        diagnostics,
        formulas,
    }
}

/// Called by [`crate::Database`] to parse all the statements in the database
///
/// The provided `segments`, `nset`, and `grammar` shall be the result of previous phases over the database.
/// The provided `stmt_parse` will be updated with the results of the parse.
/// The parse tree for a given statement can then be obtained through [`StmtParse::get_formula`].
/// Use [`StmtParse::default`] to get an initial state.
/// Like for several other phases, this occurs in parallel.
pub(crate) fn parse_statements<'a>(
    stmt_parse: &mut StmtParse,
    segments: &'a Arc<SegmentSet>,
    nset: &Arc<Nameset>,
    grammar: &Arc<Grammar>,
) {
    let mut ssrq = Vec::new();
    for sref in segments.segments() {
        let segments2 = segments.clone();
        let nset = nset.clone();
        let grammar = grammar.clone();
        let id = sref.id;
        ssrq.push(segments.exec.exec(sref.bytes(), move || {
            let sref = segments2.segment(id);
            let mut names = NameReader::new(&nset);
            let id = sref.id;
            (
                id,
                Arc::new(parse_statements_single(
                    &segments2, &nset, &mut names, &grammar, id,
                )),
            )
        }));
    }

    stmt_parse.segments.clear();
    for promise in ssrq {
        let (id, arc) = promise.wait();
        stmt_parse.segments.insert(id, arc);
    }
}
