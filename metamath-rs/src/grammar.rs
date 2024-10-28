//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.

// Possibly: Remove branch/leaf and keep only the optional leaf? (then final leaf = no next node id)

use crate::diag::{Diagnostic, StmtParseError};
use crate::formula::{Formula, FormulaBuilder, Label, Symbol, TypeCode};
use crate::nameck::{Atom, NameReader, Nameset};
use crate::segment::Segment;
use crate::segment_set::SegmentSet;
use crate::statement::{CommandToken, SegmentId, StatementAddress, SymbolType, TokenRef};
use crate::util::HashMap;
use crate::{as_str, Database, Span, StatementRef, StatementType};
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
    format!("{node_id}")
}

/// For the labels in DOT format
#[cfg(feature = "dot")]
fn escape(str: &str) -> String {
    str.replace('\\', "\\\\ ").replace('\"', "\\\"")
}

/// The grammar tree represents a Moore/Mealy Machine, where each node is a state of the automaton,
/// and transitions are made between node based on the input tokens read from the math string to parse.
#[derive(Debug)]
struct GrammarTree(Vec<GrammarNode>);

impl GrammarTree {
    /// Create a new, empty branch node
    fn create_branch(&mut self) -> NodeId {
        self.0.push(GrammarNode::Branch {
            map: HashMap::default(),
        });
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
    ) -> Result<(), Diagnostic> {
        match self.get_two_nodes_mut(copy_from_node_id, copy_to_node_id) {
            (
                GrammarNode::Branch { map },
                GrammarNode::Branch {
                    map: ref mut to_map,
                },
            ) => {
                for (&(stype, symbol), next_node) in map {
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
            _ => Err(Diagnostic::GrammarCantBuild("Malformed garden path: Cannot copy branches if any of the 'from' or 'to' is a leaf.")),
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
/// use metamath_rs::database::{Database, DbOptions};
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
/// let grammar = db.grammar_pass();
/// ```
#[derive(Debug)]
pub struct Grammar {
    provable_type: TypeCode,
    logic_type: TypeCode,
    typecodes: Vec<TypeCode>,
    type_conversions: Vec<(TypeCode, TypeCode, Label)>,
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
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
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

/// Increments the offets of the `reduce`s in the given list.
fn increment_offsets(rv: &mut ReduceVec) {
    for ref mut reduce in rv {
        reduce.offset += 1;
    }
}

/// Extends the `extend` list with the reduces in `rv1`, if not in `rv2`
fn diff_extend(rv1: ReduceVec, rv2: ReduceVec, extend: &mut ReduceVec) -> Result<(), Diagnostic> {
    let mut i2 = rv2.iter();
    let mut or2 = i2.next();
    for r1 in rv1 {
        if let Some(r2) = or2 {
            if r1.label == r2.label {
                or2 = i2.next();
            } else {
                extend.push(r1);
            }
        } else {
            extend.push(r1);
        }
    }
    if or2.is_some() {
        Err(Diagnostic::GrammarCantBuild("Malformed garden path: More <reduce> in the target branch than in the template branch."))
    } else {
        Ok(())
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

struct GrammarNodeRef<'a>(&'a GrammarNode, &'a Nameset);
impl fmt::Debug for GrammarNodeRef<'_> {
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

struct GrammarNodeIdRef<'a> {
    grammar: &'a Grammar,
    node_id: NodeId,
    nset: &'a Nameset,
}

impl fmt::Debug for GrammarNodeIdRef<'_> {
    /// Lists the contents of the grammar node, given the grammar and a node id
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {:?}",
            self.node_id,
            GrammarNodeRef(&self.grammar.nodes.0[self.node_id], self.nset)
        )
    }
}

impl Default for Grammar {
    fn default() -> Self {
        Grammar {
            provable_type: TypeCode::default(),
            logic_type: TypeCode::default(),
            typecodes: Vec::new(),
            type_conversions: Vec::new(),
            nodes: GrammarTree(Vec::new()),
            root: 0,
            diagnostics: HashMap::default(),
            debug: false,
        }
    }
}

fn undefined(token: TokenRef<'_>, sref: &StatementRef<'_>) -> Diagnostic {
    Diagnostic::UndefinedToken(sref.math_span(token.index()), token.slice.into())
}

fn undefined_cmd(token: &CommandToken, buf: &[u8]) -> Diagnostic {
    Diagnostic::UndefinedToken(token.full_span(), token.value(buf).into())
}

impl Grammar {
    /// Initializes the grammar using the parser commands
    fn initialize(&mut self, sset: &SegmentSet, nset: &Nameset) {
        for sref in sset.segments(..) {
            let buf = &**sref.buffer;
            for (_, (_, command)) in &sref.j_commands {
                use CommandToken::*;
                match &**command {
                    [Keyword(cmd), sort, Keyword(as_), logic]
                        if cmd.as_ref(buf) == b"syntax" && as_.as_ref(buf) == b"as" =>
                    {
                        self.provable_type = nset.lookup_symbol(&sort.value(buf)).unwrap().atom;
                        self.logic_type = nset.lookup_symbol(&logic.value(buf)).unwrap().atom;
                        self.typecodes.push(self.logic_type);
                    }
                    [Keyword(cmd), rest @ ..] if cmd.as_ref(buf) == b"syntax" => {
                        for sort in rest {
                            self.typecodes
                                .push(nset.lookup_symbol(&sort.value(buf)).unwrap().atom)
                        }
                    }
                    _ => {}
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
    fn ambiguous(&self, start_node: NodeId, nset: &Nameset) -> Diagnostic {
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

    fn too_short(
        last_token: FormulaToken,
        map: &HashMap<(SymbolType, Atom), NextNode>,
        nset: &Nameset,
    ) -> StmtParseError {
        StmtParseError::ParsedStatementTooShort(
            last_token.span,
            map.keys()
                .find(|k| k.0 == SymbolType::Constant)
                .map(|(_, expected_symbol)| nset.atom_name(*expected_symbol).into()),
        )
    }

    /// Gets the map of a branch
    fn get_branch(&self, node_id: NodeId) -> &HashMap<(SymbolType, Atom), NextNode> {
        if let GrammarNode::Branch { map } = &self.nodes.get(node_id) {
            map
        } else {
            panic!("Expected branch for node {node_id}!");
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
        let GrammarNode::Branch { map } = self.nodes.get_mut(to_node) else {
            return Err(to_node); // Error: cannot add to a leaf node, `to_node` is the conflicting node
        };
        match map.get(&(stype, symbol)) {
            Some(prev_node) if prev_node.leaf_label == add_reduce => Ok(prev_node.next_node_id),
            Some(prev_node) => Err(prev_node.next_node_id),
            None => {
                let new_node_id = self.nodes.create_branch();
                // here we have to re-borrow from self after the creation,
                // because the previous var_map and cst_map may not be valid pointers anymore
                let GrammarNode::Branch { map } = self.nodes.get_mut(to_node) else {
                    unreachable!();
                };
                map.insert(
                    (stype, symbol),
                    NextNode::new_with_reduce_vec(new_node_id, add_reduce),
                );
                Ok(new_node_id)
            }
        }
    }

    /// Build the parse tree, marking variables with their types
    fn add_axiom(
        &mut self,
        sref: &StatementRef<'_>,
        nset: &Nameset,
        names: &mut NameReader<'_>,
    ) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter().peekable();

        // Atom for this axiom's label.
        let this_label = names
            .lookup_label(sref.label())
            .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?
            .atom;
        let this_typecode = nset.get_atom(tokens.next().ok_or(Diagnostic::EmptyMathString)?.slice);

        // In case of a non-syntax axiom, skip it.
        if this_typecode == self.provable_type {
            return Ok(());
        }

        // Detect "type conversion" syntax axioms: ~cv for set.mm
        if sref.math_len() == 2 {
            let token_ptr = sref.math_at(1).slice;
            let symbol = names
                .lookup_symbol(token_ptr)
                .ok_or_else(|| Diagnostic::UndefinedToken(sref.math_span(1), token_ptr.into()))?;
            if symbol.stype == SymbolType::Variable {
                let Some(lookup_float) = names.lookup_float(token_ptr) else {
                    return Err(Diagnostic::VariableMissingFloat(1));
                };
                self.type_conversions
                    .push((lookup_float.typecode_atom, this_typecode, this_label));
                return Ok(()); // we don't need to add the type conversion axiom itself to the grammar (or do we?)
            }
        }

        // We will add this syntax axiom to the grammar tree
        let mut node = self.root;
        let mut var_count = 0;
        while let Some(token) = tokens.next() {
            let symbol = names
                .lookup_symbol(token.slice)
                .ok_or_else(|| undefined(token, sref))?;
            let atom = match symbol.stype {
                SymbolType::Constant => symbol.atom,
                SymbolType::Variable => {
                    var_count += 1;
                    // We need a second lookup to find out the typecode of a floating variable...
                    // Ideally this information would be included in the LookupSymbol
                    names
                        .lookup_float(token.slice)
                        .ok_or_else(|| undefined(token, sref))?
                        .typecode_atom
                }
            };
            match if tokens.peek().is_some() {
                self.add_branch_with_reduce(node, atom, symbol.stype, ReduceVec::new())
            } else {
                let leaf_node_id = self
                    .nodes
                    .create_leaf(Reduce::new(this_label, var_count), this_typecode);
                self.add_branch(node, atom, symbol.stype, &NextNode::new(leaf_node_id))
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
        nset: &Nameset,
        names: &mut NameReader<'_>,
    ) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter();

        // Atom for this float's label.
        let this_label = names
            .lookup_label(sref.label())
            .ok_or_else(|| Diagnostic::UnknownLabel(sref.label_span()))?
            .atom;
        let this_typecode =
            nset.get_atom(tokens.next().ok_or(Diagnostic::NotActiveSymbol(0))?.slice);

        // Float shall not be of the provable typecode.
        if this_typecode == self.provable_type {
            return Err(Diagnostic::GrammarProvableFloat);
        }

        // We will add this floating declaration to the grammar tree
        let leaf_node = self
            .nodes
            .create_leaf(Reduce::new_variable(this_label), this_typecode);

        let token = tokens.next().ok_or(Diagnostic::BadFloating)?;
        let symbol = names
            .lookup_symbol(token.slice)
            .ok_or(Diagnostic::FloatNotVariable(1))?;

        debug!(
            "========== Statement {:?} ==========",
            as_str(nset.statement_name(sref))
        );

        let GrammarNode::Branch { map } = self.nodes.get_mut(self.root) else {
            unreachable!("Root node must be a branch node!")
        };
        // We ignore the ambiguity in floats, since they are actually frame dependent.
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
        db: &Database,
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
                            debug!("{:?}", self.node_id(db, node_id));
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
                            .unwrap(); // We're adding a missing branch, not such branch shall not exist yet.
                        }
                        Some(existing_next_node) => {
                            // A branch for the converted type already exist: add the conversion to that branch!
                            debug!(
                                "Type Conv copying to {} node id {}",
                                next_node_id, existing_next_node.next_node_id
                            );
                            debug!("{:?}", self.node_id(db, next_node_id));
                            debug!("{:?}", self.node_id(db, existing_next_node.next_node_id));
                            let existing_next_node_id = existing_next_node.next_node_id;
                            self.nodes.copy_branches(
                                next_node_id,
                                existing_next_node_id,
                                Reduce::new(label, 1),
                            )?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn next_var_node(&self, node_id: NodeId, typecode: TypeCode) -> Option<(NodeId, &ReduceVec)> {
        let GrammarNode::Branch { map } = self.nodes.get(node_id) else {
            return None;
        };
        let NextNode {
            next_node_id,
            leaf_label,
        } = map.get(&(SymbolType::Variable, typecode))?;
        Some((*next_node_id, leaf_label))
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
        db: &Database,
        mut stored_reduces: ReduceVec,
        make_final: F,
    ) -> Result<(), Diagnostic>
    where
        F: FnOnce(&ReduceVec, TypeCode) -> Result<NextNode, Diagnostic> + Copy,
    {
        debug!("Clone {} to {}", add_from_node_id, add_to_node_id);
        debug!("{:?}", self.node_id(db, add_from_node_id));
        debug!("{:?}", self.node_id(db, add_to_node_id));
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
                    let mut reduce_vec = next_node.leaf_label;
                    for reduce in stored_reduces {
                        reduce_vec.push(reduce);
                    }
                    reduce_vec.push(*r);
                    debug!(
                        "LEAF for {} to {} {:?}",
                        add_from_node_id, add_to_node_id, reduce_vec
                    );
                    let final_node = make_final(&reduce_vec, typecode)?;
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
                            )?;
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
                        db,
                        new_stored_reduces,
                        make_final,
                    )?;
                }
            }
        }
        Ok(())
    }

    // compare this with "copy_branches"!
    fn clone_with_reduce_vec(
        &mut self,
        add_from_node_id: NodeId,
        add_to_node_id: NodeId,
        reduce_vec: &ReduceVec,
    ) -> Result<(), Diagnostic> {
        if add_from_node_id == add_to_node_id {
            // nothing to clone here!
            return Ok(());
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
            .map_err(|_| {
                Diagnostic::GrammarCantBuild(
                    "Grammar implementation does not handle double conflicts",
                )
            })?;
        }
        Ok(())
    }

    /// Expand the tree at the given node, for the given symbol.  This means cloning/inserting from the root tree at that symbol, until a given typecode is obtained, into the given node
    /// This is used in order to ensure that a given sequence is in the grammar tree, like `<. <.`, which does not correspond to a single syntax axiom
    fn expand_tree(
        &mut self,
        to_node: NodeId,
        symbol: Symbol,
        stype: SymbolType,
        db: &Database,
    ) -> Result<NodeId, Diagnostic> {
        let next_node_id_from_root = self
            .nodes
            .get(self.root)
            .next_node(symbol, stype)
            .ok_or(Diagnostic::GrammarCantBuild(
                "Expanded formula cannot be parsed from root node",
            ))?
            .next_node_id;
        let node_from_root = self.nodes.get(next_node_id_from_root).clone();
        let new_node_id = self
            .add_branch_with_reduce(to_node, symbol, stype, ReduceVec::new())
            .map_err(|_| {
                Diagnostic::GrammarCantBuild(
                    "Malformed garden path: Tree to be expanded already exists",
                )
            })?;
        self.clone_branches(
            next_node_id_from_root,
            new_node_id,
            db,
            ReduceVec::new(),
            |rv, t| {
                Ok(node_from_root
                    .next_node(t, SymbolType::Variable)
                    .ok_or(Diagnostic::GrammarCantBuild(
                        "Malformed garden path: Expanded node's typecode is not available",
                    ))?
                    .with_reduce_vec(rv))
            },
        )?;
        Ok(self
            .nodes
            .get(to_node)
            .next_node(symbol, stype)
            .ok_or(Diagnostic::GrammarCantBuild(
                "Malformed garden path: prefix cannot be parsed",
            ))?
            .next_node_id)
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
        prefix: &[CommandToken],
        shadows: &[CommandToken],
        buf: &[u8],
        db: &Database,
        names: &mut NameReader<'_>,
    ) -> Result<(), Diagnostic> {
        let mut node_id = self.root;
        let mut index = 0;

        // First we follow the tree to the common prefix
        loop {
            if prefix[index].value(buf) != shadows[index].value(buf) {
                break;
            }
            // TODO(tirix): use https://rust-lang.github.io/rfcs/2497-if-let-chains.html once it's out!
            if let GrammarNode::Branch { map } = self.nodes.get(node_id) {
                let prefix_symbol = db
                    .name_result()
                    .lookup_symbol(&prefix[index].value(buf))
                    .ok_or_else(|| undefined_cmd(&prefix[index], buf))?
                    .atom;
                let next_node = map
                    .get(&(SymbolType::Constant, prefix_symbol))
                    .expect("Prefix cannot be parsed!");
                node_id = next_node.next_node_id;
                index += 1;
            } else {
                return Err(Diagnostic::GrammarCantBuild(
                    "Leaf reached while parsing common prefixes",
                ));
            }
        }

        // We note the typecode and next branch of the "shadowed" prefix
        let shadowed_typecode = names
            .lookup_float(&shadows[index].value(buf))
            .ok_or_else(|| undefined_cmd(&shadows[index], buf))?
            .typecode_atom;
        let (shadowed_next_node, _) =
            self.next_var_node(node_id, shadowed_typecode)
                .ok_or(Diagnostic::GrammarCantBuild(
                    "Shadowed prefix cannot be parsed",
                ))?;

        // We note what comes after the shadowing typecode, both if we start from the prefix and if we start from the root
        let mut add_from_node_id = self.root;
        let mut shadowing_atom: Atom;
        let mut shadowing_stype;
        let mut missing_reduce = ReduceVec::new();
        for token in &prefix[index..] {
            let lookup_symbol = names
                .lookup_symbol(&token.value(buf))
                .ok_or_else(|| undefined_cmd(token, buf))?;
            debug!(
                "Following prefix {}, at {} / {}",
                as_str(&token.value(buf)),
                node_id,
                add_from_node_id
            );
            shadowing_stype = lookup_symbol.stype;
            shadowing_atom = match shadowing_stype {
                SymbolType::Constant => lookup_symbol.atom,
                SymbolType::Variable => {
                    increment_offsets(&mut missing_reduce);
                    names
                        .lookup_float(&token.value(buf))
                        .ok_or_else(|| undefined_cmd(token, buf))?
                        .typecode_atom
                }
            };
            let add_to_next_node = self
                .nodes
                .get(node_id)
                .next_node(shadowing_atom, shadowing_stype)
                .ok_or(Diagnostic::GrammarCantBuild("Prefix cannot be parsed"))?;
            node_id = add_to_next_node.next_node_id;
            add_from_node_id = match self
                .nodes
                .get(add_from_node_id)
                .next_node(shadowing_atom, shadowing_stype)
            {
                Some(next_node) => {
                    diff_extend(
                        next_node.leaf_label,
                        add_to_next_node.leaf_label,
                        &mut missing_reduce,
                    )?;
                    next_node.next_node_id
                }
                None => self.expand_tree(add_from_node_id, shadowing_atom, shadowing_stype, db)?,
            }
        }

        debug!("Shadowed token: {}", as_str(&shadows[index].value(buf)));
        debug!("Missing reduces: {}", missing_reduce.len());
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
        let make_final = |rv: &ReduceVec, _| {
            Ok(NextNode {
                next_node_id: shadowed_next_node,
                leaf_label: *rv,
            })
        };
        match self.nodes.get(add_from_node_id) {
            GrammarNode::Branch { .. } => {
                self.clone_branches(add_from_node_id, node_id, db, missing_reduce, make_final)?;
            }
            GrammarNode::Leaf { reduce, .. } => {
                missing_reduce.push(*reduce);
                self.clone_with_reduce_vec(shadowed_next_node, node_id, &missing_reduce)?;
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
        db: &Database,
        names: &mut NameReader<'_>,
    ) -> Result<(), (StatementAddress, Diagnostic)> {
        let nset = db.name_result();
        for sref in db.parse_result().segments(..) {
            let buf = &**sref.buffer;
            for &(ix, (span, ref command)) in &sref.j_commands {
                use CommandToken::*;
                let address = StatementAddress::new(sref.id, ix);
                let [Keyword(k), ref rest @ ..] = **command else {
                    return Err((address, Diagnostic::BadCommand(span)));
                };
                // Empty parser command
                match k.as_ref(buf) {
                    b"syntax" => match rest {
                        [ty, Keyword(as_), code] if as_.as_ref(buf) == b"as" => {
                            // syntax '|-' as 'wff';
                            self.provable_type = nset
                                .lookup_symbol(&ty.value(buf))
                                .ok_or_else(|| (address, undefined_cmd(ty, buf)))?
                                .atom;
                            self.typecodes.push(
                                nset.lookup_symbol(&code.value(buf))
                                    .ok_or_else(|| (address, undefined_cmd(code, buf)))?
                                    .atom,
                            );
                        }
                        _ => {
                            for ty in rest {
                                // syntax 'setvar';
                                self.typecodes.push(
                                    nset.lookup_symbol(&ty.value(buf))
                                        .ok_or_else(|| (address, undefined_cmd(ty, buf)))?
                                        .atom,
                                );
                            }
                        }
                    },
                    // Handle Ambiguous prefix commands
                    b"garden_path" => {
                        let split_index = rest
                            .iter()
                            .position(|t| matches!(t, Keyword(k) if k.as_ref(buf) == b"=>"))
                            .ok_or((address, Diagnostic::BadCommand(k)))?; // '=>' not present in 'garden_path' command
                        let (prefix, shadows) = rest.split_at(split_index);
                        if let Err(diag) =
                            self.handle_common_prefixes(prefix, &shadows[1..], buf, db, names)
                        {
                            return Err((address, diag));
                        }
                    }
                    // Handle replacement schemes
                    b"type_conversions" => {
                        for &(from_typecode, to_typecode, label) in &self.type_conversions.clone() {
                            self.perform_type_conversion(from_typecode, to_typecode, label, db)
                                .map_err(|diag| (address, diag))?;
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    fn do_shift(
        &self,
        symbol_iter: &mut dyn Iterator<Item = Result<FormulaToken, StmtParseError>>,
        nset: &Nameset,
    ) -> Result<(), StmtParseError> {
        if let Some(token) = symbol_iter.next() {
            let token = token?;
            if self.debug {
                debug!("   SHIFT {:?}", as_str(nset.atom_name(token.symbol)));
            }
        }
        Ok(())
    }

    fn do_reduce(formula_builder: &mut FormulaBuilder, reduce: Reduce, nset: &Nameset) {
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
        symbol_iter: &mut impl Iterator<Item = Result<FormulaToken, StmtParseError>>,
        expected_typecodes: &[TypeCode],
        convert_to_provable: bool,
        nset: &Nameset,
    ) -> Result<Formula, StmtParseError> {
        struct StackElement {
            node_id: NodeId,
            expected_typecodes: Box<[TypeCode]>,
        }

        let mut formula_builder = FormulaBuilder::default();
        let mut symbol_enum = symbol_iter.peekable();
        let Ok(mut last_token) = symbol_enum
            .peek()
            .ok_or(StmtParseError::ParsedStatementNoTypeCode)?
        else {
            return Err(symbol_enum.next().unwrap().unwrap_err());
        };
        let mut e = StackElement {
            node_id: self.root,
            expected_typecodes: expected_typecodes.to_vec().into_boxed_slice(),
        };
        let mut stack = vec![];
        loop {
            match *self.nodes.get(e.node_id) {
                GrammarNode::Leaf {
                    reduce,
                    mut typecode,
                } => {
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
                            if typecode == self.logic_type && convert_to_provable {
                                typecode = self.provable_type;
                            }
                            return Ok(formula_builder.build(typecode));
                        } else {
                            // There are still symbols to parse, continue from root
                            let (next_node_id, leaf_label) = self
                                .next_var_node(self.root, typecode)
                                .ok_or(StmtParseError::UnparseableStatement(last_token.span))?;
                            for &reduce in leaf_label {
                                Self::do_reduce(&mut formula_builder, reduce, nset);
                            }
                            e.node_id = next_node_id;
                        }
                    } else {
                        // We have parsed everything but did not obtain an expected typecode, try a type conversion.
                        if symbol_enum.peek().is_none() {
                            for (from_typecode, to_typecode, label) in &self.type_conversions {
                                if *from_typecode == typecode
                                    && e.expected_typecodes.contains(to_typecode)
                                {
                                    let reduce = Reduce::new(*label, 1);
                                    Self::do_reduce(&mut formula_builder, reduce, nset);
                                    let typecode =
                                        if *to_typecode == self.logic_type && convert_to_provable {
                                            self.provable_type
                                        } else {
                                            *to_typecode
                                        };
                                    return Ok(formula_builder.build(typecode));
                                }
                            }
                        }
                        // We have not found the expected typecode, continue from root
                        debug!(" ++ Wrong type obtained, continue.");
                        let (next_node_id, leaf_label) = self
                            .next_var_node(self.root, typecode)
                            .ok_or(StmtParseError::UnparseableStatement(last_token.span))?;
                        for &reduce in leaf_label {
                            Self::do_reduce(&mut formula_builder, reduce, nset);
                        }
                        e.node_id = next_node_id;
                    }
                }
                GrammarNode::Branch { ref map } => {
                    if let Some(&Ok(token)) = symbol_enum.peek() {
                        last_token = token;
                        debug!("   {:?}", as_str(nset.atom_name(token.symbol)));

                        if let Some(NextNode {
                            next_node_id,
                            leaf_label,
                        }) = map.get(&(SymbolType::Constant, token.symbol))
                        {
                            // Found an atom matching one of our next nodes: First optionally REDUCE and continue
                            for &reduce in leaf_label {
                                Self::do_reduce(&mut formula_builder, reduce, nset);
                            }

                            // Found an atom matching one of our next nodes: SHIFT, to the next node
                            self.do_shift(&mut symbol_enum, nset)?;
                            e.node_id = *next_node_id;
                            debug!("   Next Node: {:?}", e.node_id);
                        } else {
                            // No matching constant, search among variables
                            if map.is_empty() || e.node_id == self.root {
                                return Err(StmtParseError::UnparseableStatement(token.span));
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
                        if let Some(token) = symbol_enum.next() {
                            token?;
                        }
                        return Err(Grammar::too_short(last_token, map, nset));
                    }
                }
            }
        }
    }
}

/// An Atom which remembers its position in the source, for error handling
#[derive(Clone, Copy, Debug)]
pub struct FormulaToken {
    /// The symbol's atom
    pub symbol: Symbol,
    /// The span of the original source string this token has been read from, used for error reporting.
    pub span: Span,
}

/// An iterator through the tokens of a string
struct FormulaTokenIter<'a> {
    string: &'a str,
    chars: std::iter::Peekable<core::str::Chars<'a>>,
    nset: &'a Arc<Nameset>,
    last_pos: usize,
}

impl<'a> FormulaTokenIter<'a> {
    /// Builds a `FormulaTokenIter` from a string.
    /// Characters are expected to be ASCII
    fn from_str(string: &'a str, nset: &'a Arc<Nameset>) -> Self {
        Self {
            string,
            chars: string.chars().peekable(),
            nset,
            last_pos: 0,
        }
    }
}

impl Iterator for FormulaTokenIter<'_> {
    type Item = Result<FormulaToken, StmtParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.last_pos >= self.string.len() {
            None
        } else {
            let span = if let Some(next_pos) = self.chars.position(|c| c.is_ascii_whitespace()) {
                Span::new(self.last_pos, self.last_pos + next_pos)
            } else {
                Span::new(self.last_pos, self.string.len())
            };
            self.last_pos = span.end as usize + 1;
            while self.chars.peek().map(char::is_ascii_whitespace) == Some(true) {
                self.chars.next();
                self.last_pos += 1;
            }
            let t = &self.string[span.start as usize..span.end as usize];
            if let Some(l) = self.nset.lookup_symbol(t.as_bytes()) {
                Some(Ok(FormulaToken {
                    symbol: l.atom,
                    span,
                }))
            } else {
                Some(Err(StmtParseError::UnknownToken(span)))
            }
        }
    }
}

/// An iterator through the tokens of a math expression
#[derive(Debug)]
pub struct StmtTokenIter<'a, 'b> {
    span: &'a [Span],
    buffer: &'a [u8],
    index: usize,
    names: &'a mut NameReader<'b>,
}

impl StatementRef<'_> {
    /// Returns a new iterator over tokens of a math expression.
    /// `names` caches the result of any name lookups performed.
    pub fn token_iter<'a, 'b>(&'a self, names: &'a mut NameReader<'b>) -> StmtTokenIter<'a, 'b> {
        let range = self.statement.math_start..self.statement.proof_start;
        StmtTokenIter {
            span: &self.segment.segment.span_pool[range],
            buffer: &self.segment.segment.buffer,
            index: 1,
            names,
        }
    }
}

impl Iterator for StmtTokenIter<'_, '_> {
    type Item = Result<FormulaToken, StmtParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        let span = *self.span.get(self.index)?;
        self.index += 1;
        Some(
            if let Some(lookup) = self.names.lookup_symbol(span.as_ref(self.buffer)) {
                Ok(FormulaToken {
                    symbol: lookup.atom,
                    span,
                })
            } else {
                Err(StmtParseError::UnknownToken(span))
            },
        )
    }
}

impl Grammar {
    /// Parses a character string into a formula
    /// As a first math token, the string is expected to contain the typecode for the formula.
    /// Diagnostics mark the errors with [Span]s based on the position in the input string.
    pub fn parse_string(
        &self,
        formula_string: &str,
        nset: &Arc<Nameset>,
    ) -> Result<Formula, StmtParseError> {
        let mut symbols = FormulaTokenIter::from_str(formula_string, nset);
        let typecode = symbols
            .next()
            .ok_or(StmtParseError::ParsedStatementNoTypeCode)??;
        let expected_typecode = if typecode.symbol == self.provable_type {
            self.logic_type
        } else {
            typecode.symbol
        };
        let convert_to_provable = typecode.symbol == self.provable_type;
        self.parse_formula(
            &mut symbols,
            &[expected_typecode],
            convert_to_provable,
            nset,
        )
    }

    /// Parses an individual statement into a formula.
    pub fn parse_statement(
        &self,
        sref: &StatementRef<'_>,
        nset: &Nameset,
        names: &mut NameReader<'_>,
    ) -> Result<Formula, StmtParseError> {
        if sref.math_len() == 0 {
            return Err(StmtParseError::ParsedStatementNoTypeCode);
        }

        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let typecode = nset.get_atom(sref.math_at(0).slice);
        let mut expected_typecode = typecode;

        // If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
        if expected_typecode == self.provable_type {
            expected_typecode = self.logic_type;
        }
        // At the time of writing, there are only 3 statements which are not provable but "syntactic theorems": weq, wel and bj-0

        debug!(
            "--------- Statement {:?} ---------",
            as_str(nset.statement_name(sref))
        );

        let mut math_string = sref.token_iter(names);
        let convert_to_provable = typecode == self.provable_type;
        let formula = self.parse_formula(
            &mut math_string,
            &[expected_typecode],
            convert_to_provable,
            nset,
        )?;
        Ok(formula)
    }

    /// Returns the typecodes allowed in this grammar
    #[must_use]
    pub fn typecodes(&self) -> Box<[TypeCode]> {
        self.typecodes.clone().into_boxed_slice()
    }

    /// Returns the provable typecode for this grammar
    /// (for set.mm, that is `|-`)
    #[must_use]
    pub const fn provable_typecode(&self) -> TypeCode {
        self.provable_type
    }

    /// Returns the logic typecode for this grammar
    /// (for set.mm, that is `wff`)
    #[must_use]
    pub const fn logic_typecode(&self) -> TypeCode {
        self.logic_type
    }

    /// Converts the given formula to the target typecode,
    /// provided there is a suitable type conversion.
    #[must_use]
    pub fn convert_typecode(&self, fmla: Formula, target_tc: TypeCode) -> Option<Formula> {
        let source_tc = fmla.get_typecode();
        self.type_conversions
            .iter()
            .find(|(from_tc, to_tc, _)| *from_tc == source_tc && *to_tc == target_tc)
            .map(|(_, _, label)| {
                let mut builder = FormulaBuilder::from_formula(fmla);
                builder.reduce(*label, 1, 0, false);
                builder.build(target_tc)
            })
    }

    /// Lists the contents of the grammar's parse table. This can be used for debugging.
    pub fn dump(&self, db: &Database) {
        println!("Grammar tree has {:?} nodes.", self.nodes.len());
        for i in 0..self.nodes.len() {
            println!("{:?}", self.node_id(db, i));
        }
    }

    fn node_id<'a>(&'a self, db: &'a Database, node_id: NodeId) -> GrammarNodeIdRef<'a> {
        GrammarNodeIdRef {
            grammar: self,
            node_id,
            nset: db.name_result(),
        }
    }

    #[cfg(feature = "dot")]
    /// Exports the grammar tree in the "dot" format.
    /// See <https://www.graphviz.org/doc/info/lang.html>
    /// This dot file can then be converted to an SVG image using ` dot -Tsvg -o grammar.svg grammar.dot `
    pub fn export_dot(&self, nset: &Nameset, write: &mut File) -> Result<(), ExportError> {
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

    /// Called by [`crate::Database`] to build the grammar from the syntax axioms in the database.
    ///
    /// The provided `sset`, and `nset` shall be the result of previous phases over the database.
    /// The provided `grammar` will be updated with the results of the grammar build.
    /// The grammar can then be used to parse the statements of the database (see [`parse_statements`]),
    /// or to parse a single statement.
    /// Use [`Grammar::default`] to get an initial state.
    pub(crate) fn new(db: &Database) -> Grammar {
        let mut grammar = Grammar::default();
        let sset = db.parse_result();
        let nset = db.name_result();
        // Read information about the grammar from the parser commands
        grammar.initialize(sset, nset);
        grammar.root = grammar.nodes.create_branch();

        let mut names = NameReader::new(nset);

        // Build the initial grammar tree, just form syntax axioms and floats.
        let segments = sset.segments(..);
        assert!(
            segments.clone().next().is_some(),
            "Parse returned no segment!"
        );
        for segment in segments {
            for sref in segment {
                if let Err(diag) = match sref.statement_type() {
                    StatementType::Axiom => grammar.add_axiom(&sref, nset, &mut names),
                    StatementType::Floating => grammar.add_floating(&sref, nset, &mut names),
                    _ => Ok(()),
                } {
                    grammar.diagnostics.insert(sref.address(), diag);
                }
            }
        }

        // Post-treatement (type conversion and garden paths) as instructed by $j parser commands
        if let Err((address, diag)) = grammar.handle_commands(db, &mut names) {
            grammar.diagnostics.insert(address, diag);
        }
        grammar
    }
}

/// The result of parsing all statements of the database with the language grammar
///
/// Example:
/// ```
/// use metamath_rs::database::{Database, DbOptions};
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
/// let stmt_parse = db.stmt_parse_pass();
/// ```
///
/// The parse tree for a given statement can then be obtained through [`StmtParse::get_formula`].
#[derive(Debug, Default)]
pub struct StmtParse {
    segments: HashMap<SegmentId, Arc<StmtParseSegment>>,
}

impl StmtParse {
    /// Returns a list of errors that were generated when parsing the database's statements.
    #[must_use]
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sps in self.segments.values() {
            for (&sa, diag) in &sps.diagnostics {
                out.push((sa, diag.clone().into()));
            }
        }
        out
    }

    /// Check that printing parsed statements gives back the original formulas
    // TODO(tirix): this could be parallelized
    pub(crate) fn verify(&self, db: &Database) -> Vec<(StatementAddress, Diagnostic)> {
        let sset = db.parse_result();
        let nset = db.name_result();
        let mut diags = vec![];
        for sps in self.segments.values() {
            for (&sa, formula) in &sps.formulas {
                let sref = sset.statement(sa);
                let math_iter = sref.math_iter().skip(1).flat_map(|token| {
                    nset.lookup_symbol(token.slice)
                        .ok_or_else(|| {
                            (
                                sref.address(),
                                StmtParseError::UnknownToken(sref.math_span(token.index())),
                            )
                        })
                        .map(|l| l.atom)
                });
                let fmla_iter = formula.as_ref(db).iter();
                if math_iter.ne(fmla_iter) {
                    diags.push((sa, Diagnostic::FormulaVerificationFailed));
                }
            }
        }
        diags
    }

    /// Writes down all formulas
    pub(crate) fn dump(&self, db: &Database) {
        println!("Formula Dump:");
        let sset = db.parse_result();
        let nset = db.name_result();
        for sps in self.segments.values() {
            for (&sa, formula) in &sps.formulas {
                let sref = sset.statement(sa);
                println!(
                    "{}: {}",
                    as_str(nset.statement_name(&sref)),
                    formula.as_ref(db).as_sexpr()
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
    diagnostics: HashMap<StatementAddress, StmtParseError>,
    formulas: HashMap<StatementAddress, Formula>,
}

/// Runs statement parsing for a single segment.
fn parse_statements_single(
    sset: &SegmentSet,
    nset: &Nameset,
    names: &mut NameReader<'_>,
    grammar: &Grammar,
    sid: SegmentId,
) -> StmtParseSegment {
    let segment = sset.segment(sid);
    let mut diagnostics = HashMap::default();
    let mut formulas = HashMap::default();

    for sref in segment {
        if let StatementType::Axiom | StatementType::Essential | StatementType::Provable =
            sref.statement_type()
        {
            match grammar.parse_statement(&sref, nset, names) {
                Err(diag) => {
                    warn!(" FAILED to parse {}!", as_str(nset.statement_name(&sref)));
                    diagnostics.insert(sref.address(), diag);
                    break; // inserted here to stop at first error!
                }
                Ok(formula) => {
                    formulas.insert(sref.address(), formula);
                }
            }
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
pub(crate) fn parse_statements(
    stmt_parse: &mut StmtParse,
    segments: &Arc<SegmentSet>,
    nset: &Arc<Nameset>,
    grammar: &Arc<Grammar>,
) {
    let mut ssrq = Vec::new();
    for sref in segments.segments(..) {
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
