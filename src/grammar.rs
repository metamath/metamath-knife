//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.

// Possibly: Remove branch/leaf and keep only the optional leaf? (then final leaf = no next node id)

use crate::diag::Diagnostic;
use crate::nameck::NameReader;
use crate::nameck::Nameset;
use crate::nameck::Atom;
use crate::parser::Segment;
use crate::parser::SegmentId;
use crate::parser::StatementAddress;
use crate::parser::StatementType;
use crate::parser::StatementRef;
use crate::parser::SymbolType;
use crate::parser::Token;
use crate::parser::TokenIndex;
use crate::parser::as_str;
use crate::parser::copy_token;
use crate::segment_set::SegmentSet;
use crate::formula::Symbol;
use crate::formula::TypeCode;
use crate::formula::Label;
use crate::formula::Formula;
use crate::formula::FormulaBuilder;
use std::ops::Index;
use std::sync::Arc;
use tinyvec::ArrayVec;
use crate::util::HashMap;
use crate::util::new_map;
use std::fmt;
use std::fmt::Formatter;
use log::{debug,warn};

#[cfg(feature = "dot")]
use dot_writer::{Attributes, Color, DotWriter, Shape};
#[cfg(feature = "dot")]
use crate::export::ExportError;
#[cfg(feature = "dot")]
use std::fmt::Write;
#[cfg(feature = "dot")]
use std::fs::File;

/// An index to address [GrammarNode]'s
type NodeId = usize;

/// For the labels in DOT format
#[cfg(feature = "dot")]
fn as_string(node_id: NodeId) -> String {
    format!("{}", node_id)
}

/// For the labels in DOT format
#[cfg(feature = "dot")]
fn escape(str: &str) -> String {
    str
        .replace("\\","\\\\ ")
        .replace("\"","\\\"")
}

/// The grammar tree represents a Moore/Mealy Machine, where each node is a state of the automaton, 
/// and transitions are made between node based on the input tokens read from the math string to parse.
struct GrammarTree(Vec<GrammarNode>);

impl GrammarTree {
    /// Create a new, empty branch node
    fn create_branch(&mut self) -> NodeId {
        self.0.push(GrammarNode::Branch{cst_map: new_map(), var_map: new_map()});
        //if self.0.len() - 1 == 1413 { panic!("Created 1413!"); }
        self.0.len() - 1
    }

    /// Create a new leaf node, with the given [Reduce], and producing the given [Typecode]
    fn create_leaf(&mut self, reduce: Reduce, typecode: TypeCode) -> NodeId {
        self.0.push(GrammarNode::Leaf{reduce, typecode});
        self.0.len() - 1
    }
    
    /// Retrieves a [GrammarNode] structure, given its [NodeId].
    fn get(&self, node_id: NodeId) -> &GrammarNode {
        &self.0[node_id]
    }

    /// Retrieves a mutable [GrammarNode] structure, given its [NodeId].
    fn get_mut(&mut self, node_id: NodeId) -> &mut GrammarNode {
        &mut self.0[node_id]
    }

    /// Returns the total number of nodes in this grammar tree.
    fn len(&self) -> usize {
        self.0.len()
    }

    /// A utility function to return two nodes, one being a mutable one.
    /// This is used to avoid double-borrowing issues when copying grammar tree branches.
    fn get_two_nodes_mut(&mut self, from_node_id: NodeId, to_node_id: NodeId) -> (&GrammarNode, &mut GrammarNode) {
        if from_node_id < to_node_id {
            let slice = &mut self.0[from_node_id .. to_node_id+1];
            let (first_part, second_part) = slice.split_at_mut(to_node_id-from_node_id);
            (&first_part[0], &mut second_part[0])
        } else {
            let slice = &mut self.0[to_node_id .. from_node_id+1];
            let (first_part, second_part) = slice.split_at_mut(from_node_id-to_node_id);
            (&second_part[0], &mut first_part[0])
        }
    }

    // Copy all branches from `from_node` to `to_node`, adding the provided reduce on the way
    fn copy_branches(&mut self, copy_from_node_id: NodeId, copy_to_node_id: NodeId, add_reduce: Reduce) -> Result<(), NodeId> {
        match self.get_two_nodes_mut(copy_from_node_id, copy_to_node_id) {
            // TODO here we might have to reduce with offset (e.g. ` ( a o b ) `, after ` o ` )
            (GrammarNode::Branch { cst_map, var_map }, GrammarNode::Branch { cst_map: ref mut to_cst_map, var_map: ref mut to_var_map }) => {
                for (symbol, next_node) in cst_map.iter() {
                    if to_cst_map.get(symbol).is_some() { // TODO later use map_try_insert #82766
                        // Skip error here, do nothing for now...
                        //return Err(conflict_next_node.next_node_id);
                        //panic!("Conflict when copying constant grammar branches!");
                    } else {
                        to_cst_map.insert(*symbol, next_node.with_reduce(add_reduce));
                    }
                }
                for (typecode, next_node) in var_map.iter() {
                    if to_var_map.get(typecode).is_some() { // TODO later use map_try_insert #82766
                        // Skip error here, do nothing for now...
                        //return Err(conflict_next_node.next_node_id);
                        //panic!("Conflict when copying variable grammar branches!");
                    } else {
                        to_var_map.insert(*typecode, next_node.with_reduce(add_reduce));
                    }
                }
                Ok(())
            },
            _ => {
                Err(copy_to_node_id)
            }
        }
    }
}

/// The grammar built from the database's syntactic axioms
///
/// It is used to parse metamath statements into [Formula].
/// See [StmtParse] for getting the formula for statements from the database.
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
#[derive(Clone,Copy,Debug,Default,PartialEq)]
struct Reduce {
    label: Label,
    var_count: u8,
    offset: u8,
}

impl Reduce {
    fn new(label: Label, var_count: u8, offset: u8) -> Self {
        Reduce { label, var_count, offset }
    }
}

/// With the current implementation, up to 5 reduce steps can be done in a single transition.
/// This limit is hard-coded here.
type ReduceVec = ArrayVec::<[Reduce; 5]>;

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

#[derive(Clone,Copy)]
struct NextNode {
    next_node_id: NodeId,
    leaf_label: ReduceVec,          // This deals with ambiguity in the grammar, performing one or several reduce then continuing
}

impl NextNode {
    fn new(next_node_id: NodeId) -> Self {
        NextNode { next_node_id, leaf_label: ReduceVec::new() }
    }
    
    fn new_with_reduce_vec(next_node_id: NodeId, leaf_label: ReduceVec) -> Self {
        NextNode { next_node_id, leaf_label }
    }
    
    fn with_reduce(&self, reduce: Reduce) -> Self {
        let mut leaf_label = self.leaf_label;
        leaf_label.insert(0, reduce);
        NextNode { next_node_id: self.next_node_id, leaf_label }
    }

    fn with_reduce_vec(&self, reduce_vec: &ReduceVec) -> Self {
        let mut leaf_label = self.leaf_label;
        for reduce in reduce_vec {
            leaf_label.push(*reduce);
        }
        NextNode { next_node_id: self.next_node_id, leaf_label }
    }
}

#[derive(Clone)]
enum GrammarNode {
    Leaf {
        reduce: Reduce,
        typecode: TypeCode,
        },
    Branch {
        cst_map: HashMap<Symbol, NextNode>,   // Table of choices leading to the next node when a constant is encountered
        var_map: HashMap<TypeCode, NextNode>, // Table of choices leading to the next node when a variable is successfully parsed
    }, 
}

impl Index<SymbolType> for GrammarNode {
    type Output = HashMap<Atom, NextNode>;
    
    fn index(&self, index: SymbolType) -> &Self::Output {
        if let GrammarNode::Branch{cst_map, var_map} = self {
            match index {
                SymbolType::Constant => cst_map,
                SymbolType::Variable => var_map,
            }
        } else {
            panic!("Only index branch nodes!");
        }
    }
}

impl GrammarNode {
    /// Next node
    fn next_node(&self, symbol: Symbol, stype: SymbolType) -> Option<&NextNode> {
        match self {
            GrammarNode::Leaf{..} => None,
            GrammarNode::Branch{cst_map, var_map} => {
                let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
                map.get(&symbol)
            }
        }
    }
}

struct GrammarNodeDebug<'a>(&'a GrammarNode, &'a Arc<Nameset>);
impl fmt::Debug for GrammarNodeDebug<'_> {
    /// Lists the contents of the grammar node
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let nset = self.1;
        match self.0 {
            GrammarNode::Leaf{reduce, typecode} => { write!(f, "Leaf {} {} ({} vars)", as_str(nset.atom_name(*typecode)), as_str(nset.atom_name(reduce.label)), reduce.var_count) },
            GrammarNode::Branch{cst_map, var_map} => {
                write!(f, "Branch CST={{")?;
                for (symbol, node) in cst_map {
                    write!(f, "{}: {:?}", as_str(nset.atom_name(*symbol)), node.next_node_id)?;
                    for reduce in node.leaf_label.into_iter() {
                        write!(f, "({:?} {})", as_str(nset.atom_name(reduce.label)), reduce.var_count)?;
                    }
                    write!(f, ", ")?;
                }
                write!(f, "}} VAR={{")?;
                for (typecode, node) in var_map {
                    write!(f, "{}: {:?}", as_str(nset.atom_name(*typecode)), node.next_node_id)?;
                    for reduce in node.leaf_label.into_iter() {
                        write!(f, "({:?} {})", as_str(nset.atom_name(reduce.label)), reduce.var_count)?;
                    }
                    write!(f, ", ")?;
                }
                write!(f, "}}")
            },
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
        write!(f, "{}: {:?}", node_id, GrammarNodeDebug(&grammar.nodes.0[node_id], nset))
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
                    self.typecodes.push(nset.lookup_symbol(&command[1]).unwrap().atom);
                }
            }
        }
    }

    /// Returns a list of errors that were generated during the grammar
    /// computation.
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
                GrammarNode::Branch{cst_map, ..} => {
                    // It shall be safe to unwrap here, as we shall never insert a branch without a leaf
                    node = cst_map.values().next().unwrap().next_node_id;
                }
                GrammarNode::Leaf{reduce, ..} => {
                    let sa = nset.lookup_label(nset.atom_name(reduce.label)).unwrap().address;
                    return Diagnostic::GrammarAmbiguous(sa);
                }
            }
        }
    }

    fn too_short(map: &HashMap<Symbol,NextNode>, nset: &Arc<Nameset>) -> Diagnostic {
        let expected_symbol = *map.keys().next().unwrap();
        let expected_token = copy_token(nset.atom_name(expected_symbol));
        Diagnostic::ParsedStatementTooShort(expected_token)
    }

    /// Gets the maps of a branch
    fn get_branch(&self, node_id: NodeId) -> (&HashMap<Symbol, NextNode>, &HashMap<TypeCode, NextNode>) {
        if let GrammarNode::Branch{cst_map, var_map} = &self.nodes.get(node_id) {
            (cst_map, var_map)
        } else {
            panic!("Expected branch for node {}!", node_id);
        }
    }

    /// Adds the symbol to the branch, providing the next node, and returns that next node
    fn add_branch(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, leaf: &NextNode) -> Result<NodeId, NodeId> {
        match self.nodes.get_mut(to_node) {
            GrammarNode::Leaf{..} => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
            GrammarNode::Branch{cst_map, var_map} => {
                let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
                match map.get(&symbol) {
                    Some(prev_node) => Err(prev_node.next_node_id), // Error : We want to add a leaf note, but there is already a branch.
                    None => { map.insert(symbol, *leaf); Ok(leaf.next_node_id) },
                }
            }
        }
    }

    /// Adds the symbol to the branch, providing a reduce, and returns the next node
    fn add_branch_with_reduce(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, add_reduce: ReduceVec) -> Result<NodeId, NodeId> {
        match self.nodes.get_mut(to_node) {
            GrammarNode::Leaf{..} => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
            GrammarNode::Branch{cst_map, var_map} => {
                let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
                match map.get(&symbol) {
                    Some(prev_node) => {
                        if prev_node.leaf_label != add_reduce {
                            Err(prev_node.next_node_id)
                        } else {
                            Ok(prev_node.next_node_id)
                        }
                    },
                    None => {
                        let new_node_id = self.nodes.create_branch();
                        // here we have to re-borrow from self after the creation, because the previous var_map and cst_map may not be valid pointers anymore
                        if let GrammarNode::Branch{cst_map, var_map} = self.nodes.get_mut(to_node) {
                            let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
                            map.insert(symbol, NextNode::new_with_reduce_vec(new_node_id, add_reduce));
                            Ok(new_node_id)
                        } else {
                            panic!("Shall not happen!");
                        }
                    },
                }
            }
        }
    }

    /// Build the parse tree, marking variables with their types
    fn add_axiom(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader, type_conversions: &mut Vec<(TypeCode,TypeCode,Label)>) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter().peekable();

        // Atom for this axiom's label.
        let this_label = names.lookup_label(sref.label()).unwrap().atom;
        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let this_typecode = nset.get_atom(tokens.next().unwrap().slice); 

        // In case of a non-syntax axiom, skip it.
        if this_typecode == self.provable_type { return Ok(()); }

        // Detect "type conversion" syntax axioms: ~cv for set.mm
        if sref.math_len() == 2 {
            let token_ptr = sref.math_at(1).slice;
            let symbol = names.lookup_symbol(token_ptr).unwrap();
            if symbol.stype == SymbolType::Variable {
                type_conversions.push((names.lookup_float(token_ptr).unwrap().typecode_atom, this_typecode, this_label));
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
                    let leaf_node_id = self.nodes.create_leaf(Reduce::new(this_label, var_count, 0), this_typecode);
                    self.add_branch(node, atom, symbol.stype, &NextNode::new(leaf_node_id))
                    },
            } {
                Ok(next_node) => { node = next_node; },
                Err(conflict_node) => { return Err(self.ambiguous(conflict_node, nset)); },
            }
        };
        Ok(())
    }

    /// Add a floating variable node to the parse tree.
    fn add_floating(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
        let mut tokens = sref.math_iter();

        // Atom for this flaot's label.
        let this_label = names.lookup_label(sref.label()).unwrap().atom;
        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let this_typecode = nset.get_atom(tokens.next().unwrap().slice); 

        // Float shall not be of the provable typecode.
        if this_typecode == self.provable_type { return Err(Diagnostic::GrammarProvableFloat); }

        // We will add this floating declaration to the grammar tree
        let leaf_node = self.nodes.create_leaf(Reduce::new(this_label, 0, 0), this_typecode);

        // If is safe to unwrap here since parser has already checked.
        let token = tokens.next().unwrap();
        let symbol = names.lookup_symbol(token.slice).unwrap();

        debug!("========== Statement {:?} ==========", as_str(nset.statement_name(sref)));

        match self.nodes.get_mut(self.root) {
            // We ignore the ambiguity in floats, since they are actually frame dependent.
            GrammarNode::Branch{cst_map, ..} => match cst_map.insert(symbol.atom, NextNode::new(leaf_node)) {
                None => Ok(()),
                Some(_) => Ok(()), // Err(self.ambiguous(conflict_node.next_node_id, nset)), 
            }
            _ => panic!("Root node shall be a branch node!"),
        }
    }

    /// Handle type conversion:
    /// Go through each node and everywhere there is to_typecode(`class`), put a from_typecode(`setvar`), 
    /// pointing to a copy of the next node with a leaf to first do a `cv`
    fn perform_type_conversion(&mut self, from_typecode: TypeCode, to_typecode: TypeCode, label: Label, nset: &Arc<Nameset>) -> Result<(), Diagnostic> {
        let len = self.nodes.len();
        for node_id in 0 .. len {
            match self.nodes.get(node_id) {
                GrammarNode::Branch { var_map, .. } => {
                    if let Some(ref_next_node) = var_map.get(&to_typecode) {
                        let next_node_id = ref_next_node.next_node_id;
                        match var_map.get(&from_typecode) {
                            None => {
                                // No branch exist for the converted type: create one, with a leaf label.
                                debug!("Type Conv adding to {} node id {}", node_id, next_node_id);
                                debug!("{:?}", GrammarNodeIdDebug(self, node_id, nset));
                                let mut leaf_label = ref_next_node.leaf_label;
                                leaf_label.insert(0, Reduce::new(label, 1, 0));
                                self.add_branch(node_id, from_typecode, SymbolType::Variable, &NextNode{ next_node_id, leaf_label }).unwrap();
                            },
                            Some(existing_next_node) => {
                                // A branch for the converted type already exist: add the conversion to that branch!
                                debug!("Type Conv copying to {} node id {}", next_node_id, existing_next_node.next_node_id);
                                debug!("{:?}", GrammarNodeIdDebug(self, next_node_id, nset));
                                debug!("{:?}", GrammarNodeIdDebug(self, existing_next_node.next_node_id, nset));
                                let existing_next_node_id = existing_next_node.next_node_id;
                                self.nodes.copy_branches(next_node_id, existing_next_node_id, Reduce::new(label, 1, 0)).unwrap();
                            },
                        }
                    }
                },
                _ => {}, // Nothing to do for leafs
            }
        }
        Ok(())
    }

    fn next_var_node(&self, node_id: NodeId, typecode: TypeCode) -> Option<(NodeId, &ReduceVec)> {
        match self.nodes.get(node_id) {
            GrammarNode::Branch { var_map, .. } => match var_map.get(&typecode) {
                Some(NextNode { next_node_id, leaf_label }) => Some((*next_node_id, leaf_label)),
                _ => None
            },
            _ => None
        }
    }

    /// Recursively clone the whole grammar tree starting from add_from_node_id
    //  This implementation may needlessly duplicate some nodes: it creates new ones everytime, not checking if a duplicate was already created and could be reused.
    //  A cleverer implementation would store the duplicates created, for example in a hashmap, and reuse them.
    //  Branch nodes are recursively copied.
    //  The `make_final` argument is a function building the final node from the reduce of the found leaf node and the final typecode.
    fn clone_branches<F>(&mut self, add_from_node_id: NodeId, add_to_node_id: NodeId, nset: &Arc<Nameset>, mut stored_reduces: ReduceVec, make_final: F) where F: FnOnce(&ReduceVec, TypeCode) -> NextNode + Copy {
        debug!("Clone {} to {}", add_from_node_id, add_to_node_id);
        debug!("{:?}", GrammarNodeIdDebug(self, add_from_node_id, nset));
        debug!("{:?}", GrammarNodeIdDebug(self, add_to_node_id, nset));
        for stype in &[SymbolType::Constant, SymbolType::Variable] {
            let map = &(*self.nodes.get(add_from_node_id)).clone()[*stype]; // can we prevent cloning here?
            if *stype == SymbolType::Variable { increment_offsets(&mut stored_reduces); }
            for (symbol, next_node) in map {
                if next_node.next_node_id == add_to_node_id { continue; } // avoid infinite recursion
                if let GrammarNode::Leaf { reduce: r, typecode } = self.nodes.get(next_node.next_node_id) {
                    let mut reduce_vec = ReduceVec::new();
                    for reduce in stored_reduces { reduce_vec.push(reduce); }
                    reduce_vec.push(*r);
                    debug!("LEAF for {} to {} {:?}", add_from_node_id, add_to_node_id, reduce_vec);
                    let final_node = make_final(&reduce_vec, *typecode);
                    match self.add_branch(add_to_node_id, *symbol, *stype, &final_node) {
                        Ok(_) => {},
                        Err(conflict_node_id) => {
                            debug!("Conflict Node = {}", conflict_node_id);
                            // conflict node id = 394 : CST={): 395, } VAR={}
                            // next_node_id = 16: CST={\/: 23, <->: 20, -/\: 35, /\: 26, ->: 17, \/_: 38, } VAR={}
                            // reduce = wbr 3
                            // expected result: 394 : CST={): 395, \/: (wbr 3) 23, <->: (wbr 3) 20, ...} VAR={}
                            self.clone_with_reduce_vec(final_node.next_node_id, conflict_node_id, &reduce_vec);
                        }, 
                    }
                } else {
                    debug!("BRANCH for {} to {} {:?}", add_from_node_id, add_to_node_id, next_node.leaf_label);
                    let new_next_node_id = match self.add_branch_with_reduce(add_to_node_id, *symbol, *stype, next_node.leaf_label) {
                        Ok(new_next_node_id) => new_next_node_id,
                        Err(new_next_node_id) => {
                            // This is the case where there is already a branch, with a different reduce.
                            // In that case, we have to store the reduce until the copy is finished.
                            for reduce in next_node.leaf_label {
                                debug!(">> Storing {:?}", reduce);
                                stored_reduces.push(reduce);
                            }
                            new_next_node_id
                        },
                    };
                    self.clone_branches(next_node.next_node_id, new_next_node_id, nset, stored_reduces, make_final);
                }
            }
        }
    }

    // compare this with "copy_branches"!
    fn clone_with_reduce_vec(&mut self, add_from_node_id: NodeId, add_to_node_id: NodeId, reduce_vec: &ReduceVec) {
        if add_from_node_id == add_to_node_id { return; } // nothing to clone here!
        debug!("Clone with reduce {} to {}", add_from_node_id, add_to_node_id);
        for stype in &[SymbolType::Constant, SymbolType::Variable] {
            let map = &(*self.nodes.get(add_from_node_id)).clone()[*stype]; // can we prevent cloning here?
            for (symbol, next_node) in map {
                self.add_branch(add_to_node_id, *symbol, *stype, &next_node.with_reduce_vec(reduce_vec)).expect("Double conflict!");
            }
        }
    }

    /// Expand the tree at the given node, for the given symbol.  This means cloning/inserting from the root tree at that symbol, until a given typecode is obtained, into the given node
    /// This is used in order to ensure that a given sequence is in the grammar tree, like `<. <.`, which does not correspond to a single syntax axiom
    fn expand_tree(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, nset: &Arc<Nameset>) -> NodeId {
        let next_node_id_from_root = self.nodes.get(self.root).next_node(symbol, stype).expect("Expanded formula cannot be parsed from root node!").next_node_id;
        let node_from_root = self.nodes.get(next_node_id_from_root).clone();
        let new_node_id = self.add_branch_with_reduce(to_node, symbol, stype, ReduceVec::new()).unwrap();
        self.clone_branches(next_node_id_from_root, new_node_id, nset, ReduceVec::new(), |rv,t| {
            node_from_root.next_node(t, SymbolType::Variable).expect("Expanded node's typecode not available!").with_reduce_vec(rv)
        });
        self.nodes.get(to_node).next_node(symbol, stype).unwrap().next_node_id
    }

    /// Handle common prefixes. 
    /// For example in set.mm, ` (  A ` is a prefix common to ` ( A X. B ) ` and ` ( A e. B /\ T. ) `
    /// The first is a notation, but would "shadow" the second option.
    /// The command `ambiguous_prefix ( A   =>   ( ph ;` handles this.
    /// 
    // NOTE: 
    //    Common prefix must be constant only, and both first differing symbols must be variables
    fn handle_common_prefixes(&mut self, prefix: &[Token], shadows: &[Token], nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
        let mut node_id = self.root;
        let mut index = 0;
        
        // First we follow the tree to the common prefix
        loop {
            if prefix[index] != shadows[index] { break; }
            // TODO use https://rust-lang.github.io/rfcs/2497-if-let-chains.html once it's out!
            if let GrammarNode::Branch { cst_map, .. } = self.nodes.get(node_id) {
                let prefix_symbol = nset.lookup_symbol(prefix[index].as_ref()).unwrap().atom;
                let next_node = cst_map.get(&prefix_symbol).expect("Prefix cannot be parsed!");
                node_id = next_node.next_node_id;
                index += 1;
            }
            else {
                panic!("Leaf reached while parsing common prefixes!");
            }
        }

        // We note the typecode and next branch of the "shadowed" prefix
        let shadowed_typecode = names.lookup_float(&shadows[index]).unwrap().typecode_atom;
        let (shadowed_next_node, _) = self.next_var_node(node_id, shadowed_typecode).expect("Shadowed prefix cannot be parsed!");
        
        // We note what comes after the shadowing typecode, both if we start from the prefix and if we start from the root
        let mut add_from_node_id = self.root;
        let mut shadowing_atom:Atom;
        let mut shadowing_stype;
        for token in &prefix[index..] {
            let lookup_symbol = names.lookup_symbol(token).unwrap();
            debug!("Following prefix {}, at {} / {}", as_str(token), node_id, add_from_node_id);
            shadowing_stype = lookup_symbol.stype;
            shadowing_atom = match shadowing_stype {
                SymbolType::Constant => lookup_symbol.atom,
                SymbolType::Variable => names.lookup_float(token).unwrap().typecode_atom,
            };
            node_id = self.nodes.get(node_id).next_node(shadowing_atom, shadowing_stype).expect("Prefix cannot be parsed!").next_node_id;
            add_from_node_id = match self.nodes.get(add_from_node_id).next_node(shadowing_atom, shadowing_stype) {
                Some(next_node) => { next_node.next_node_id },
                None => { self.expand_tree(add_from_node_id, shadowing_atom, shadowing_stype, nset) },
            }
        }

        debug!("Shadowed token: {}", as_str(&shadows[index]));
        debug!("Handle shadowed next node {}, typecode {:?}", shadowed_next_node, shadowed_typecode);
        debug!("Handle shadowed next node from root {}, typecode {:?}", add_from_node_id, shadowed_typecode);
        debug!("Handle shadowing next node {}", node_id);

        // Then we copy each of the next branch of the shadowed string to the shadowing branch
        // If the next node is a leaf, instead, we add a leaf label, and point to the next
        let make_final = |rv: &ReduceVec, _| {
            NextNode { next_node_id: shadowed_next_node, leaf_label: *rv }
        };
        match self.nodes.get(add_from_node_id) {
            GrammarNode::Branch {..} => {
                self.clone_branches(add_from_node_id, node_id, nset, ReduceVec::new(), make_final);
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
    ///   $( $j ambiguous_prefix ( A   =>   ( ph ;
    ///         type_conversions;
    ///         ambiguous_prefix ( x e. A   =>   ( ph ;
    ///         ambiguous_prefix { <.   =>   { A ;
    ///         ambiguous_prefix { <. <.   =>   { A ;
    ///   $)
    /// `
    fn handle_commands(&mut self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>, names: &mut NameReader, type_conversions: &[(TypeCode,TypeCode,Label)]) -> Result<(), (StatementAddress, Diagnostic)> {
        for (address, command) in sset.parser_commands() {
            assert!(!command.is_empty(), "Empty parser command!");
            if &command[0].as_ref() == b"syntax" {
                if command.len() == 4 && &command[2].as_ref() == b"as" {
                    // syntax '|-' as 'wff';
                    self.provable_type = nset.lookup_symbol(&command[1]).unwrap().atom;
                    self.typecodes.push(nset.lookup_symbol(&command[3]).unwrap().atom);
                } else if command.len() == 2 {
                    // syntax 'setvar';
                    self.typecodes.push(nset.lookup_symbol(&command[1]).unwrap().atom);
                }
            }
            // Handle Ambiguous prefix commands
            if &command[0].as_ref() == b"ambiguous_prefix" {
                let split_index = command.iter().position(|t| t.as_ref() == b"=>").expect("'=>' not present in 'ambiguous_prefix' command!");
                let (prefix, shadows) = command.split_at(split_index);
                if let Err(diag) = self.handle_common_prefixes(&prefix[1..], &shadows[1..], nset, names) { return Err((address, diag)) }
            }
            // Handle replacement schemes
            if &command[0].as_ref() == b"type_conversions" {
                for (from_typecode, to_typecode, label) in type_conversions {
                    if let Err(diag) = self.perform_type_conversion(*from_typecode, *to_typecode, *label, nset) { return Err((address, diag)) }
                }
            }
        }
        Ok(())
    }

    fn do_shift(&self, sref: &StatementRef, ix: &mut TokenIndex, nset: &Arc<Nameset>, names: &mut NameReader) {
        if self.debug {
            let token = sref.math_at(*ix);
            let symbol = names.lookup_symbol(token.slice).unwrap();
            debug!("   SHIFT {:?}", as_str(nset.atom_name(symbol.atom)));
        }
        *ix += 1;
    }

    fn do_reduce(&self, formula_builder: &mut FormulaBuilder, reduce: Reduce, nset: &Arc<Nameset>) {
        debug!("   REDUCE {:?}", as_str(nset.atom_name(reduce.label)));
        formula_builder.reduce(reduce.label, reduce.var_count, reduce.offset);
        //formula_builder.dump(nset);
        debug!(" {:?} {} {}", as_str(nset.atom_name(reduce.label)), reduce.var_count, reduce.offset);
    }

    fn parse_formula<'a>(&self, start_node: NodeId, sref: &StatementRef, ix: &mut TokenIndex, formula_builder: &mut FormulaBuilder, expected_typecodes: &'a[&'a TypeCode], nset: &Arc<Nameset>, names: &mut NameReader) -> Result<TypeCode, Diagnostic> {
        let mut node = start_node;
        loop {
            match self.nodes.get(node) {
                GrammarNode::Leaf{reduce, typecode} => {
                    // We found a leaf: REDUCE
                    self.do_reduce(formula_builder, *reduce, nset);
                    if expected_typecodes.iter().any(|&t| *t==*typecode) {
                        if *ix == sref.math_len() { return Ok(*typecode); }
                        else { println!("Check this out! {} < {} for {:?}", *ix, sref.math_len(), as_str(nset.statement_name(sref))); return Ok(*typecode); }
                    } else {
                        debug!(" ++ Wrong type obtained, continue.");
                        let (next_node_id, leaf_label) = self.next_var_node(self.root, *typecode).unwrap(); // TODO error case
                        for reduce in leaf_label.into_iter() {
                            self.do_reduce(formula_builder, *reduce, nset);
                        }
                        node = next_node_id;
                    }
                },
                GrammarNode::Branch{cst_map, var_map} => {
                    if *ix == sref.math_len() { return Err(Grammar::too_short(cst_map, nset)); }
                    let token = sref.math_at(*ix);
                    let symbol = names.lookup_symbol(token.slice).unwrap();
                    debug!("   {:?}", as_str(nset.atom_name(symbol.atom)));

                    match cst_map.get(&symbol.atom) {
                        Some(NextNode { next_node_id, leaf_label }) => {
                            // Found an atom matching one of our next nodes: First optionally REDUCE and continue
                            for reduce in leaf_label.into_iter() {
                                self.do_reduce(formula_builder, *reduce, nset);
                            }

                            // Found an atom matching one of our next nodes: SHIFT, to the next node
                            self.do_shift(sref, ix, nset, names);
                            node = *next_node_id;
                            debug!("   Next Node: {:?}", node);
                        },
                        None => {
                            // No matching constant, search among variables
                            if var_map.is_empty() || node == self.root {
                                return Err(Diagnostic::UnparseableStatement(token.index()));
                            }

                            debug!(" ++ Not in CST map, recursive call expecting {:?}", var_map.keys());
                            let typecode = self.parse_formula(self.root, sref, ix, formula_builder, var_map.keys().collect::<Vec<&TypeCode>>().as_slice(), nset, names)?;
                            debug!(" ++ Finished parsing formula, found typecode {:?}, back to {}", as_str(nset.atom_name(typecode)), node);
                            match var_map.get(&typecode) {
                                Some(NextNode { next_node_id, leaf_label }) => {
                                    // Found a sub-formula: First optionally REDUCE and continue
                                    for reduce in leaf_label.into_iter() {
                                        self.do_reduce(formula_builder, *reduce, nset);
                                    }

                                    node = *next_node_id;
                                    debug!("   Next Node: {:?}", node);
                                },
                                None => {
                                    // No match found, try as a prefix of a larger formula
                                    let (_, var_map_2) = self.get_branch(self.root);
                                    match var_map_2.get(&typecode) {
                                        Some(NextNode { next_node_id: next_node_id_2, leaf_label: leaf_label_2 }) => {
                                            // Found a sub-formula: First optionally REDUCE and continue
                                            for reduce in leaf_label_2.into_iter() {
                                                self.do_reduce(formula_builder, *reduce, nset);
                                            }
        
                                            // Found and reduced a sub-formula, to the next node
                                            debug!(" ++ Considering prefix, switching to {}", next_node_id_2);
                                            let typecode = self.parse_formula(*next_node_id_2, sref, ix, formula_builder, var_map.keys().collect::<Vec<&TypeCode>>().as_slice(), nset, names)?;
                                            debug!(" ++ Finished parsing formula, found typecode {:?}, back to {}", as_str(nset.atom_name(typecode)), node);
                                            match var_map.get(&typecode) {
                                                Some(NextNode { next_node_id, leaf_label }) => {
                                                    // Found a sub-formula: First optionally REDUCE and continue
                                                    for reduce in leaf_label.into_iter() {
                                                        self.do_reduce(formula_builder, *reduce, nset);
                                                    }
                
                                                    node = *next_node_id;
                                                    debug!("   Next Node: {:?}", node);
                                                },
                                                None => {
                                                    // Still no match found, error.
                                                    return Err(Diagnostic::UnparseableStatement(token.index()));
                                                },
                                            }
                                        },
                                        _ => {
                                            // Still no match found, error.
                                            return Err(Diagnostic::UnparseableStatement(token.index()));
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            }
        }
    }

    fn parse_statement(&self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<Option<Formula>, Diagnostic> {
        if sref.math_len() == 0 {
            return Err(Diagnostic::ParsedStatementNoTypeCode);
        }

        // Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
        let typecode = nset.get_atom(sref.math_at(0).slice); 
        let mut expected_typecode = typecode; 

        // Skip syntactic axioms 
        if sref.statement_type() == StatementType::Axiom && expected_typecode != self.provable_type { return Ok(None) }

        // If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
        if expected_typecode == self.provable_type { expected_typecode = self.logic_type; }

        // At the time of writing, there are only 3 statements which are not provable but "syntactic theorems": weq, wel and bj-0
        let mut formula_builder = FormulaBuilder::default();

        debug!("--------- Statement {:?} ---------", as_str(nset.statement_name(sref)));

        self.parse_formula(self.root, sref, &mut 1, &mut formula_builder, vec![&expected_typecode].as_slice(), nset, names)?;
        Ok(Some(formula_builder.build(typecode)))
    }

    /// Lists the contents of the grammar's parse table. This can be used for debugging.
    pub fn dump(&self, nset: &Arc<Nameset>) {
        println!("Grammar tree has {:?} nodes.", self.nodes.len());
        for i in 0 .. self.nodes.len() {
            println!("{:?}", GrammarNodeIdDebug(self, i, nset));
        }
    }
    
    #[cfg(feature = "dot")]
    /// Exports the grammar tree in the "dot" format. See https://www.graphviz.org/doc/info/lang.html
    /// This dot file can then be converted to an SVG image using ` dot -Tsvg -o grammar.svg grammar.dot `
    pub fn export_dot(&self, nset: &Arc<Nameset>, write: &mut File) -> Result<(), ExportError> {
        let mut dot_writer = DotWriter::from(write);
        let mut digraph = dot_writer.digraph();
        for node_id in 0 .. self.nodes.len() {
            match &self.nodes.0[node_id] {
                GrammarNode::Leaf{reduce,..} => { 
                    digraph
                        .node_named(as_string(node_id))
                        .set_shape(Shape::Mdiamond)
                        .set_label(format!("{} {}", node_id, escape(as_str(nset.atom_name(reduce.label)))).as_str()); // , escape(as_str(nset.atom_name(*typecode))), reduce.var_count
                    },
                GrammarNode::Branch{cst_map, var_map} => {
                    for (symbol, node) in cst_map {
                        let mut buf = String::new();
                        for reduce in node.leaf_label.into_iter() {
                            if reduce.offset > 0 { write!(buf, "{}({}) / ", as_str(nset.atom_name(reduce.label)), reduce.offset)?; }
                            else { write!(buf, "{} / ", as_str(nset.atom_name(reduce.label)))?; }
                        }
                        write!(buf, escape(as_str(nset.atom_name(*symbol))).as_str())?;
                        digraph
                            .edge(as_string(node_id), as_string(node.next_node_id))
                            .attributes()
                            .set_label(buf.as_str())
                            .set_font("Courier");
                    }
                    for (typecode, node) in var_map {
                        let mut buf = String::new();
                        buf.write_str(escape(as_str(nset.atom_name(*typecode))).as_str())?;
                        for reduce in node.leaf_label.into_iter() {
                            if reduce.offset > 0 { write!(buf, " / {}({})", as_str(nset.atom_name(reduce.label)),reduce.offset)?; }
                            else { write(buf, " / {}", as_str(nset.atom_name(reduce.label)))?; }
                        }
                        digraph
                            .edge(as_string(node_id), as_string(node.next_node_id))
                            .attributes()
                            .set_label(buf.as_str())
                            .set_color(Color::Blue)
                            .set_font_color(Color::Blue);
                    }
                },
            }
        }
        Ok(())
    }
}

/// Called by [crate::Database] to build the grammar from the syntax axioms in the database.
/// 
/// The provided `sset`, and `nset` shall be the result of previous phases over the database.
/// The provided `grammar` will be updated with the results of the grammar build.
/// The grammar can then be used to parse the statements of the database (see [parse_statements]), or to parse a single statement.
/// Use [Grammar::default] to get an initial state.
pub(crate)  fn build_grammar<'a>(grammar: &mut Grammar, sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>) {
    // Read information about the grammar from the parser commands
    grammar.initialize(sset, nset);
    grammar.root = grammar.nodes.create_branch();

    let mut names = NameReader::new(nset);
    let mut type_conversions = Vec::new();

    // Build the initial grammar tree, just form syntax axioms and floats.
    let segments = sset.segments();
    assert!(!segments.is_empty(), "Parse returned no segment!");
    for segment in segments.iter() {
        for sref in *segment {
            if let Err(diag) = match sref.statement_type() {
                StatementType::Axiom => grammar.add_axiom(&sref, nset, &mut names, &mut type_conversions),
                StatementType::Floating => grammar.add_floating(&sref, nset, &mut names),
                _ => Ok(())
            } {
                grammar.diagnostics.insert(sref.address(), diag);
            }
        }
    }

    // Post-treatement (type conversion and ambiguous prefix) as instructed by $j parser commands
    if let Err((address, diag)) = grammar.handle_commands(sset, nset, &mut names, &type_conversions) {
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
/// The parse tree for a given statement can then be obtained through [StmtParse::get_formula].
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
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sps in self.segments.values() {
            for (&sa, &ref diag) in &sps.diagnostics {
                out.push((sa, diag.clone()));
            }
        }
        out
    }

    /// Writes down all formulas
    pub fn dump(&self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) {
        println!("Formula Dump:");
        for sps in self.segments.values() {
            for (&sa, &ref formula) in &sps.formulas {
                let sref = sset.statement(sa);
                println!("{}: {}", as_str(nset.statement_name(&sref)), formula.display(sset, nset));
            }
        }
    }

    /// Returns the formula for a given statement
    pub fn get_formula(&self, sref: &StatementRef) -> Option<&Formula> {
        let stmt_parse_segment = self.segments.get(&sref.segment().id)?;
        stmt_parse_segment.formulas.get(&sref.address())
    }
}

/// Data generated by the statement parsing process for a single segment.
struct StmtParseSegment {
    _source: Arc<Segment>,
    diagnostics: HashMap<StatementAddress, Diagnostic>,
    formulas: HashMap<StatementAddress, Formula>,
}

/// Runs statement parsing for a single segment.
fn parse_statements_single<'a>(sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>, names: &mut NameReader, grammar: &Arc<Grammar>, sid: SegmentId) -> StmtParseSegment {
    let segment = sset.segment(sid);
    let mut diagnostics = new_map();
    let mut formulas = new_map();

    for sref in segment {
        match match sref.statement_type() {
            StatementType::Axiom | StatementType::Essential | StatementType::Provable => grammar.parse_statement(&sref, nset, names),
            _ => Ok(None)
        } {
            Err(diag) => {
                warn!(" FAILED to parse {}!", as_str(nset.statement_name(&sref)));
                diagnostics.insert(sref.address(), diag);
                break; // inserted here to stop at first error!
            },
            Ok(Some(formula)) => {
                formulas.insert(sref.address(), formula);
            },
            _ => {},
        }
    }

    StmtParseSegment {
        _source: (*segment).clone(),
        diagnostics,
        formulas,
    }
}

/// Called by [crate::Database] to parse all the statements in the database
/// 
/// The provided `segments`, `nset`, and `grammar` shall be the result of previous phases over the database.
/// The provided `stmt_parse` will be updated with the results of the parse.
/// The parse tree for a given statement can then be obtained through [StmtParse::get_formula].
/// Use [StmtParse::default] to get an initial state. Like for several other phases, this occurs in parallel.
pub(crate) fn parse_statements<'a>(stmt_parse: &mut StmtParse, segments: &'a Arc<SegmentSet>, nset: &Arc<Nameset>, grammar: &Arc<Grammar>) {
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
            (id, Arc::new(parse_statements_single(&segments2, &nset, &mut names, &grammar, id)))
        }));
    }

    stmt_parse.segments.clear();
    for promise in ssrq {
        let (id, arc) = promise.wait();
        stmt_parse.segments.insert(id, arc);
    }
}
