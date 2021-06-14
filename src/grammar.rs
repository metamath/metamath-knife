//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.
//!

use crate::diag::Diagnostic;
use crate::nameck::NameReader;
use crate::nameck::Nameset;
use crate::parser::Segment;
use crate::parser::SegmentId;
use crate::parser::StatementAddress;
use crate::parser::StatementType;
use crate::parser::StatementRef;
use crate::parser::SymbolType;
use crate::parser::TokenIndex;
use crate::parser::as_str;
use crate::parser::copy_token;
use crate::segment_set::SegmentSet;
use crate::formula::Symbol;
use crate::formula::TypeCode;
use crate::formula::Label;
use crate::formula::Formula;
use crate::formula::FormulaBuilder;
use std::sync::Arc;
use crate::util::HashMap;
use crate::util::new_map;


type NodeId = usize;

struct GrammarTree(Vec<GrammarNode>);

impl GrammarTree {
	fn create_branch(&mut self) -> NodeId {
	    self.0.push(GrammarNode::Branch{cst_map: new_map(), var_map: new_map()});
	    self.0.len() - 1
	}

	fn create_leaf(&mut self, label: Label, var_count: u8, typecode: TypeCode) -> NodeId {
	    self.0.push(GrammarNode::Leaf{label, var_count, typecode});
	    self.0.len() - 1
	}
	
	fn get(&self, node_id: NodeId) -> &GrammarNode {
		&self.0[node_id]
	}

	fn get_mut(&mut self, node_id: NodeId) -> &mut GrammarNode {
		&mut self.0[node_id]
	}

	fn len(&self) -> usize {
		self.0.len()
	}

	// Copy all branches from `from_node` to `to_node`, adding the provided leaf label on the way
	fn copy_branches(&mut self, copy_from_node_id: NodeId, copy_to_node_id: NodeId, set_leaf_label: Option<(Label, u8)>) -> Result<(), NodeId> {
		let (from_node, to_node) = if copy_from_node_id < copy_to_node_id {
			let slice = &mut self.0[copy_from_node_id .. copy_to_node_id+1];
			let (first_part, second_part) = slice.split_at_mut(copy_to_node_id-copy_from_node_id);
			(&first_part[0], &mut second_part[0])
		} else {
			let slice = &mut self.0[copy_to_node_id .. copy_from_node_id+1];
			let (first_part, second_part) = slice.split_at_mut(copy_from_node_id-copy_to_node_id);
			(&second_part[0], &mut first_part[0])
		};
		match (to_node, from_node) {
			(GrammarNode::Branch { cst_map: ref mut to_cst_map,.. }, GrammarNode::Branch { cst_map,.. }) => {
				for (symbol, next_node) in cst_map.iter() {
					if let Some(conflict_next_node) = to_cst_map.insert(*symbol, next_node.with_leaf_label(set_leaf_label)) {
						return Err(conflict_next_node.next_node_id);
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

/** The Grammar built from the database's syntactic axioms */
pub struct Grammar {
	provable_type: TypeCode,
	logic_type: TypeCode,
	typecodes: Vec<TypeCode>,
	nodes: GrammarTree,
	root: NodeId, // The root of the Grammar tree
	diagnostics: HashMap<StatementAddress, Diagnostic>,
	debug: bool,
}

#[derive(Clone,Copy,Debug)]
struct NextNode {
	next_node_id: NodeId,
	leaf_label: Option<(Label, u8)>,          // This deals with ambiguity in the grammar, performing a reduce then continuing
}

impl NextNode {
	fn new(next_node_id: NodeId) -> Self {
		NextNode { next_node_id, leaf_label: None }
	}
	
	fn with_leaf_label(&self, leaf_label: Option<(Label, u8)>) -> Self {
		NextNode { next_node_id: self.next_node_id, leaf_label }
	}
}

enum GrammarNode {
	Leaf {
		label: Label,
		var_count: u8,
		typecode: TypeCode,
		},
	Branch {
		cst_map: HashMap<Symbol, NextNode>,   // Table of choices leading to the next node when a constant is encountered
		var_map: HashMap<TypeCode, NextNode>, // Table of choices leading to the next node when a variable is successfully parsed
	}, 
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
			debug: true,
		}
	}
}

impl Grammar {
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
				GrammarNode::Leaf{label, ..} => {
					let sa = nset.lookup_label(nset.atom_name(*label)).unwrap().address;
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
	
	/// Adds the symbol to the branch, and returns the next node
	fn add_branch(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, leaf: Option<NextNode>) -> Result<NodeId, NodeId> {
		match self.nodes.get_mut(to_node) {
			GrammarNode::Leaf{..} => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
			GrammarNode::Branch{cst_map, var_map} => {
				let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
				match leaf {
					Some(ref leaf_node) => {
						match map.insert(symbol, *leaf_node) {
							Some(prev_node) => Err(prev_node.next_node_id), // Error : We want to add a leaf note, but there is already a branch.
							None => Ok(leaf_node.next_node_id),
						}
					},
					None => {
						match map.get(&symbol) {
							Some(prev_node) => Ok(prev_node.next_node_id),
							None => {
								let new_node_id = self.nodes.create_branch();
								if let GrammarNode::Branch{cst_map, var_map} = self.nodes.get_mut(to_node) {
									let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
									map.insert(symbol, NextNode::new(new_node_id));
									Ok(new_node_id)
								} else {
									panic!("Shall not happen!");
								}
							},
						}
					}
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
			let next_leaf = match &tokens.peek() {
				Some(_) => None,
				None => Some(NextNode::new(self.nodes.create_leaf(this_label, var_count, this_typecode))),
			};
			match self.add_branch(node, atom, symbol.stype, next_leaf) {
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
		let leaf_node = self.nodes.create_leaf(this_label, 0, this_typecode);

		// If is safe to unwrap here since parser has already checked.
		let token = tokens.next().unwrap();
		let symbol = names.lookup_symbol(token.slice).unwrap();

		if self.debug {
			println!("\nStatement {:?}\n---------", as_str(nset.statement_name(sref)));
		}

		match self.nodes.get_mut(self.root) {
			GrammarNode::Branch{cst_map, ..} => match cst_map.insert(symbol.atom, NextNode::new(leaf_node)) {
				None => Ok(()),
				Some(conflict_node) => Err(self.ambiguous(conflict_node.next_node_id, nset)),
			}
			_ => panic!("Root node shall be a branch node!"),
		}
	}

	/// Handle type conversion:
	/// Go through each node and everywhere there is to_typecode(`class`), put a from_typecode(`setvar`), 
	/// pointing to a copy of the next node with a leaf to first do a `cv`
	fn perform_type_conversion(&mut self, from_typecode: TypeCode, to_typecode: TypeCode, label: Label) -> Result<(), Diagnostic> {
		let len = self.nodes.len();
		for node_id in 0 .. len {
			match &self.nodes.get(node_id) {
				GrammarNode::Branch { var_map, .. } => {
					if let Some(ref_next_node_id) = var_map.get(&to_typecode) {
						let next_node_id = ref_next_node_id.next_node_id;
						match var_map.get(&from_typecode) {
							None => {
								// No branch exist for the converted type: create one, with a leaf label.
								println!("{}: {} class None setvar", node_id, next_node_id);
								self.add_branch(node_id, from_typecode, SymbolType::Variable, Some(NextNode{
									next_node_id, leaf_label: Some((label, 1)),
								}));
							},
							Some(existing_next_node) => {
								// A branch for the converted type already exist: add the conversion to that branch!
								println!("{}: {} class {} setvar", node_id, next_node_id, existing_next_node.next_node_id);
								self.nodes.copy_branches(next_node_id, existing_next_node.next_node_id, Some((label, 1)));
								
							},
						}


					}
				},
				_ => {}, // Nothing to do for leafs
			}
		}
		Ok(())
	}

					
/*
						let add_to_node_id = match var_map.get(&from_typecode) {
							None => self.add_branch(node_id, from_typecode, SymbolType::Variable, None),
							Some(existing_next_node_id) => Ok(existing_next_node_id.next_node_id),
						}.unwrap();
						self.nodes.copy_branch(next_node_id, add_to_node_id, Some((label, 1)));




						match self.nodes.get2(next_node_id, add_to_node_id) {
							(GrammarNode::Branch { cst_map, leaf_label: None,.. }, GrammarNode::Branch { cst_map: ref mut to_cst_map, leaf_label: ref mut to_leaf_label,.. }) => {
								//cst_map.extend();
								*to_leaf_label = Some((label, 1));
								//continue here!...
							},
							_ => {
								return Err(self.ambiguous(add_to_node_id,nset)); // TODO
							}
						}

self.nodes.copy_branch(next_node_id, add_to_node_id, Some((label, 1)));
	
	fn copy_branch(&mut self, copy_from_node_id: NodeId, copy_to_node_id: NodeId, set_leaf_label: Option<(Label, u8)>) {
		match (self.get_mut(copy_to_node_id), self.get(copy_from_node_id)) {
			(GrammarNode::Branch { cst_map: ref mut to_cst_map, leaf_label: ref mut to_leaf_label,.. }, GrammarNode::Branch { cst_map, leaf_label: None,.. }) => {
				//cst_map.extend();
				*to_leaf_label = set_leaf_label;
				//continue here!...
			},
			_ => {
				return; // Err(self.ambiguous(add_to_node_id,nset)); // TODO
			}
		}
	}


						fn create_branch_with(&mut self, cst_map: &HashMap<Symbol, NodeId>, var_map: &HashMap<TypeCode, NodeId>, leaf_label: Option<(Label, u8)>) -> NodeId {
		let mut new_cst_map = new_map();
		let mut new_var_map = new_map();
		new_cst_map.extend(cst_map.iter());
		new_var_map.extend(var_map.iter());
	    self.0.push(GrammarNode::Branch{cst_map: new_cst_map, var_map: new_var_map, leaf_label});
	    self.0.len() - 1
	}
	
	/// Duplicate
	fn dup_branch(&mut self, node_id: NodeId, label: Label, var_count: u8) -> Result<NodeId, NodeId> {
		match self.nodes.get(node_id) {
			GrammarNode::Leaf { .. } => Err(node_id), // Error: cannot duplicate a leaf node
			GrammarNode::Branch { cst_map: _, var_map: _, leaf_label: Some(_) } => Err(node_id), // Error: cannot duplicate if there is already a leaf label
			GrammarNode::Branch { ref cst_map, ref var_map, leaf_label: None } => Ok(self.nodes.create_branch_with(cst_map, var_map, Some((label, var_count)))),
		}
	}


					match (var_map.get(&to_typecode), var_map.get(&from_typecode)) {
						(Some(next_node_id), None) => {
							println!("{} Only class", next_node_id);
							match self.dup_branch(*next_node_id, label, 1) {
								Ok(new_node_id) => {
									var_map.insert(from_typecode, new_node_id);
								},
								Err(conflict_node) => { return Err(self.ambiguous(conflict_node, nset)); },
							}
						},
						(Some(next_node), Some(next_node_2)) => {
							println!("{} class {} setvar", next_node, next_node_2);
						},
						(None, _) => {}, // Nothing to do it from_typecode not in the var_map
					}
				},
				_ => {},
*/



	/// Bake the lookahead into the grammar automaton.
	/// This handles casses like the ambiguity between ` ( x e. A /\ ph ) ` and ` ( x e. A |-> B ) `
	/// which share a common prefix, and can only be distinguished after the 5th token is read.
	/// This is dealt with by introducing branch nodes where the optional leaf is set, 
	/// which lead to partial reduce. 
	/// In the example case, at the 5th token "/\", this method modifies the grammar tree 
	/// by adding the optional "wcel" reduce to the corresponding tree node.
	fn bake_in_lookahead(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) {
		let mut tokens = sref.math_iter().peekable();

		// Atom for this axiom's label.
		let _this_label = names.lookup_label(sref.label()).unwrap().atom;
		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let _this_typecode = nset.get_atom(tokens.next().unwrap().slice);

		// In case of a non-syntax axiom, skip it.
		if _this_typecode == self.provable_type { return; }

		// Search a sub-string of this syntax axiom which is parseable itself.
		
		
	}

	fn do_shift(&self, sref: &StatementRef, ix: &mut TokenIndex, nset: &Arc<Nameset>, names: &mut NameReader) {
		if self.debug {
			let token = sref.math_at(*ix);
			let symbol = names.lookup_symbol(token.slice).unwrap();
			println!("   SHIFT {:?}", as_str(nset.atom_name(symbol.atom)));
		}
		*ix += 1;
	}

	fn do_reduce(&self, formula_builder: &mut FormulaBuilder, stmt: Label, var_count: u8, nset: &Arc<Nameset>) {
		if self.debug {
			println!("   REDUCE {:?}", as_str(nset.atom_name(stmt)));
		}
		formula_builder.reduce(stmt, var_count);
		if self.debug {
			print!(" {:?} {}", as_str(nset.atom_name(stmt)), var_count);
		}
	}

	fn parse_formula<'a>(&self, start_node: NodeId, sref: &StatementRef, ix: &mut TokenIndex, formula_builder: &mut FormulaBuilder, _expected_typecodes: impl IntoIterator<Item = &'a TypeCode>, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<TypeCode, Diagnostic> {
		let mut node = start_node;
		loop {
			match self.nodes.get(node) {
				GrammarNode::Leaf{label, var_count, typecode} => {
					// We found a leaf: REDUCE
					self.do_reduce(formula_builder, *label, *var_count, nset);
					return Ok(*typecode);
				},
				GrammarNode::Branch{cst_map, var_map} => {
					if *ix == sref.math_len() { return Err(Grammar::too_short(cst_map, nset)); }
					let token = sref.math_at(*ix);
					let symbol = names.lookup_symbol(token.slice).unwrap();
					if self.debug { print!("   {:?}", as_str(nset.atom_name(symbol.atom))); }

					match cst_map.get(&symbol.atom) {
						Some(NextNode { next_node_id, leaf_label }) => {
							// Found an atom matching one of our next nodes: First optionally REDUCE and continue
							if let Some((label, var_count)) = leaf_label {
								self.do_reduce(formula_builder, *label, *var_count, nset);
							}

							// Found an atom matching one of our next nodes: SHIFT, to the next node
							self.do_shift(sref, ix, nset, names);
							node = *next_node_id;
							if self.debug { println!("   Next Node: {:?}", node); }
						},
						None => {
							// No matching constant, search among variables
							if var_map.is_empty() || node == self.root {
								return Err(Diagnostic::UnparseableStatement(token.index()));
							}

							if self.debug { println!(" ++ Not in CST map, recursive call expecting {:?}", var_map.keys()); }
							let typecode = self.parse_formula(self.root, sref, ix, formula_builder, var_map.keys(), nset, names)?;
							if self.debug { println!(" ++ Finished parsing formula, found typecode {:?}, back to {}", as_str(nset.atom_name(typecode)), node); }
							match var_map.get(&typecode) {
								Some(NextNode { next_node_id, leaf_label }) => {
									// Found a sub-formula: First optionally REDUCE and continue
									if let Some((label, var_count)) = leaf_label {
										self.do_reduce(formula_builder, *label, *var_count, nset);
									}

									node = *next_node_id;
									if self.debug { println!("   Next Node: {:?}", node); }
								},
								None => {
									// No match found, try as a prefix of a larger formula
									let (_, var_map_2) = self.get_branch(self.root);
									match var_map_2.get(&typecode) {
										Some(NextNode { next_node_id: next_node_id_2, leaf_label: leaf_label_2 }) => {
											// Found a sub-formula: First optionally REDUCE and continue
											if let Some((label, var_count)) = leaf_label_2 {
												self.do_reduce(formula_builder, *label, *var_count, nset);
											}
		
											// Found and reduced a sub-formula, to the next node
											if self.debug { println!(" ++ Considering prefix, switching to {}", next_node_id_2); }
											let typecode = self.parse_formula(*next_node_id_2, sref, ix, formula_builder, var_map.keys(), nset, names)?;
											if self.debug { println!(" ++ Finished parsing formula, found typecode {:?}, back to {}", as_str(nset.atom_name(typecode)), node); }
											match var_map.get(&typecode) {
												Some(NextNode { next_node_id, leaf_label }) => {
													// Found a sub-formula: First optionally REDUCE and continue
													if let Some((label, var_count)) = leaf_label {
														self.do_reduce(formula_builder, *label, *var_count, nset);
													}
				
													node = *next_node_id;
													if self.debug { println!("   Next Node: {:?}", node); }
												},
												None => {
													// Still no match found, error.
													println!("EXIT 2 at node {} with token {:?}", node, as_str(nset.atom_name(symbol.atom)));
													std::process::exit(1);
													//return Err(Diagnostic::UnparseableStatement(token.index()));
													//return Ok(None);
												},
											}
										},
										_ => {
											// Still no match found, error.
											println!("EXIT 3 at node {} with token {:?}", node, as_str(nset.atom_name(symbol.atom)));
											std::process::exit(1);
											//return Err(Diagnostic::UnparseableStatement(token.index()));
											//return Ok(None);
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
			//println!("Statement #{}, {} has length 0", sref.index(), nset.lookup_label(sref.label()));
			return Err(Diagnostic::ParsedStatementNoTypeCode);
		}
		// Atom for this statement's label. TODO: Safe to unwrap here?  
		//let this_label = as_str(nset.atom_name(nset.lookup_label(sref.label()).unwrap().atom));
		//println!("Parsing {:?}", this_label);

		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let typecode = nset.get_atom(sref.math_at(0).slice); 
		let mut expected_typecode = typecode; 

		// Skip syntactic axioms 
		if sref.statement_type() == StatementType::Axiom && expected_typecode != self.provable_type { return Ok(None) }

		// If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
		if expected_typecode == self.provable_type { expected_typecode = self.logic_type; }

		// At the time of writing, there are only 3 statements which are not provable but "syntactic theorems": weq, wel and bj-0
		let mut formula_builder = FormulaBuilder::default();

		if self.debug {
			println!("\nStatement {:?}\n---------", as_str(nset.statement_name(sref)));
		}

		self.parse_formula(self.root, sref, &mut 1, &mut formula_builder, vec![&expected_typecode], nset, names)?;
		Ok(Some(formula_builder.build(typecode)))
	}

	/// Lists the contents of the grammar
	pub fn dump(&self, nset: &Arc<Nameset>) {
		println!("Grammar tree has {:?} nodes.", self.nodes.len());
		for i in 0 .. self.nodes.len() {
			match &self.nodes.0[i] {
				GrammarNode::Leaf{label, var_count, typecode} => { println!("{:?}: {} {} ({} vars)", i, as_str(nset.atom_name(*typecode)), as_str(nset.atom_name(*label)), var_count); },
				GrammarNode::Branch{cst_map, var_map} => {
					print!("{:?}: CST={{", i);
					for (symbol, node) in cst_map {
						print!("{}: {:?}", as_str(nset.atom_name(*symbol)), node.next_node_id);
						if let Some((label, var_count)) = node.leaf_label {
							print!("({:?} {})", as_str(nset.atom_name(label)), var_count);
						}
						print!(", ");
					}
					print!("}} VAR={{");
					for (typecode, node) in var_map {
						print!("{}: {:?}", as_str(nset.atom_name(*typecode)), node.next_node_id);
						if let Some((label, var_count)) = node.leaf_label {
							print!("({:?} {})", as_str(nset.atom_name(label)), var_count);
						}
						print!(", ");
					}
					println!("}}");
				},
			}
		}
	}
}

/// Builds the grammar from the syntax axioms in the database, and parse all other statements
/// Then, search for shorter sequences like ` x e. A ` in the longer ones like ` ( x e. A |-> B ) `
/// 
/// If there is a match, generate new rules for each rule starting with ` ( ph ... `,
/// like ` ( A e. B /\ ps ) ` , ` ( A e. B \/ ps ) `, etc. 
/// When parsed, this shall generate a double reduce, to both the full expression and x e. A.
/// The same applies for ` ( <. x , y >. e. A |-> B ) ` and so on.
/// 
pub fn build_grammar<'a>(grammar: &mut Grammar, sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>) {
	// TODO make this configurable, or read in $j statements
	let provable_type = nset.lookup_symbol("|-".as_bytes()).unwrap().atom;
	let wff_type = nset.lookup_symbol("wff".as_bytes()).unwrap().atom;
	let setvar_type = nset.lookup_symbol("setvar".as_bytes()).unwrap().atom;
	let class_type = nset.lookup_symbol("class".as_bytes()).unwrap().atom;
	grammar.provable_type = provable_type; 
	grammar.logic_type = wff_type;

	// TODO construct this from the Float $f statements
	grammar.typecodes.push(wff_type);
	grammar.typecodes.push(setvar_type);
	grammar.typecodes.push(class_type);

	grammar.root = grammar.nodes.create_branch();

	let mut names = NameReader::new(nset);

	let mut type_conversions = Vec::new();

	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");
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

	// Handle replacement schemes
	for (from_typecode, to_typecode, label) in type_conversions {
		if let Err(diag) = grammar.perform_type_conversion(from_typecode, to_typecode, label) {
			//grammar.diagnostics.insert(sref.address(), diag);
			println!("ERROR {:?}", diag); // TODO format error message!
		}
	}

	grammar.dump(nset);

	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");
    for segment in segments.iter() {
	    for sref in *segment {
			match sref.statement_type() {
		        StatementType::Axiom => grammar.bake_in_lookahead(&sref, nset, &mut names),
				_ => {},
			}
	    }
	}
}

/** The result of parsing all statements with the language grammar */
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
				if grammar.debug { println!(" FAILED to parse {}!", as_str(nset.statement_name(&sref)))}
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

/// Parses all the statements in the database
/// 
pub fn parse_statements<'a>(stmt_parse: &mut StmtParse, sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>, grammar: &Arc<Grammar>) {
	let mut names = NameReader::new(nset);
	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");

	// TODO make this parallel using segments.exec.exec()!
	stmt_parse.segments.clear();
    for segment in segments.iter() {
		let id = segment.id;
		let arc = Arc::new(parse_statements_single(sset, nset, &mut names, grammar, id));
		stmt_parse.segments.insert(id, arc);
	}
}