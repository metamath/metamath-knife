//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.
//!

use crate::diag::Diagnostic;
use crate::nameck::Atom;
use crate::nameck::NameReader;
use crate::nameck::Nameset;
use crate::parser::StatementAddress;
use crate::parser::StatementType;
use crate::parser::StatementRef;
use crate::parser::SymbolType;
//use crate::parser::TokenIndex;
use crate::parser::TokenIter;
use crate::parser::as_str;
use crate::parser::copy_token;
use crate::scopeck::ScopeResult;
use crate::segment_set::SegmentSet;
use std::sync::Arc;
use core::iter::Peekable;
use crate::util::HashMap;
use crate::util::new_map;
//use crate::bit_set::Bitset;

type TypeCode = Atom;
type Symbol = Atom;

type NodeId = usize;

struct Arena(Vec<GrammarNode>);

impl Arena {
	fn create_branch(&mut self) -> NodeId {
	    self.0.push(GrammarNode::Branch{cst_map: new_map(), var_map: new_map()});
	    self.0.len() - 1
	}

	fn create_leaf(&mut self, label: Atom) -> NodeId {
	    self.0.push(GrammarNode::Leaf(label));
	    self.0.len() - 1
	}
	
	fn get(&self, node: NodeId) -> &GrammarNode {
		&self.0[node]
	}

	fn get_mut(&mut self, node: NodeId) -> &mut GrammarNode {
		&mut self.0[node]
	}
	
	fn len(&self) -> usize {
		self.0.len()
	}
}

type TypeCodeSet=Atom;

/** The Grammar built from the database's axioms */
pub struct Grammar {
	provable_type: TypeCode,
	logic_type: TypeCode,
	typecodes: Vec<TypeCode>,
	nodes: Arena,

	variable_types: Vec<(TypeCodeSet, NodeId)>, // A grammar tree for each of the variable types
	diagnostics: HashMap<StatementAddress, Diagnostic>,
}

enum GrammarNode {
	Leaf(Atom), // The atoms for Label of the Statement obtained - TODO, double leafs
	Branch{
		cst_map: HashMap<Symbol, NodeId>, 	// Table of choices leading to the next node
		var_map: HashMap<TypeCode, NodeId>, 
	}, 
}

impl Default for Grammar {
	fn default() -> Self {
		Grammar {
			provable_type: Atom::default(),
			logic_type: Atom::default(),
			typecodes: Vec::new(),
			nodes: Arena(Vec::new()),
			variable_types: Vec::new(),
			diagnostics: new_map(),
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
					node = *cst_map.values().next().unwrap();
				}
				GrammarNode::Leaf(label) => {
					let sa = nset.lookup_label(nset.atom_name(*label)).unwrap().address;
					return Diagnostic::GrammarAmbiguous(sa);
				}
			}
		}
	}
	
	fn too_short(map: &HashMap<Symbol,NodeId>, nset: &Arc<Nameset>) -> Diagnostic {
		let expected_symbol = *map.keys().next().unwrap();
		let expected_token = copy_token(nset.atom_name(expected_symbol));
		Diagnostic::ParsedStatementTooShort(expected_token)
	}

	/// Returns the grammar tree for a given typecode
	fn grammar_tree(&mut self, typecode_set: TypeCodeSet) -> NodeId {
		match self.variable_types.iter().find(|&t| t.0 == typecode_set) {
			Some((_, node)) => *node,
			None => {
				let new_branch = self.nodes.create_branch();
				self.variable_types.push((typecode_set, new_branch));
				new_branch
			}
		}
	}

	/// Adds the symbol to the branch, and returns the next node
	fn add_branch(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, leaf: Option<NodeId>) -> Result<NodeId, NodeId> {
		match self.nodes.get_mut(to_node) {
			GrammarNode::Leaf(_) => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
			GrammarNode::Branch{cst_map, var_map} => {
				let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
				match leaf {
					Some(leaf_node) => {
						match map.insert(symbol, leaf_node) {
							Some(prev_node) => Err(prev_node), // Error : We want to add a leaf note, but there is already a branch.
							None => Ok(leaf_node),
						}
					},
					None => {
						//Ok(*map.entry(symbol).or_insert_with(|| self.nodes.create_branch())),
						match map.get(&symbol) {
							Some(prev_node) => Ok(*prev_node),
							None => {
								let new_node = self.nodes.create_branch();
								if let GrammarNode::Branch{cst_map, var_map} = self.nodes.get_mut(to_node) {
									let map = match stype { SymbolType::Constant => { cst_map }, SymbolType::Variable => { var_map } };
									map.insert(symbol, new_node);
									Ok(new_node)
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
	fn add_axiom(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader, parse_statements: bool) -> Result<(), Diagnostic> {
		let mut tokens = sref.math_iter().peekable();

		// Atom for this axiom's label. TODO: Safe to unwrap here?  
		let this_label = nset.lookup_label(sref.label()).unwrap().atom;
		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let this_typecode = nset.get_atom(tokens.next().unwrap().slice); 

		// In case of a non-syntax axiom, parse it.
		if this_typecode == self.provable_type {
			if parse_statements { return self.parse_statement(sref, nset, names); }
			else { return Ok(()); }
		}

		// We will add this syntax axiom to the corresponding grammar tree
		let mut node = self.grammar_tree(this_typecode);
		let leaf_node = self.nodes.create_leaf(this_label);
		while let Some(token) = tokens.next() {
			let symbol = names.lookup_symbol(token.slice).unwrap();
			let atom = match symbol.stype {
				SymbolType::Constant => symbol.atom,
				// We need a second lookup to find out the typecode of a floating variable...
				// Ideally this information would be included in the LookupSymbol
				SymbolType::Variable => names.lookup_float(token.slice).unwrap().typecode_atom,
			};
			let next_leaf = match &tokens.peek() {
				Some(_) => None,
				None => Some(leaf_node),
			};
			match self.add_branch(node, atom, symbol.stype, next_leaf) {
				Ok(next_node) => { node = next_node; },
				Err(conflict_node) => { return Err(self.ambiguous(conflict_node, nset)); },
			}
//
//			match node {
//				&mut GrammarNode::Leaf(_) => {
//					// A prefix of this syntax is already recorded: the grammar is ambiguous
//					return Some(ambiguous(node, nset));
//				}
//				&mut GrammarNode::Branch(mut map) => {
//					// It is safe to unwrap since parser has checked for NotActiveSymbol error 
//					let symbol = names.lookup_symbol(token.slice).unwrap();
//					//let atom = names.get_atom(token.slice);
//					let atom = match symbol.stype {
//						SymbolType::Constant => symbol.atom,
//						// We need a second lookup to find out the typecode of a floating variable...
//						SymbolType::Variable => names.lookup_float(token.slice).unwrap().typecode_atom,
//					};
//					match &tokens.peek() {
//						Some(_) => { 
//							node = map.entry(atom).or_insert(Grammar::create_branch());
//						},
//						None => {
//							match map.get(&atom) {
//								Some(other_node) => {
//									// A longer syntax is already recorded: the grammar is ambiguous, search for a leaf
//									return Some(ambiguous(other_node, nset));
//								},
//								None => {
//									map.insert(atom, GrammarNode::Leaf(this_label));
//								}
//							}
//						},
//					}
//				}
//			}
		};
		// TODO
		Ok(())
	}

	fn parse_formula(&mut self, mut tokens: Peekable<TokenIter>, expected_typecode: TypeCode, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
		let mut node = self.grammar_tree(expected_typecode);
		loop {
			match self.nodes.get(node) {
				GrammarNode::Leaf(_) => {
					// We found a leaf: REDUCE
					return Ok(());
				}
				GrammarNode::Branch{cst_map, var_map} => {
					match tokens.next() {
						None => { return Err(Grammar::too_short(cst_map, nset)); }
						Some(token) => {
							// It is safe to unwrap since parser has checked for NotActiveSymbol error 
							let symbol = names.lookup_symbol(token.slice).unwrap();
							match symbol.stype {
								SymbolType::Variable => {
									// Token is a variable, we can immediately reduce it to is float typecode
									let typecode = names.lookup_float(token.slice).unwrap().typecode_atom;
									if typecode == expected_typecode {
										// REDUCE, we don't use the map as this is an extra $f reduct
										return Ok(());
									} else {
										// Search for a non-constant
										match var_map.iter().next() {
											Some((_typecode, next_node)) => {
												//self.parse_formula(tokens, *typecode, nset, names)?;
												// Found and reduced a sub-formula, now SHIFT, to the next node
												node = *next_node;
											},
											None => {
												// No match found, error.
												return Err(Diagnostic::UnparseableStatement(token.index()));
											}
										}
									}
								},
								SymbolType::Constant => { 
									match cst_map.get(&symbol.atom) {
										Some(next_node) => {
											// Found a constant matching one of our next nodes: SHIFT, to the next node
											node = *next_node;
										},
										None => {
											// No matching constant, search among variables
											match var_map.iter().next() {
												Some((_typecode, next_node)) => {
													//self.parse_formula(tokens, *typecode, nset, names)?;
													// Found and reduced a sub-formula, now SHIFT, to the next node
													node = *next_node;
												},
												None => {
													// No match found, error.
													return Err(Diagnostic::UnparseableStatement(token.index()));
												}
											}
										}
									}
								},
							};
						}
					}
				}
			}
		}
	}

	fn parse_statement(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
		let mut tokens = sref.math_iter().peekable();

		// Atom for this statement's label. TODO: Safe to unwrap here?  
		let _this_label = nset.lookup_label(sref.label()).unwrap().atom;
		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let mut typecode = nset.get_atom(tokens.next().unwrap().slice); 
		// If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
		if typecode == self.provable_type { typecode = self.logic_type; }

		self.parse_formula(tokens, typecode, nset, names)
	}

	fn dump(&self, nset: &Arc<Nameset>) {
		println!("Grammar tree has {:?} nodes.", self.nodes.len());
		for i in 0 .. self.nodes.len() {
			match &self.nodes.0[i] {
				GrammarNode::Leaf(label) => { println!("{:?}: {}", i, as_str(nset.atom_name(*label))); },
				GrammarNode::Branch{cst_map, var_map} => {
					print!("{:?}: CST={{", i);
					for (symbol, node) in cst_map {
						print!("{}: {}, ", as_str(nset.atom_name(*symbol)), node);
					}
					println!("}} VAR={{");
					for (typecode, node) in var_map {
						print!("{}: {}, ", as_str(nset.atom_name(*typecode)), node);
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
/// Parsing algorithm:
/// 
pub fn build_grammar<'a>(grammar: &mut Grammar, sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>, _scope: &ScopeResult, parse_statements: bool) {
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
	let mut names = NameReader::new(nset);

	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");
    for segment in segments.iter() {
	    for sref in *segment {
	        if let Err(diag) = match sref.statement_type() {
	            StatementType::Axiom => grammar.add_axiom(&sref, nset, &mut names, parse_statements),
	            StatementType::Essential | StatementType::Provable => {
					if parse_statements { grammar.parse_statement(&sref, nset, &mut names) }
					else { Ok(()) }
				},
	            _ => Ok(())
	        } {
				grammar.diagnostics.insert(sref.address(), diag);
				break; // inserted here to stop at first error!
			}
	    }
	}
	grammar.dump(nset);
}