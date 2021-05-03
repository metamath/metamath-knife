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
use crate::parser::TokenIndex;
use crate::parser::as_str;
use crate::parser::copy_token;
use crate::segment_set::SegmentSet;
use std::sync::Arc;
use crate::util::HashMap;
use crate::util::new_map;

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

/** The Grammar built from the database's syntactic axioms */
pub struct Grammar {
	provable_type: TypeCode,
	logic_type: TypeCode,
	typecodes: Vec<TypeCode>,
	nodes: Arena,
	root: NodeId, // The root of the Grammar tree
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
			root: 0,
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

	fn wrong_typecode(expected_typecode: TypeCode, found_typecode: TypeCode, nset: &Arc<Nameset>) -> Diagnostic {
		let expected_token = copy_token(nset.atom_name(expected_typecode));
		let found_token = copy_token(nset.atom_name(found_typecode));
		Diagnostic::ParsedStatementWrongTypeCode(expected_token, found_token)
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
	fn add_axiom(&mut self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
		let mut tokens = sref.math_iter().peekable();

		// Atom for this axiom's label. TODO: Safe to unwrap here?  
		let this_label = nset.lookup_label(sref.label()).unwrap().atom;
		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let this_typecode = nset.get_atom(tokens.next().unwrap().slice); 

		// In case of a non-syntax axiom, skip it.
		if this_typecode == self.provable_type { return Ok(()); }

		// We will add this syntax axiom to the corresponding grammar tree
		let mut node = self.root;
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

	fn parse_formula(&self, sref: &StatementRef, ix: &mut TokenIndex, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<TypeCode, Diagnostic> {
		let mut node = self.root;
		loop {
			match self.nodes.get(node) {
				GrammarNode::Leaf(_label) => {
					// We found a leaf: REDUCE
					//let stmt = sset.statement(label)  //let stmt_address = nset.lookup_label(nset.atom_name(label)).unwrap().address;
					//print!("   REDUCE!");
					return Ok(self.logic_type); // TODO use actual statement type!
				},
				GrammarNode::Branch{cst_map, var_map} => {
					if *ix == sref.math_len() { return Err(Grammar::too_short(cst_map, nset)); }
					let token = sref.math_at(*ix);
					let symbol = names.lookup_symbol(token.slice).unwrap();
					//print!("   {:?}", as_str(nset.atom_name(symbol.atom)));
					match symbol.stype {
						SymbolType::Variable => {
							// Token is a variable, we can immediately reduce it to is float typecode
							let typecode = names.lookup_float(token.slice).unwrap().typecode_atom;
							//println!(" -> Variable, typecode {:?}", as_str(nset.atom_name(typecode)));
							// SHIFT REDUCE, we don't use the map as this is an extra $f reduct
							if node == 0 {
								// If we were at the root node, just reduce the float and return.
								//println!("   SHIFT REDUCE single float!");
								*ix += 1;
								return Ok(typecode);
							}
							else {
								match var_map.get(&typecode) {
									Some(next_node) => {
										// Found and reduced a variable, to the next node
										*ix += 1;
										node = *next_node;
										//println!("   SHIFT REDUCE FLOAT, Next: {:?}", node);
									},
									None => {
										// No match found, try recursively.
										let typecode = self.parse_formula(sref, ix, nset, names)?;
										match var_map.get(&typecode) {
											Some(next_node) => {
												// Found and reduced a compound variable, to the next node
												node = *next_node;
												//println!("   Next: {:?}", node);
											},
											None => {
												// No match found.
												return Err(Grammar::wrong_typecode(*var_map.keys().next().unwrap(), typecode, nset));
											}
										}
									}
								}
							}
						},
						SymbolType::Constant => { 
							match cst_map.get(&symbol.atom) {
								Some(next_node) => {
									// Found a constant matching one of our next nodes: SHIFT, to the next node
									*ix += 1;
									node = *next_node;
									//println!("   SHIFT CST! Next: {:?}", node);
								},
								None => {
									// No matching constant, search among variables
									//println!(" ++ Not in CST map, recursive call");
									let typecode = self.parse_formula(sref, ix, nset, names)?;
									//println!(" ++ Finished parsing formula, found typecode {:?}", as_str(nset.atom_name(typecode)));
									match var_map.get(&typecode) {
										Some(next_node) => {
											// Found and reduced a sub-formula, to the next node
											node = *next_node;
											//println!("   Next: {:?}", node);
										},
										None => {
											// No match found, error.
											return Err(Diagnostic::UnparseableStatement(token.index()));
										}
									}
								}
							}
						},
					}
				},
			}
		}
	}

	fn parse_statement(&self, sref: &StatementRef, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<(), Diagnostic> {
		if sref.math_len() == 0 {
			//println!("Statement #{}, {} has length 0", sref.index(), nset.lookup_label(sref.label()));
			return Err(Diagnostic::ParsedStatementNoTypeCode);
		}
		// Atom for this statement's label. TODO: Safe to unwrap here?  
		//let this_label = as_str(nset.atom_name(nset.lookup_label(sref.label()).unwrap().atom));
		//println!("Parsing {:?}", this_label);

		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let mut expected_typecode = nset.get_atom(sref.math_at(0).slice); 

		// Skip syntactic axioms 
		if sref.statement_type() == StatementType::Axiom && expected_typecode != self.provable_type { return Ok(()) }

		// If this is a provable statement, prove that this is a wff. Otherwise just use the provided typecode
		if expected_typecode == self.provable_type { expected_typecode = self.logic_type; }

		let found_typecode = self.parse_formula(sref, &mut 1, nset, names)?;
		if found_typecode != expected_typecode {
			Err(Grammar::wrong_typecode(expected_typecode, found_typecode, nset))
		} else {
			Ok(())
		}
	}

	/// Lists the contents of the grammar
	pub fn dump(&self, nset: &Arc<Nameset>) {
		println!("Grammar tree has {:?} nodes.", self.nodes.len());
		for i in 0 .. self.nodes.len() {
			match &self.nodes.0[i] {
				GrammarNode::Leaf(label) => { println!("{:?}: {}", i, as_str(nset.atom_name(*label))); },
				GrammarNode::Branch{cst_map, var_map} => {
					print!("{:?}: CST={{", i);
					for (symbol, node) in cst_map {
						print!("{}: {}, ", as_str(nset.atom_name(*symbol)), node);
					}
					print!("}} VAR={{");
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

	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");
    for segment in segments.iter() {
	    for sref in *segment {
	        if let Err(diag) = match sref.statement_type() {
	            StatementType::Axiom => grammar.add_axiom(&sref, nset, &mut names),
	            _ => Ok(())
	        } {
				grammar.diagnostics.insert(sref.address(), diag);
			}
	    }
	}
}

/** The result of parsing all statements with the language grammar */
pub struct StmtParse {
	diagnostics: HashMap<StatementAddress, Diagnostic>,
}

impl Default for StmtParse {
	fn default() -> Self {
		StmtParse {
			diagnostics: new_map(),
		}
	}
}

impl StmtParse {
    /// Returns a list of errors that were generated when parsing the database's statements.
    pub fn diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for (sa, diag) in &self.diagnostics {
            out.push((*sa, diag.clone()));
        }
        out
    }
}

/// Parses all the statements in the database
/// 
pub fn parse_statements<'a>(stmt_parse: &mut StmtParse, sset: &'a Arc<SegmentSet>, nset: &Arc<Nameset>, grammar: &Arc<Grammar>) {
	let mut names = NameReader::new(nset);
	let segments = sset.segments();
	assert!(segments.len() > 0, "Parse returned no segment!");

    for segment in segments.iter() {
	    for sref in *segment {
			println!("Statement {:?}\n---------", as_str(nset.atom_name(nset.lookup_label(sref.label()).map_or(Atom::default(), |l| l.atom))));
	        if let Err(diag) = match sref.statement_type() {
	            StatementType::Axiom | StatementType::Provable => grammar.parse_statement(&sref, nset, &mut names),
	            _ => Ok(())
	        } {
				stmt_parse.diagnostics.insert(sref.address(), diag);
				return; // inserted here to stop at first error!
			}
	    }
	}
}