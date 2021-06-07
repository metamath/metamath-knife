//! Grammar processes a database, extracts a Grammar, which it also
//! validates, and parses statements in the system.
//!

use crate::diag::Diagnostic;
use crate::nameck::Atom;
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
use crate::formula::Formula;
use crate::formula::FormulaBuilder;
use std::sync::Arc;
use crate::util::HashMap;
use crate::util::new_map;


type NodeId = usize;

struct GrammarTree(Vec<GrammarNode>);

impl GrammarTree {
	fn create_branch(&mut self) -> NodeId {
	    self.0.push(GrammarNode::Branch{cst_map: new_map(), var_map: new_map(), leaf_label: None});
	    self.0.len() - 1
	}

	fn create_leaf(&mut self, label: Atom, var_count: u8, typecode: TypeCode) -> NodeId {
	    self.0.push(GrammarNode::Leaf{label, var_count, typecode});
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
	nodes: GrammarTree,
	root: NodeId, // The root of the Grammar tree
	diagnostics: HashMap<StatementAddress, Diagnostic>,
	debug: bool,
}

enum GrammarNode {
	Leaf {
		label: Atom,
		var_count: u8,
		typecode: TypeCode,
		},
	Branch {
		cst_map: HashMap<Symbol, NodeId>, 	// Table of choices leading to the next node when a constant is encountered
		var_map: HashMap<TypeCode, NodeId>, // Table of choices leading to the next node when a variable is successfully parsed
		leaf_label: Option<Atom>,           // This deals with ambiguity in the grammar, see `bake_in_lookahead`
	}, 
}

impl Default for Grammar {
	fn default() -> Self {
		Grammar {
			provable_type: Atom::default(),
			logic_type: Atom::default(),
			typecodes: Vec::new(),
			nodes: GrammarTree(Vec::new()),
			root: 0,
			diagnostics: new_map(),
			debug: false,
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
				GrammarNode::Leaf{label, ..} => {
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

	/// Adds the symbol to the branch, and returns the next node
	fn add_branch(&mut self, to_node: NodeId, symbol: Symbol, stype: SymbolType, leaf: Option<NodeId>) -> Result<NodeId, NodeId> {
		match self.nodes.get_mut(to_node) {
			GrammarNode::Leaf{..} => Err(to_node), // Error: cannot add to a leaf node, `to_node` is the conflicting node
			GrammarNode::Branch{cst_map, var_map, ..} => {
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
								if let GrammarNode::Branch{cst_map, var_map, ..} = self.nodes.get_mut(to_node) {
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

		// Atom for this axiom's label.
		let this_label = names.lookup_label(sref.label()).unwrap().atom;
		// Type token. It is safe to unwrap here since parser has checked for EmptyMathString error.
		let this_typecode = nset.get_atom(tokens.next().unwrap().slice); 

		// In case of a non-syntax axiom, skip it.
		if this_typecode == self.provable_type { return Ok(()); }

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
				None => Some(self.nodes.create_leaf(this_label, var_count, this_typecode)),
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
			GrammarNode::Branch{cst_map, ..} => match cst_map.insert(symbol.atom, leaf_node) {
				None => Ok(()),
				Some(conflict_node) => Err(self.ambiguous(conflict_node, nset)),
			}
			_ => panic!("Root node shall be a branch node!"),
		}
	}

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

	fn do_reduce(&self, formula_builder: &mut FormulaBuilder, stmt: Atom, var_count: u8, nset: &Arc<Nameset>) {
		if self.debug {
			println!("   REDUCE {:?}", as_str(nset.atom_name(stmt)));
		}
		formula_builder.reduce(stmt, var_count);
		if self.debug {
			print!(" {:?} {}", as_str(nset.atom_name(stmt)), var_count);
		}
	}

	fn parse_formula<'a>(&self, sref: &StatementRef, ix: &mut TokenIndex, formula_builder: &mut FormulaBuilder, _expected_typecodes: impl IntoIterator<Item = &'a TypeCode>, nset: &Arc<Nameset>, names: &mut NameReader) -> Result<TypeCode, Diagnostic> {
		let mut node = self.root;
		loop {
			match self.nodes.get(node) {
				GrammarNode::Leaf{label, var_count, typecode} => {
					// We found a leaf: REDUCE
					self.do_reduce(formula_builder, *label, *var_count, nset);
					return Ok(*typecode);
				},
				GrammarNode::Branch{cst_map, var_map, ..} => {
					if *ix == sref.math_len() { return Err(Grammar::too_short(cst_map, nset)); }
					let token = sref.math_at(*ix);
					let symbol = names.lookup_symbol(token.slice).unwrap();
					if self.debug { print!("   {:?}", as_str(nset.atom_name(symbol.atom))); }

					match cst_map.get(&symbol.atom) {
						Some(next_node) => {
							// Found an atom matching one of our next nodes: SHIFT, to the next node
							self.do_shift(sref, ix, nset, names);
							node = *next_node;
							if self.debug { println!("   Next Node: {:?}", node); }
						},
						None => {
							// No matching constant, search among variables
							if self.debug { println!(" ++ Not in CST map, recursive call"); }
							let typecode = self.parse_formula(sref, ix, formula_builder, var_map.keys(), nset, names)?;
							if self.debug { println!(" ++ Finished parsing formula, found typecode {:?}", as_str(nset.atom_name(typecode))); }
							match var_map.get(&typecode) {
								Some(next_node) => {
									// Found and reduced a sub-formula, to the next node
									node = *next_node;
									if self.debug { println!("   Next Node: {:?}", node); }
								},
								None => {
									// No match found, error.
									//println!("EXIT 2");
									//std::process::exit(1);
									return Err(Diagnostic::UnparseableStatement(token.index()));
									//return Ok(None);
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

		self.parse_formula(sref, &mut 1, &mut formula_builder, vec![&expected_typecode], nset, names)?;
		Ok(Some(formula_builder.build(typecode)))
	}

	/// Lists the contents of the grammar
	pub fn dump(&self, nset: &Arc<Nameset>) {
		println!("Grammar tree has {:?} nodes.", self.nodes.len());
		for i in 0 .. self.nodes.len() {
			match &self.nodes.0[i] {
				GrammarNode::Leaf{label, var_count, typecode} => { println!("{:?}: {} {} ({} vars)", i, as_str(nset.atom_name(*typecode)), as_str(nset.atom_name(*label)), var_count); },
				GrammarNode::Branch{cst_map, var_map, leaf_label} => {
					print!("{:?}: CST={{", i);
					for (symbol, node) in cst_map {
						print!("{}: {}, ", as_str(nset.atom_name(*symbol)), node);
					}
					print!("}} VAR={{");
					for (typecode, node) in var_map {
						print!("{}: {}, ", as_str(nset.atom_name(*typecode)), node);
					}
					if let Some(label) = leaf_label {
						print!("Leaf: {}, ", as_str(nset.atom_name(*label)));
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
	            StatementType::Floating => grammar.add_floating(&sref, nset, &mut names),
	            _ => Ok(())
	        } {
				grammar.diagnostics.insert(sref.address(), diag);
			}
	    }
	}

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