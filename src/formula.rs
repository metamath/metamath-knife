//! `Formula` stores the result of a parsing as the tree of its "synctactic proof" 
//!

use crate::parser::as_str;
use crate::parser::SymbolType;
use crate::parser::TokenIter;
use crate::segment_set::SegmentSet;
use crate::nameck::Atom;
use crate::nameck::Nameset;
use std::sync::Arc;

type NodeId = usize;

struct FormulaNode {
	atom: Atom,
	first_child: NodeId,
	next_sibling: NodeId,
}

/// A parsed formula, in a format in which it is convenient to perform unifications
#[derive(Default)]
pub struct Formula {
	root: NodeId,
	nodes: Vec<FormulaNode>,
}

impl Formula {
	/// Convert the formula back to a flat list of symbols
	/// This is slow and shall not normally be called except for showing a result to the user.
	pub fn iter<'a>(&'a self, sset: &'a Arc<SegmentSet>, nset: &'a Arc<Nameset>) -> Flattener<'a> {
		Flattener {
			formula: self,
			stack: vec![(self.root, None, None)],
			sset,
			nset,
		}
	}

	/// Displays the formula as a string
	pub fn display(&self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) -> String {
		let mut str = String::new();
		for symbol in self.iter(sset, nset) {
			str.push_str(" ");
			str.push_str(as_str(nset.atom_name(symbol)));
		}
		return str;
	}

	/// Debug only, dumps the internal structure of the fomula.
	pub fn dump(&self, nset: &Arc<Nameset>) {
		println!("  Root: {}", self.root);
		for node in &self.nodes {
			println!("  - {:?} fc={}, ns={}", as_str(nset.atom_name(node.atom)), node.first_child, node.next_sibling);
		}
	}
}

/// An iterator going through each symbol in a formula
pub struct Flattener<'a> {
	formula: &'a Formula,
	stack: Vec<(NodeId, Option<TokenIter<'a>>, Option<NodeId>)>,
	sset: &'a Arc<SegmentSet>, 
	nset: &'a Arc<Nameset>,
}

impl<'a> Iterator for Flattener<'a> {
	type Item = Atom;
	
    fn next(&mut self) -> Option<Self::Item> {
		if self.stack.len() == 0 { return None; }
		let stack_end = self.stack.len()-1;
		match &mut self.stack[stack_end] {
			(0, None, None) => None,
			(index, None, None) => {
				// We have an index, but no iterator yet: create one
				let node = &self.formula.nodes[*index-1];
				let sref = self.sset.statement(self.nset.lookup_label(self.nset.atom_name(node.atom)).unwrap().address);
				let mut math_iter = sref.math_iter();
				math_iter.next(); // Always skip the typecode token.
				self.stack[stack_end] = (*index, Some(math_iter), None);
				self.next()
			},
			(index, Some(ref mut math_iter), ref mut current_child) => {
				// We are already iterating within one syntaxical axiom
				if let Some(token) = math_iter.next() {
					let symbol = self.nset.lookup_symbol(token.slice).unwrap();
					let node = &self.formula.nodes[*index-1];
					match (node.first_child, symbol.stype) {
						(_, SymbolType::Constant) | (0, SymbolType::Variable) => Some(symbol.atom),
						(_, SymbolType::Variable) => {
							// Variable : push into the next child
							let current_child_index = match current_child {
								None => node.first_child,
								Some(child_index) => self.formula.nodes[*child_index-1].next_sibling,
							};
							*current_child = Some(current_child_index);
							self.stack.push((current_child_index, None, None));
							self.next()
						},
					}
				} else {
					// End of this formula, pop to the parent one
					self.stack.pop();
					self.next()
				}
			},
			_ => {
				panic!("Wrong formula iterator state!");
			}
		}
    }

	// TODO provide an implementation for size_hint?
}

#[derive(Default)]
pub(crate) struct FormulaBuilder {
	stack: Vec<NodeId>,
	formula: Formula,
}

/// A utility to build a formula. 
impl FormulaBuilder {
	/// Every REDUCE pops `var_count` subformula items on the stack, 
	/// and pushes one single new item, with the popped subformulas as children
	pub(crate) fn reduce(&mut self, label: Atom, var_count: u8) {
		let mut new_node = FormulaNode {
			atom: label,
			first_child: 0,
			next_sibling: 0,
		};
		let mut pointer = &mut new_node.first_child;
		assert!(self.stack.len()>=var_count.into());
		let new_length = self.stack.len().saturating_sub(var_count.into());
		for child_index in self.stack.drain(new_length..) {
			*pointer = child_index;
			pointer = &mut self.formula.nodes[child_index-1].next_sibling;
		}
		self.formula.nodes.push(new_node);
		self.stack.push(self.formula.nodes.len());
	}

	pub(crate) fn build(mut self) -> Formula {
		// Only one entry shall remain in the stack at the time of building, the formula root.
		assert!(self.stack.len() == 1); 
		self.formula.root = self.stack[0];
		return self.formula;
	}
}