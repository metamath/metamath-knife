//! `Formula` stores the result of a parsing as the tree of its "synctactic proof" 
//!

use crate::parser::as_str;
use crate::parser::SymbolType;
use crate::parser::TokenIter;
use crate::segment_set::SegmentSet;
use crate::nameck::Atom;
use crate::nameck::Nameset;
use crate::tree::Tree;
use crate::tree::NodeId;
use crate::tree::SiblingIter;
use std::sync::Arc;

/// An atom representing a typecode (for "set.mm", that's one of 'wff', 'class', 'setvar' or '|-')
pub type TypeCode = Atom;

/// An atom representing a math symbol
pub type Symbol = Atom;

/// A parsed formula, in a tree format which is convenient to perform unifications
#[derive(Default)]
pub struct Formula {
	typecode: TypeCode,
	tree: Tree<Atom>,
	root: NodeId,
}

impl Formula {
	/// Convert the formula back to a flat list of symbols
	/// This is slow and shall not normally be called except for showing a result to the user.
	pub fn iter<'a>(&'a self, sset: &'a Arc<SegmentSet>, nset: &'a Arc<Nameset>) -> Flatten<'a> {
		let mut f = Flatten {
			formula: self,
			stack: vec![],
			sset,
			nset,
		};
		f.step_into(self.root);
		f
	}

	/// Displays the formula as a string
	pub fn display(&self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) -> String {
		let mut str = String::new();
		str.push_str(as_str(nset.atom_name(self.typecode)));
		for symbol in self.iter(sset, nset) {
			str.push_str(" ");
			str.push_str(as_str(nset.atom_name(symbol)));
		}
		return str;
	}

	/// Debug only, dumps the internal structure of the fomula.
	pub fn dump(&self, nset: &Arc<Nameset>) {
		println!("  Root: {}", self.root);
		self.tree.dump(|atom| as_str(nset.atom_name(*atom)));
	}
}

/// An iterator going through each symbol in a formula
pub struct Flatten<'a> {
	formula: &'a Formula,
	stack: Vec<(TokenIter<'a>, Option<SiblingIter<'a, Atom>>)>,
	sset: &'a Arc<SegmentSet>, 
	nset: &'a Arc<Nameset>,
}

impl<'a> Flatten<'a> {
	fn step_into(&mut self, node_id: NodeId) {
		let label = self.formula.tree[node_id];
		let sref = self.sset.statement(self.nset.lookup_label(self.nset.atom_name(label)).unwrap().address);
		let mut math_iter = sref.math_iter();
		math_iter.next(); // Always skip the typecode token.
		if self.formula.tree.has_children(node_id) { 
			self.stack.push((math_iter, Some(self.formula.tree.children_iter(node_id))));
		} 
		else {
			self.stack.push((math_iter, None)); 
		};
		
	}
}

impl<'a> Iterator for Flatten<'a> {
	type Item = Symbol;
	
    fn next(&mut self) -> Option<Self::Item> {
		if self.stack.is_empty() { return None; }
		let stack_end = self.stack.len()-1;
		let (ref mut math_iter, ref mut sibling_iter) = self.stack[stack_end];
		if let Some(token) = math_iter.next() {
			// Continue with next token of this syntax
			let symbol = self.nset.lookup_symbol(token.slice).unwrap();
			match (sibling_iter,symbol.stype) {
				(_, SymbolType::Constant) | (None, SymbolType::Variable) => Some(symbol.atom),
				(Some(ref mut iter), SymbolType::Variable) => {
					// Variable : push into the next child
					if let Some(next_child_id) = iter.next() {
						self.step_into(next_child_id);
						self.next()
					} else {
						panic!("Empty formula!");
					}
				},
			}
		} else {
			// End of this formula, pop to the parent one
			self.stack.pop();
			self.next()
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
		assert!(self.stack.len()>=var_count.into());
		let new_length = self.stack.len().saturating_sub(var_count.into());
		let new_node_id = {
			let children = self.stack.drain(new_length..);
			self.formula.tree.add_node(label, children.as_slice())
		};
		self.stack.push(new_node_id);
	}

	pub(crate) fn build(mut self, typecode: TypeCode) -> Formula {
		// Only one entry shall remain in the stack at the time of building, the formula root.
		assert!(self.stack.len() == 1, "Final formula building state does not have one root"); 
		self.formula.root = self.stack[0];
		self.formula.typecode = typecode;
		return self.formula;
	}
}