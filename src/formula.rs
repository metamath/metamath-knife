//! `Formula` stores the result of a parsing as the tree of its "synctactic proof" 
//!

use crate::parser::SymbolType;
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
	pub fn flatten(&self, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>) -> Vec<Atom> {
		let mut flat_array = Vec::new(); // TODO guess default array capacity?
		self.flatten_at(1, sset, nset, &mut flat_array);
		return flat_array;
	}

	fn flatten_at(&self, index: usize, sset: &Arc<SegmentSet>, nset: &Arc<Nameset>, flat_array: &mut Vec<Atom>) {
		// TODO It may be better to use an iterator
		let node = &self.nodes[index-1];
		let sref = sset.statement(nset.lookup_label(nset.atom_name(node.atom)).unwrap().address);
		let mut math_iter = sref.math_iter();
		let mut current_child: Option<usize> = None;
		while let Some(token) = math_iter.next() {
			let symbol = nset.lookup_symbol(token.slice).unwrap();
			match symbol.stype {
				SymbolType::Constant => { flat_array.push(symbol.atom) }
				SymbolType::Variable => { 
					let current_child_index = match current_child {
						None => node.first_child-1,
						Some(index) => self.nodes[index-1].next_sibling,
					};
					self.flatten_at(current_child_index, sset, nset, flat_array);
					current_child = Some(current_child_index);
				},
			};
		}
	}
}

#[derive(Default)]
pub(crate) struct FormulaBuilder {
	stack: Vec<NodeId>,
	formula: Formula,
}

/// A utility to build a formula tree. This is done by repetively calling 'accumulate' for each child,
/// and finally 'reduce'.
impl FormulaBuilder {
	pub(crate) fn accumulate(&mut self) {
		self.stack.push(self.formula.root);
	}

	pub(crate) fn reduce(&mut self, label: Atom) {
		//self.label = label;
	}

	pub(crate) fn build(self) -> Formula {
		return self.formula;
	}
}