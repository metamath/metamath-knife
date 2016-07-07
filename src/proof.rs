//! The proof object model for RPN proofs used in Metamath.

use nameck::Atom;
use std::sync::Arc;
use std::hash::Hash;
use std::hash::Hasher;
use std::hash::SipHasher;
use std::collections::HashSet;

/// A tree structure for storing proofs and grammar derivations.
#[derive(Clone,Eq)]
pub struct ProofTree {
    /// The axiom/theorem being applied at the root.
    pub atom: Atom,
    /// The hypotheses ($e and $f) in database order.
    pub children: Vec<Arc<ProofTree>>,
    /// The precomputed hash for this tree.
    hash: u64,
}

impl PartialEq for ProofTree {
    fn eq(&self, other: &ProofTree) -> bool {
        self.atom == other.atom && self.children == other.children
    }
}

impl Hash for ProofTree {
    fn hash<H>(&self, state: &mut H)
        where H: Hasher
    {
        self.hash.hash(state)
    }
}

impl ProofTree {
    /// Create a new proof tree using the given atom and children.
    pub fn new(atom: Atom, children: Vec<Arc<ProofTree>>) -> Self {
        let mut hasher = SipHasher::new();
        atom.hash(&mut hasher);
        children.hash(&mut hasher);
        ProofTree {
            atom: atom,
            children: children,
            hash: hasher.finish(),
        }
    }
}


/// Look up the given value in the cache table, and return the cached version
/// of the value
pub fn intern<T: Clone + Hash + Eq>(table: &mut HashSet<T>, val: T) -> &T {
    let v2 = val.clone();
    table.insert(val);
    table.get(&v2).unwrap()
}