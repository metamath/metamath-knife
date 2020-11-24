//! The proof object model for RPN proofs used in Metamath.

use diag::Diagnostic;
use nameck::Nameset;
use parser::as_str;
use parser::StatementAddress;
use parser::StatementRef;
use parser::TokenPtr;
use scopeck::ScopeResult;
use segment_set::SegmentSet;
use std::cmp::Ord;
use std::cmp::Ordering;
use std::cmp::PartialOrd;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Write;
use std::hash::Hash;
use std::hash::Hasher;
use std::hash::SipHasher;
use std::ops::Range;
use std::u16;
use verify::ProofBuilder;
use verify::verify_one;

/// A tree structure for storing proofs and grammar derivations.
#[derive(Clone,Debug,Eq)]
pub struct ProofTree {
    /// The axiom/theorem being applied at the root.
    pub address: StatementAddress,
    /// The hypotheses ($e and $f) in database order, indexes into the parent `ProofTreeArray`.
    pub children: Vec<usize>,
    /// The precomputed hash for this tree.
    hash: u64,
}

impl PartialEq for ProofTree {
    /// This is a shallow equality check
    fn eq(&self, other: &ProofTree) -> bool {
        self.address == other.address && self.children == other.children
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
    pub fn new(parent: &ProofTreeArray, address: StatementAddress, children: Vec<usize>) -> Self {
        let mut hasher = SipHasher::new();
        address.hash(&mut hasher);
        for &ix in &children {
            parent.trees[ix].hash(&mut hasher);
        }
        ProofTree {
            address: address,
            children: children,
            hash: hasher.finish(),
        }
    }
}

/// An array of proof trees, used to collect steps of a proof
/// in proof order
#[derive(Default,Debug,Clone)]
pub struct ProofTreeArray {
    map: HashMap<u64, usize>,
    /// The list of proof trees
    pub trees: Vec<ProofTree>,
    /// The uncompressed strings for each proof tree
    pub exprs: Vec<Vec<u8>>,
    /// The QED step
    pub qed: usize,
    /// The distance from each step to the QED step
    indent: Vec<u16>,
}


/// A strongly typed representation of the RPN proof style used by
/// Metamath proofs (except compressed style)
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum RPNStep {
    /// A "normal" step is one that defines a new formula not seen
    /// before in this proof.
    Normal {
        /// A number by which to refer to this step in later steps,
        /// or zero if it is not going to be reused.
        fwdref: usize,
        /// The theorem being applied at this step
        addr: StatementAddress,
        /// The address of the parent of this step, and the index of
        /// this hypotheses among its siblings. This is set to `None`
        /// if we are not in explicit mode, and it is also `None` for
        /// the root step (which has no parent).
        hyp: Option<(StatementAddress, usize)>,
    },
    /// A backreference step, which copies the subtree and formula
    /// from a previously derived subtree.
    Backref {
        /// A reference to the previously numbered step
        backref: usize,
        /// The address of the parent of this step, and the index of
        /// this hypotheses among its siblings. This is set to `None`
        /// if we are not in explicit mode, and it is also `None` for
        /// the root step (which has no parent).
        hyp: Option<(StatementAddress, usize)>,
    },
}

impl ProofTreeArray {
    /// Get the index of a proof tree in the array
    pub fn index(&self, tree: &ProofTree) -> Option<usize> {
        self.map.get(&tree.hash).cloned()
    }

    /// Create a proof tree array from the proof  a single $p statement,
    /// returning the result of the given proof builder, or an error if the
    /// proof is faulty
    pub fn new(sset: &SegmentSet,
               nset: &Nameset,
               scopes: &ScopeResult,
               stmt: StatementRef)
               -> Result<ProofTreeArray, Diagnostic> {
        let mut arr = ProofTreeArray::default();
        arr.qed = verify_one(sset, nset, scopes, &mut arr, stmt)?;
        arr.indent = arr.calc_indent();
        Ok(arr)
    }

    /// Get the minimum distance from each step to the QED step
    pub fn indent(&self) -> &[u16] {
        &self.indent
    }

    /// Finds the shortest path from each node in the proof tree to the `qed` step,
    /// using Dijkstra's algorithm.  Based on the example in
    /// https://doc.rust-lang.org/std/collections/binary_heap/.
    fn calc_indent(&self) -> Vec<u16> {

        #[derive(Copy, Clone, Eq, PartialEq)]
        struct IndentNode {
            index: usize,
            cost: u16,
        }

        // The priority queue depends on `Ord`.
        // Explicitly implement the trait so the queue becomes a min-heap
        // instead of a max-heap.
        impl Ord for IndentNode {
            fn cmp(&self, other: &IndentNode) -> Ordering {
                // Notice that the we flip the ordering here
                other.cost.cmp(&self.cost)
            }
        }

        // `PartialOrd` needs to be implemented as well.
        impl PartialOrd for IndentNode {
            fn partial_cmp(&self, other: &IndentNode) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        // dist[node] = current shortest distance from `start` to `node`
        let mut dist: Vec<u16> = vec![u16::MAX;self.trees.len()];

        let mut heap = BinaryHeap::new();

        // We're at `qed`, with a zero cost
        dist[self.qed] = 0;
        heap.push(IndentNode {
            index: self.qed,
            cost: 0,
        });

        // Examine the frontier with lower cost nodes first (min-heap)
        while let Some(IndentNode { index, cost }) = heap.pop() {
            // Important as we may have already found a better way
            if cost > dist[index] {
                continue;
            }

            // For each node we can reach, see if we can find a way with
            // a lower cost going through this node
            for &hix in &self.trees[index].children {
                let next = IndentNode {
                    index: hix,
                    cost: cost + 1,
                };

                // If so, add it to the frontier and continue
                if next.cost < dist[next.index] {
                    heap.push(next);
                    // Relaxation, we have now found a better way
                    dist[next.index] = next.cost;
                }
            }
        }

        dist
    }

    /// Get the number of parents of each step in the proof
    pub fn count_parents(&self) -> Vec<usize> {
        let mut out = vec![0; self.trees.len()];
        for tree in &self.trees {
            for &hix in &tree.children {
                out[hix] += 1;
            }
        }
        out
    }

    /// Write the proof as an RPN sequence with backrefs
    pub fn to_rpn(&self, parents: &[usize], explicit: bool) -> Vec<RPNStep> {
        #[derive(Debug)]
        struct Env<'a> {
            arr: &'a ProofTreeArray,
            parents: &'a [usize],
            explicit: bool,
            out: Vec<RPNStep>,
            backrefs: Vec<usize>,
            count: usize,
        }

        fn output_step(env: &mut Env, step: usize, hyp: Option<(StatementAddress, usize)>) {
            let step = if env.backrefs[step] == 0 {
                let ref tree = env.arr.trees[step];
                for (i, &hix) in tree.children.iter().enumerate() {
                    let nhyp = if env.explicit {
                        Some((tree.address, i))
                    } else {
                        None
                    };
                    output_step(env, hix, nhyp);
                }
                RPNStep::Normal {
                    fwdref: if env.parents[step] > 1 && !tree.children.is_empty() {
                        env.count += 1;
                        env.backrefs[step] = env.count;
                        env.count
                    } else {
                        0
                    },
                    addr: tree.address,
                    hyp: hyp,
                }
            } else {
                RPNStep::Backref {
                    backref: env.backrefs[step],
                    hyp: hyp,
                }
            };
            env.out.push(step);
        }
        let mut env = Env {
            arr: self,
            parents: parents,
            explicit: explicit,
            out: vec![],
            backrefs: vec![0; self.trees.len()],
            count: 0,
        };
        output_step(&mut env, self.qed, None);
        env.out
    }

    /// Produce an iterator over the steps in the proof in
    /// normal/uncompressed mode. (Because this can potentially
    /// be *very* long, we do not store the list and just stream it.)
    pub fn normal_iter(&self, explicit: bool) -> NormalIter {
        NormalIter {
            arr: self,
            explicit: explicit,
            stack: vec![(self.qed, 0)],
        }
    }
}

/// An iterator which loops over the steps of the proof in tree order
/// (with repetition for duplicate subtrees).
#[derive(Debug)]
pub struct NormalIter<'a> {
    arr: &'a ProofTreeArray,
    explicit: bool,
    stack: Vec<(usize, usize)>,
}

impl<'a> Iterator for NormalIter<'a> {
    type Item = RPNStep;

    fn next(&mut self) -> Option<RPNStep> {
        loop {
            let (ix, ohix) = match self.stack.last() {
                None => return None,
                Some(&(ix, child)) => (ix, self.arr.trees[ix].children.get(child)),
            };
            if let Some(&hix) = ohix {
                self.stack.push((hix, 0));
                continue;
            }
            self.stack.pop();
            let hyp = if let Some(&mut (lix, ref mut i)) = self.stack.last_mut() {
                let hyp = if self.explicit {
                    Some((self.arr.trees[lix].address, *i))
                } else {
                    None
                };
                *i += 1;
                hyp
            } else {
                None
            };
            let out = RPNStep::Normal {
                fwdref: 0,
                addr: self.arr.trees[ix].address,
                hyp: hyp,
            };
            return Some(out);
        }
    }
}

impl ProofBuilder for ProofTreeArray {
    type Item = usize;
    type Accum = Vec<usize>;

    fn push(&mut self, hyps: &mut Vec<usize>, hyp: usize) {
        hyps.push(hyp);
    }

    fn build(&mut self,
             addr: StatementAddress,
             trees: Vec<usize>,
             pool: &[u8],
             expr: Range<usize>)
             -> usize {
        let tree = ProofTree::new(self, addr, trees);
        self.index(&tree).unwrap_or_else(|| {
            let ix = self.trees.len();
            self.map.insert(tree.hash, ix);
            self.trees.push(tree);
            let mut uexpr = vec![b' '];
            for &chr in &pool[expr] {
                if chr & 0x80 == 0 {
                    uexpr.push(chr);
                } else {
                    uexpr.push(chr & 0x7F);
                    uexpr.push(b' ');
                }
            }
            uexpr.pop();
            self.exprs.push(uexpr);
            ix
        })
    }
}

/// List of possible proof output types.
#[derive(Debug,PartialEq,Eq)]
pub enum ProofStyle {
    /// `/compressed` proof output (default). Label list followed by step letters.
    Compressed,
    /// `/normal` proof output. Uncompressed step names only.
    Normal,
    /// `/packed` proof output. Same as `/normal` with backreferences.
    Packed,
    /// `/explicit` proof output. `/normal` with hypothesis names.
    Explicit,
    /// `/packed/explicit` proof output. `/normal` with hypothesis names and backreferences.
    PackedExplicit,
}

/// A struct for storing display parameters for printing proofs.
pub struct ProofTreePrinter<'a> {
    /// The segment set, for looking up statements
    pub sset: &'a SegmentSet,
    /// The nameset, for looking up statements
    pub nset: &'a Nameset,
    /// The scoping pass, for looking up statements
    pub scope: &'a ScopeResult,
    /// The current statement label (only used in explicit style)
    pub thm_label: TokenPtr<'a>,
    /// The type of output (normal, compressed, packed, ...)
    pub style: ProofStyle,
    /// The source data
    pub arr: &'a ProofTreeArray,
    /// The initial cursor character number on the current line
    pub initial_chr: u16,
    /// The amount of leading whitespace to print
    pub indent: u16,
    /// The number of characters to fit before going to a new line
    pub line_width: u16,
}

impl<'a> fmt::Display for ProofTreePrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut indent = "\n".to_string();
        for _ in 0..self.indent {
            indent.push(' ');
        }
        f.write_str(&indent[(self.initial_chr + 2) as usize..])?;
        let mut chr = self.indent - 1;
        let parents = self.arr.count_parents();

        let explicit = match self.style {
            ProofStyle::Explicit |
            ProofStyle::PackedExplicit => true,
            _ => false,
        };

        let mut stmt_lookup: HashMap<StatementAddress, (&str, Vec<&str>)> = HashMap::new();
        for tree in &self.arr.trees {
            stmt_lookup.entry(tree.address)
                .or_insert_with(|| {
                    let label = self.sset.statement(tree.address).label();
                    (as_str(label),
                     if explicit {
                        match self.scope.get(label) {
                            Some(frame) => {
                                frame.hypotheses
                                    .iter()
                                    .map(|hyp| as_str(self.sset.statement(hyp.address()).label()))
                                    .collect()
                            }
                            None => vec![],
                        }
                    } else {
                        vec![]
                    })
                });
        }

        let mut print_step = |item: RPNStep| -> fmt::Result {
            let estr = |hyp| if explicit {
                format!("{}=",
                        match hyp {
                            Some((stmt, i)) => stmt_lookup[&stmt].1[i],
                            None => as_str(self.thm_label),
                        })
            } else {
                String::new()
            };
            let fmt = match item {
                RPNStep::Normal { fwdref, addr, hyp } => {
                    if fwdref == 0 {
                        format!("{}{}", estr(hyp), stmt_lookup[&addr].0)
                    } else {
                        format!("{}:{}{}", fwdref, estr(hyp), stmt_lookup[&addr].0)
                    }
                }
                RPNStep::Backref { backref, hyp } => format!("{}{}", estr(hyp), backref),
            };

            if chr + (fmt.len() as u16) < self.line_width {
                chr += (fmt.len() as u16) + 1;
                f.write_char(' ')?;
            } else {
                chr = self.indent + (fmt.len() as u16);
                f.write_str(&indent)?;
            }
            f.write_str(&fmt)
        };

        match self.style {
            ProofStyle::Compressed => unimplemented!(),
            ProofStyle::Normal | ProofStyle::Explicit => {
                for item in self.arr.normal_iter(explicit) {
                    print_step(item)?;
                }
            }
            ProofStyle::Packed |
            ProofStyle::PackedExplicit => {
                for item in self.arr.to_rpn(&parents, explicit) {
                    print_step(item)?;
                }
            }
        }
        Ok(())
    }
}
