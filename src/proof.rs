//! The proof object model for RPN proofs used in Metamath.

use crate::diag::Diagnostic;
use crate::nameck::Nameset;
use crate::parser::as_str;
use crate::parser::StatementAddress;
use crate::parser::StatementRef;
use crate::parser::StatementType::*;
use crate::parser::TokenPtr;
use crate::scopeck::Hyp;
use crate::scopeck::ScopeResult;
use crate::segment_set::SegmentSet;
use crate::util::new_map;
use crate::util::HashMap;
use crate::verify::verify_one;
use crate::verify::ProofBuilder;
use std::cmp::max;
use std::cmp::Ord;
use std::cmp::Ordering;
use std::cmp::PartialOrd;
use std::collections::hash_map::DefaultHasher;
use std::collections::hash_map::Entry;
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::Write;
use std::hash::Hash;
use std::hash::Hasher;
use std::ops::Range;
use std::u16;

/// A tree structure for storing proofs and grammar derivations.
#[derive(Clone, Debug, Eq)]
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
    where
        H: Hasher,
    {
        self.hash.hash(state)
    }
}

impl ProofTree {
    /// Create a new proof tree using the given atom and children.
    pub fn new(parent: &ProofTreeArray, address: StatementAddress, children: Vec<usize>) -> Self {
        let mut hasher = DefaultHasher::new();
        address.hash(&mut hasher);
        for &ix in &children {
            parent.trees[ix].hash(&mut hasher);
        }
        ProofTree {
            address,
            children,
            hash: hasher.finish(),
        }
    }
}

/// An array of proof trees, used to collect steps of a proof
/// in proof order
#[derive(Default, Debug, Clone)]
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
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

    /// Create a proof tree array from the proof a single $p statement,
    /// returning the result of the given proof builder, or an error if the
    /// proof is faulty
    pub fn new(
        sset: &SegmentSet,
        nset: &Nameset,
        scopes: &ScopeResult,
        stmt: StatementRef,
    ) -> Result<ProofTreeArray, Diagnostic> {
        let mut arr = ProofTreeArray::default();
        arr.qed = verify_one(sset, nset, scopes, &mut arr, stmt)?;
        arr.calc_indent();
        Ok(arr)
    }

    /// Get the minimum distance from each step to the QED step
    pub fn indent(&self) -> &[u16] {
        &self.indent
    }

    /// Finds the shortest path from each node in the proof tree to the `qed` step,
    /// using Dijkstra's algorithm.  Based on the example in
    /// <https://doc.rust-lang.org/std/collections/binary_heap/>.
    pub fn calc_indent(&mut self) {
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
        let mut dist: Vec<u16> = vec![u16::MAX; self.trees.len()];

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

        self.indent = dist;
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
                let tree = &env.arr.trees[step];
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
                    hyp,
                }
            } else {
                RPNStep::Backref {
                    backref: env.backrefs[step],
                    hyp,
                }
            };
            env.out.push(step);
        }
        let mut env = Env {
            arr: self,
            parents,
            explicit,
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
            explicit,
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
                hyp,
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

    fn build(
        &mut self,
        addr: StatementAddress,
        trees: Vec<usize>,
        pool: &[u8],
        expr: Range<usize>,
    ) -> usize {
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
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

impl ProofStyle {
    /// Returns `true` if this is in explicit style (showing proof hypotheses labels
    /// on each step)
    pub fn explicit(self) -> bool {
        matches!(self, ProofStyle::Explicit | ProofStyle::PackedExplicit)
    }

    /// Returns `true` if this is in packed style, meaning duplicate subtrees are
    /// referred to by backreferences instead of inlined. (Compressed proofs are
    /// considered packed by this definition.)
    pub fn packed(self) -> bool {
        matches!(
            self,
            ProofStyle::Compressed | ProofStyle::Packed | ProofStyle::PackedExplicit
        )
    }
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

/// The local variables of `ProofTreePrinter::fmt()`, extracted into a struct
/// so that the inner functions can be broken out.
struct ProofTreePrinterImpl<'a, 'b: 'a> {
    p: &'a ProofTreePrinter<'a>,
    f: &'a mut fmt::Formatter<'b>,
    indent: String,
    chr: u16,
    stmt_lookup: HashMap<StatementAddress, (&'a str, Vec<&'a str>)>,
    backref_alloc: Vec<String>,
    backref_max: usize,
}

impl<'a, 'b> ProofTreePrinterImpl<'a, 'b> {
    fn write_word(&mut self, word: &str) -> fmt::Result {
        let len = word.len() as u16;
        if self.chr + len < self.p.line_width {
            self.chr += len + 1;
            self.f.write_char(' ')?;
        } else {
            self.chr = self.p.indent + len;
            self.f.write_str(&self.indent)?;
        }
        self.f.write_str(word)
    }

    fn estr(&self, hyp: Option<(StatementAddress, usize)>) -> String {
        if self.p.style.explicit() {
            format!(
                "{}=",
                match hyp {
                    Some((stmt, i)) => self.stmt_lookup[&stmt].1[i],
                    None => as_str(self.p.thm_label),
                }
            )
        } else {
            String::new()
        }
    }

    fn print_step(&mut self, item: RPNStep) -> fmt::Result {
        let word = match item {
            RPNStep::Normal { fwdref, addr, hyp } => {
                if fwdref == 0 {
                    format!("{}{}", self.estr(hyp), self.stmt_lookup[&addr].0)
                } else {
                    format!(
                        "{}:{}{}",
                        if fwdref <= self.backref_alloc.len() {
                            &self.backref_alloc[fwdref - 1]
                        } else {
                            let mut s;
                            while {
                                self.backref_max += 1;
                                s = self.backref_max.to_string();
                                self.p.nset.lookup_label(s.as_bytes()).is_some()
                            } {}
                            self.backref_alloc.push(s);
                            self.backref_alloc.last().unwrap()
                        },
                        self.estr(hyp),
                        self.stmt_lookup[&addr].0
                    )
                }
            }
            RPNStep::Backref { backref, hyp } => {
                format!("{}{}", self.estr(hyp), self.backref_alloc[backref - 1])
            }
        };
        self.write_word(&word)
    }

    fn init_stmt_lookup(&mut self) {
        for tree in &self.p.arr.trees {
            let p = &self.p;
            if let Entry::Vacant(entry) = self.stmt_lookup.entry(tree.address) {
                let label = p.sset.statement(tree.address).label();
                let hyps = if p.style.explicit() {
                    match p.scope.get(label) {
                        Some(frame) => frame
                            .hypotheses
                            .iter()
                            .map(|hyp| as_str(p.sset.statement(hyp.address()).label()))
                            .collect(),
                        None => vec![],
                    }
                } else {
                    vec![]
                };
                entry.insert((as_str(label), hyps));
            }
        }
    }

    fn fmt_compressed(&mut self) -> fmt::Result {
        let parents = self.p.arr.count_parents();
        let rpn = self.p.arr.to_rpn(&parents, false);
        let mut proof_ordered: Vec<(StatementRef, usize)> = vec![];
        let frame = self.p.scope.get(self.p.thm_label).unwrap();
        for item in &rpn {
            if let RPNStep::Normal { addr, .. } = *item {
                let stmt = self.p.sset.statement(addr);
                let vec = match stmt.statement_type() {
                    Floating => {
                        let atom = self.p.nset.var_atom(stmt).unwrap();
                        if frame.var_list[..frame.mandatory_count].contains(&atom) {
                            continue;
                        }
                        &mut proof_ordered
                    }
                    Essential => continue,
                    Axiom | Provable => &mut proof_ordered,
                    _ => unreachable!(),
                };
                match vec.iter().position(|&(s, _)| s.address() == addr) {
                    Some(n) => vec[n].1 += 1,
                    None => vec.push((stmt, 1)),
                }
            }
        }
        let values: Vec<u16> = proof_ordered
            .iter()
            .map(|&(s, _)| s.label().len() as u16 + 1)
            .collect();

        let mut sorted_by_refs = (0..proof_ordered.len()).collect::<Vec<usize>>();
        sorted_by_refs.sort_by(|&a, &b| proof_ordered[b].1.cmp(&proof_ordered[a].1));
        let mut i = frame.mandatory_count;
        let mut cutoff = 20;
        while cutoff <= i {
            i -= cutoff;
            cutoff *= 5;
        }
        let mut length_block = vec![];
        let mut line_pos = 2u16;
        let mut paren_stmt = vec![];
        let width = self.p.line_width - self.p.indent + 1;

        let mut knapsack = VecDeque::new(); // scratch space used in knapsack_fit
        let mut process_block = |paren_stmt: &mut Vec<StatementRef<'a>>,
                                 length_block: &mut Vec<usize>| {
            length_block.sort_unstable();
            while !length_block.is_empty() {
                knapsack_fit(
                    length_block,
                    &values,
                    (width - line_pos) as usize,
                    &mut knapsack,
                );
                for &p in &knapsack {
                    line_pos += values[p];
                    paren_stmt.push(proof_ordered[p].0);
                    if let Ok(n) = length_block.binary_search(&p) {
                        length_block.remove(n);
                    }
                }
                if !knapsack.is_empty() || line_pos >= width - 1 {
                    line_pos = 0;
                }
            }
        };

        for pos in sorted_by_refs {
            if i == cutoff {
                i = 1;
                cutoff *= 5;
                process_block(&mut paren_stmt, &mut length_block);
            } else {
                i += 1;
            }
            length_block.push(pos);
        }
        process_block(&mut paren_stmt, &mut length_block);

        self.write_word("(")?;
        for s in &paren_stmt {
            self.write_word(as_str(s.label()))?;
        }
        self.write_word(")")?;

        let mut ess_stmt: Vec<StatementRef> = frame
            .hypotheses
            .iter()
            .filter_map(|h| {
                if let Hyp::Essential(addr, _) = h {
                    Some(self.p.sset.statement(*addr))
                } else {
                    None
                }
            })
            .collect();
        ess_stmt.append(&mut paren_stmt);
        paren_stmt = ess_stmt;

        let mut letters: Vec<u8> = vec![];
        for item in &rpn {
            let (is_fwdref, mut letter) = match *item {
                RPNStep::Normal { fwdref, addr, .. } => {
                    let stmt = self.p.sset.statement(addr);
                    let pos = if stmt.statement_type() == Floating {
                        frame.hypotheses[..frame.mandatory_count]
                            .iter()
                            .position(|h| {
                                if let Hyp::Floating(sa, ..) = h {
                                    *sa == addr
                                } else {
                                    false
                                }
                            })
                    } else {
                        None
                    };
                    (
                        fwdref != 0,
                        pos.unwrap_or_else(|| {
                            frame.mandatory_count
                                + paren_stmt.iter().position(|s| s.address() == addr).unwrap()
                        }),
                    )
                }
                RPNStep::Backref { backref, .. } => (
                    false,
                    frame.mandatory_count + paren_stmt.len() + backref - 1,
                ),
            };
            let code_start = letters.len();
            letters.push(b'A' + (letter % 20) as u8);
            letter /= 20;
            while letter != 0 {
                letter -= 1;
                letters.insert(code_start, b'U' + (letter % 5) as u8);
                letter /= 5;
            }
            if is_fwdref {
                letters.push(b'Z');
            }
        }

        let mut letters: &[u8] = &letters;
        loop {
            let ll = (self.p.line_width - self.chr)
                .checked_sub(1)
                .unwrap_or(self.p.line_width - self.p.indent) as usize;
            if ll < letters.len() {
                let (left, right) = letters.split_at(ll);
                letters = right;
                self.write_word(as_str(left))?;
            } else {
                return self.write_word(as_str(letters));
            }
        }
    }

    fn fmt(&mut self) -> fmt::Result {
        self.f
            .write_str(&self.indent[(self.p.initial_chr + 2) as usize..])?;

        match self.p.style {
            ProofStyle::Normal | ProofStyle::Explicit => {
                self.init_stmt_lookup();
                for item in self.p.arr.normal_iter(self.p.style.explicit()) {
                    self.print_step(item)?;
                }
            }
            ProofStyle::Packed | ProofStyle::PackedExplicit => {
                self.init_stmt_lookup();
                let parents = self.p.arr.count_parents();
                for item in self.p.arr.to_rpn(&parents, self.p.style.explicit()) {
                    self.print_step(item)?;
                }
            }
            ProofStyle::Compressed => self.fmt_compressed()?,
        }
        self.write_word("$.")
    }
}

/// Given an array of items, such that `values[i]` is the cost of the `i`th item,
/// and the items are labeled by `items` (so only the values `i = items[j]` are
/// relevant), find the best fit of items whose total cost is no more than `size`,
/// and return the result in the `included` array.
///
/// Implements the algorithm given in https://en.wikipedia.org/wiki/Knapsack_problem#0.2F1_knapsack_problem.
fn knapsack_fit(items: &[usize], values: &[u16], mut size: usize, included: &mut VecDeque<usize>) {
    let mut worth: Vec<Vec<u16>> = vec![vec![0; size + 1]; items.len() + 1];
    for (i, &item) in items.iter().enumerate() {
        let value = values[item];
        for s in 0..size + 1 {
            worth[i + 1][s] = if s >= value as usize {
                max(worth[i][s], value + worth[i][s - value as usize])
            } else {
                worth[i][s]
            }
        }
    }
    included.clear();
    for (i, &item) in items.iter().enumerate().rev() {
        if worth[i + 1][size] != worth[i][size] {
            included.push_front(item);
            size -= values[item] as usize;
            if size == 0 {
                break;
            }
        }
    }
}

impl<'a> fmt::Display for ProofTreePrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut indent = "\n".to_string();
        for _ in 0..self.indent {
            indent.push(' ');
        }
        ProofTreePrinterImpl {
            p: self,
            f,
            indent,
            chr: self.indent - 1,
            stmt_lookup: new_map(),
            backref_alloc: vec![],
            backref_max: 0,
        }
        .fmt()
    }
}
