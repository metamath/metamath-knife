//! The `Segment` data structure, which holds most of the actual data in the file.

use std::{
    cmp::Ordering,
    ops::{Bound, Deref, RangeBounds},
    sync::Arc,
};

use crate::{
    diag::Diagnostic,
    statement::{
        Command, FloatDef, GlobalDv, HeadingDef, LabelDef, LocalVarDef, SegmentId, Span, Statement,
        StatementAddress, StatementIndex, StatementIter, SymbolDef, TokenAddress, DUMMY_STATEMENT,
        NO_STATEMENT,
    },
    Database, StatementRef,
};

/// Data structure which tracks the logical order of segment IDs, since they are
/// not intrinsically ordered.
///
/// This is an example of an "order-maintenance data structure", actually a very
/// simple one. We can plug in the Dietz & Sleator 1987 algorithm if this gets
/// too slow.
///
/// IDs are never reused after being released from the order, so they can be
/// used safely as part of change-tracking structures.
///
/// `SegmentOrder` implements the [`Comparer`] trait, allowing it to be used
/// polymorphically with the `cmp` method to order lists of segments,
/// statements, or tokens.
#[derive(Clone, Debug)]
pub(crate) struct SegmentOrder {
    high_water: u32,
    order: Vec<SegmentId>,
    reverse: Vec<usize>,
}

impl Default for SegmentOrder {
    fn default() -> Self {
        // pre-assign 1 as "start".  (think "cyclic order")
        SegmentOrder {
            high_water: 2,
            order: vec![SegmentId(1)],
            reverse: vec![0; 2],
        }
    }
}

impl SegmentOrder {
    /// Each segment ordering has a single ID which will not be used otherwise;
    /// pass this to `new_before` to get an ID larger than all created IDs.
    pub(crate) const START: SegmentId = SegmentId(1);

    fn alloc_id(&mut self) -> SegmentId {
        let index = self.high_water;
        assert!(index < u32::MAX);
        self.high_water += 1;
        SegmentId(index)
    }

    fn reindex(&mut self) {
        self.reverse = vec![0; self.high_water as usize];
        for (ordinal, &id) in self.order.iter().enumerate() {
            self.reverse[id.0 as usize] = ordinal;
        }
    }

    /// Indicates that an ID will no longer be used, allowing some memory to be
    /// freed.
    ///
    /// The ID itself will not be reissued.
    pub(crate) fn free_id(&mut self, id: SegmentId) {
        self.order.remove(self.reverse[id.0 as usize]);
        self.reindex();
    }

    /// Gets a new ID, and adds it to the order before the named ID, or at the
    /// end if you pass `start()`.
    pub(crate) fn new_before(&mut self, after: SegmentId) -> SegmentId {
        let id = self.alloc_id();
        self.order.insert(self.reverse[after.0 as usize], id);
        self.reindex();
        id
    }

    pub(crate) fn range(&self, range: impl RangeBounds<SegmentId>) -> SegmentIter<'_> {
        let start = match range.start_bound() {
            Bound::Included(id) => self.reverse[id.0 as usize],
            Bound::Excluded(id) => self.reverse[id.0 as usize] + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(id) => self.reverse[id.0 as usize] + 1,
            Bound::Excluded(id) => self.reverse[id.0 as usize],
            Bound::Unbounded => self.order.len(),
        };
        SegmentIter(self.order[start..end].iter())
    }
}

#[derive(Clone)]
pub(crate) struct SegmentIter<'a>(std::slice::Iter<'a, SegmentId>);

impl Iterator for SegmentIter<'_> {
    type Item = SegmentId;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().copied()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for SegmentIter<'_> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl DoubleEndedIterator for SegmentIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().copied()
    }
}

/// A trait for objects which can be used to order other datatypes.
pub trait Comparer<T> {
    /// Compares two objects, like `Ord::cmp`, but with additional state data
    /// from the comparer that can be used for the ordering.
    fn cmp(&self, left: &T, right: &T) -> Ordering;

    /// Returns true if the `left` argument is (strictly) less than the `right` argument
    #[inline]
    fn lt(&self, left: &T, right: &T) -> bool {
        self.cmp(left, right) == Ordering::Less
    }

    /// Returns true if the `left` argument is less or equal to the `right` argument
    #[inline]
    fn le(&self, left: &T, right: &T) -> bool {
        self.cmp(left, right) != Ordering::Greater
    }
}

impl Comparer<SegmentId> for SegmentOrder {
    fn cmp(&self, left: &SegmentId, right: &SegmentId) -> Ordering {
        self.reverse[left.0 as usize].cmp(&self.reverse[right.0 as usize])
    }
}

impl Comparer<StatementAddress> for SegmentOrder {
    fn cmp(&self, left: &StatementAddress, right: &StatementAddress) -> Ordering {
        self.cmp(&left.segment_id, &right.segment_id)
            .then_with(|| left.index.cmp(&right.index))
    }
}

impl Comparer<TokenAddress> for SegmentOrder {
    fn cmp(&self, left: &TokenAddress, right: &TokenAddress) -> Ordering {
        self.cmp(&left.statement, &right.statement)
            .then_with(|| left.token_index.cmp(&right.token_index))
    }
}

impl Comparer<SegmentId> for Database {
    fn cmp(&self, left: &SegmentId, right: &SegmentId) -> Ordering {
        self.parse_result().order.cmp(left, right)
    }
}

impl Comparer<StatementAddress> for Database {
    fn cmp(&self, left: &StatementAddress, right: &StatementAddress) -> Ordering {
        self.parse_result().order.cmp(left, right)
    }
}

impl Comparer<TokenAddress> for Database {
    fn cmp(&self, left: &TokenAddress, right: &TokenAddress) -> Ordering {
        self.parse_result().order.cmp(left, right)
    }
}

impl<T, C: Comparer<T>> Comparer<T> for &'_ C {
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        (*self).cmp(left, right)
    }
}

/// Shared reference to a buffer which will be parsed.
///
/// We use `u8` throughout the parser because Metamath databases are limited to
/// US-ASCII by the spec.  Since math symbols are used as tokens, if we wanted
/// to allow UTF-8 in the future it would be best to continue using `u8`,
/// although there would need to be a validity check (valid UTF-8 encodings are
/// always canonical) in `Scanner::get_raw` and the eighth-bit hack in
/// `scan_expression` would need to be reverted.
pub(crate) type BufferRef = Arc<Vec<u8>>;

/// A parsed segment, containing parsed statement data and some extractions.
///
/// This is the main result of the parse which is provided to `segment_set`,
/// although most users will want to use a `SegmentRef` instead.
///
/// This is a "dense" segment, which must be fully rebuilt in order to make any
/// change.  We may in the future have an "unpacked" segment which is used for
/// active editing, as well as a "lazy" or "mmap" segment type for fast
/// incremental startup.
#[derive(Debug)]
pub struct Segment {
    /// The original string used to construct this segment.
    ///
    /// Don't assume the segment is wholly determined by this string.
    pub buffer: BufferRef,
    /// List of statements in this segment; can be indexed with any
    /// `StatementIndex`.
    pub(crate) statements: Vec<Statement>,
    /// All math strings and proof strings in this segment, concatenated for
    /// fewer allocations.
    pub(crate) span_pool: Vec<Span>,
    /// Any errors detected while parsing this segment.
    pub diagnostics: Vec<(StatementIndex, Diagnostic)>,
    /// The file, if any, which is included at the end of this segment, as a
    /// reference into the buffer.
    pub next_file: Span,
    /// Global `$d` statements extracted for nameck.
    pub global_dvs: Vec<GlobalDv>,
    /// Global `$v` and `$c` statements extracted for nameck.
    pub symbols: Vec<SymbolDef>,
    /// Local `$v` statements extracted for nameck.
    pub local_vars: Vec<LocalVarDef>,
    /// Global labelled statements extracted for nameck.
    pub labels: Vec<LabelDef>,
    /// Global `$f` statements extracted for nameck.
    pub floats: Vec<FloatDef>,
    /// Top-level headings extracted for outline
    pub outline: Vec<HeadingDef>,
    /// Parser commands provided in $t typesetting comments.
    pub t_commands: Vec<(StatementIndex, Command)>,
    /// Parser commands provided in $j additional information comments.
    pub j_commands: Vec<(StatementIndex, Command)>,
}

/// A pointer to a segment which knows its identity.
///
/// `SegmentRef` objects are constructed from outside by the `segment_set`.
#[derive(Copy, Clone, Debug)]
pub struct SegmentRef<'a> {
    /// The underlying segment from the parser.
    pub segment: &'a Arc<Segment>,
    /// The global ID which has been assigned to the segment.
    pub id: SegmentId,
}

impl Deref for SegmentRef<'_> {
    type Target = Arc<Segment>;

    #[inline]
    fn deref(&self) -> &Arc<Segment> {
        self.segment
    }
}

impl<'a> SegmentRef<'a> {
    /// Fetch a single statement from this segment by its local index.
    #[must_use]
    pub fn statement(self, index: StatementIndex) -> StatementRef<'a> {
        StatementRef {
            segment: self,
            statement: &self.segment.statements[index as usize],
            index,
        }
    }

    /// Fetch a single statement from this segment by its local index,
    /// or return a dummy statement when the index is `NO_STATEMENT`.
    #[must_use]
    pub(crate) fn statement_or_dummy(self, index: StatementIndex) -> StatementRef<'a> {
        StatementRef {
            segment: self,
            statement: if index == NO_STATEMENT {
                &DUMMY_STATEMENT
            } else {
                &self.segment.statements[index as usize]
            },
            index,
        }
    }

    /// Returns the source size of the segment, a proxy for computational
    /// difficulty which drives the `database::Executor` bin-packing heuristics.
    #[must_use]
    pub fn bytes(self) -> usize {
        self.buffer.len()
    }

    /// Returns a new empty statement iterator.
    fn empty(self) -> StatementIter<'a> {
        StatementIter {
            slice_iter: [].iter(),
            segment: self,
            index: 0,
        }
    }

    /// Returns an iterator over a range of statement indices in the current segment.
    #[must_use]
    pub fn range(self, range: impl RangeBounds<StatementIndex>) -> StatementIter<'a> {
        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&i) => i as usize + 1,
            Bound::Excluded(&i) => i as usize,
            Bound::Unbounded => self.segment.statements.len(),
        };
        StatementIter {
            slice_iter: self.segment.statements[start as usize..end].iter(),
            segment: self,
            index: start,
        }
    }

    /// Returns an iterator over a range of statement addresses in the current segment.
    #[must_use]
    pub(crate) fn range_address(
        self,
        order: &SegmentOrder,
        range: impl RangeBounds<StatementAddress>,
    ) -> StatementIter<'a> {
        let start = match range.start_bound() {
            Bound::Included(addr) => match order.cmp(&addr.segment_id, &self.id) {
                Ordering::Less => Bound::Unbounded,
                Ordering::Equal => Bound::Included(addr.index),
                Ordering::Greater => return self.empty(),
            },
            Bound::Excluded(addr) => match order.cmp(&addr.segment_id, &self.id) {
                Ordering::Less => Bound::Unbounded,
                Ordering::Equal => Bound::Excluded(addr.index),
                Ordering::Greater => return self.empty(),
            },
            Bound::Unbounded => Bound::Unbounded,
        };
        let end = match range.end_bound() {
            Bound::Included(addr) => match order.cmp(&addr.segment_id, &self.id) {
                Ordering::Less => return self.empty(),
                Ordering::Equal => Bound::Included(addr.index),
                Ordering::Greater => Bound::Unbounded,
            },
            Bound::Excluded(addr) => match order.cmp(&addr.segment_id, &self.id) {
                Ordering::Less => return self.empty(),
                Ordering::Equal => Bound::Excluded(addr.index),
                Ordering::Greater => Bound::Unbounded,
            },
            Bound::Unbounded => Bound::Unbounded,
        };
        self.range((start, end))
    }
}

impl<'a> IntoIterator for SegmentRef<'a> {
    type Item = StatementRef<'a>;
    type IntoIter = StatementIter<'a>;

    /// An iterator over the statements in this segment.
    fn into_iter(self) -> Self::IntoIter {
        StatementIter {
            slice_iter: self.segment.statements.iter(),
            segment: self,
            index: 0,
        }
    }
}
