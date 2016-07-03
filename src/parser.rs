//! Implementation of the low-level statement parser for Metamath databases.
//!
//! The parser identifies the boundaries between statements, extracts their math
//! strings and proofs, does basic validity checking within statements, and
//! extracts a list of definitions which can be indexed by nameck.  This module
//! also defines the core datatypes used to represent source positions and
//! parsed statements, which are used by other analysis passes.
//!
//! Analysis passes are not a stable interface; use `Database` instead.
//!
//! The input of the parser is a byte string, which will typically consist of a
//! file except when the preparser is used; see the `database` module
//! documentation.  The output is one or more segments; the parser is
//! responsible for detecting includes and splitting statements appropriately,
//! although responsibility for following includes rests on the `segment_set`.
//!
//! ## Addresses, indices, and references
//!
//! To identify a statement uniquely, you need to know the segment ID, and the
//! offset of the statement within the segment.  This is two numbers; global
//! statement numbers can be computed, but are not widely used because they
//! change too frequently in an incremental setting.  Those two numbers together
//! can be handled as a `StatementAddress` structure.
//!
//! Within the parser itself, the segment ID is not known yet; they are assigned
//! after all file inclusions have been resolved, which can only be done after
//! the parsing phase is complete.  Fortunately, the parsing process always
//! works with one segment at a time, so it is sufficient to use the local
//! offset alone; the type `StatementIndex` is provided to make intent clear.
//! `StatementIndex` can also be used in other analysis passes if, for wahtever
//! reason, the segment ID is known from context.
//!
//! If you want to fetch actual data for a statement, you will need pointers
//! into the segment data structures which store statement data.  A
//! `StatementRef` structure encapsulates a statement address and all necessary
//! pointers to fetch data; it can be used to fetch any parse-time information,
//! but it is larger than a `StatementAddress`, and because it contains borrowed
//! pointers it cannot be stored in long-lived data structures in any event.
//!
//! `TokenAddress`, `TokenIndex`, and `TokenRef` are provided for the same use
//! cases as applied to tokens in math strings.  A `TokenAddress` contains three
//! numbers; you will often want to use the `Atom`s provided by scopeck instead,
//! as they are smaller and can be compared directly.
//!
//! `SegmentId` and `SegmentRef` cover the same use cases for segments, although
//! it makes no sense to have a segment-local segment reference.

use diag::Diagnostic;
use std::cmp;
use std::cmp::Ordering;
use std::mem;
use std::ops::Deref;
use std::slice;
use std::str;
use std::sync::Arc;

/// Shared reference to a buffer which will be parsed.
///
/// We use `u8` throughout the parser because Metamath databases are limited to
/// US-ASCII by the spec.  Since math symbols are used as tokens, if we wanted
/// to allow UTF-8 in the future it would be best to continue using `u8`,
/// although there would need to be a validity check (valid UTF-8 encodings are
/// always canonical) in `Scanner::get_raw` and the eighth-bit hack in
/// `scan_expression` would need to be reverted.
pub type BufferRef = Arc<Vec<u8>>;

/// Semantic type for positions in files.
///
/// Due to the use of half-open ranges, input files are limited to 4 GiB - 1.
pub type FilePos = u32;

/// Semantic type for statement indices.
///
/// Since the shortest possible statement is three bytes, this cannot overflow
/// before `FilePos` does.
///
/// smetamath3 uses SMM2 statement numbering semantics, and counts all
/// statements from the spec (including group open and group close), as well as
/// counting comments as their own statements.
pub type StatementIndex = i32;

/// Constant used in valid ranges to indicate the logical end of the database.
pub const NO_STATEMENT: StatementIndex = -1;

/// Semantic type for file-position ranges.
///
/// Spans will generally not be empty.  An empty span at position 0 is called a
/// null span used as a sentinel value by several functions.
#[derive(Copy,Clone,Eq,PartialEq,Debug,Default)]
pub struct Span {
    /// Index of first character of the range.
    pub start: FilePos,
    /// Index one past last character of the range.
    pub end: FilePos,
}

impl Span {
    /// Coercion from array index pairs.
    pub fn new(start: usize, end: usize) -> Span {
        Span {
            start: start as FilePos,
            end: end as FilePos,
        }
    }

    fn new2(start: FilePos, end: FilePos) -> Span {
        Span {
            start: start,
            end: end,
        }
    }

    /// Returns the null span.
    pub fn null() -> Span {
        Span::new(0, 0)
    }

    /// Checks for the null span, i.e. zero length at offset zero.
    pub fn is_null(self) -> bool {
        self.end == 0
    }

    /// Given a position span, extract the corresponding characters from a
    /// buffer.
    pub fn as_ref(self, buf: &[u8]) -> &[u8] {
        &buf[self.start as usize..self.end as usize]
    }
}

/// Semantic type for segment identifiers, as an opacified integer.
///
/// Since segment identifiers are reused between incremental runs, and new
/// segments can be inserted between any two existing segments, the internal
/// numeric order of segment identifiers need not mean anything at all and is
/// not exposed.  If you need to compare segment identifiers for order, get a
/// reference to the database's `SegmentOrder` object.
#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash,Default)]
pub struct SegmentId(pub u32);

/// Semantic type for the index of a token in a statement.
///
/// Each token consumes at least two characters, plus a three-byte keyword and
/// space to introduce the math string at the beginning of the file, so this
/// cannot overflow for files of valid length.
pub type TokenIndex = i32;

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
/// SegmentOrder implements the `Comparer` trait, allowing it to be used
/// polymorphically with the `cmp` method to order lists of segments,
/// statements, or tokens.
#[derive(Clone,Debug,Default)]
pub struct SegmentOrder {
    high_water: u32,
    order: Vec<SegmentId>,
    reverse: Vec<usize>,
}

impl SegmentOrder {
    /// Creates a new empty segment ordering.
    pub fn new() -> Self {
        // pre-assign 1 as "start".  (think "cyclic order")
        SegmentOrder {
            high_water: 2,
            order: vec![SegmentId(1)],
            reverse: vec![0; 2],
        }
    }

    /// Each segment ordering has a single ID which will not be used otherwise;
    /// pass this to `new_before` to get an ID larger than all created IDs.
    pub fn start(&self) -> SegmentId {
        SegmentId(1)
    }

    fn alloc_id(&mut self) -> SegmentId {
        let index = self.high_water;
        assert!(index < u32::max_value());
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
    pub fn free_id(&mut self, id: SegmentId) {
        self.order.remove(self.reverse[id.0 as usize] as usize);
        self.reindex();
    }

    /// Gets a new ID, and adds it to the order before the named ID, or at the
    /// end if you pass `start()`.
    pub fn new_before(&mut self, after: SegmentId) -> SegmentId {
        let id = self.alloc_id();
        self.order.insert(self.reverse[after.0 as usize] as usize, id);
        self.reindex();
        id
    }
}

/// A trait for objects which can be used to order other datatypes.
pub trait Comparer<T> {
    /// Compares two objects, like `Ord::cmp`, but with additional state data
    /// from the comparer that can be used for the ordering.
    fn cmp(&self, left: &T, right: &T) -> Ordering;
}

impl Comparer<SegmentId> for SegmentOrder {
    fn cmp(&self, left: &SegmentId, right: &SegmentId) -> Ordering {
        self.reverse[left.0 as usize].cmp(&self.reverse[right.0 as usize])
    }
}

impl Comparer<StatementAddress> for SegmentOrder {
    fn cmp(&self, left: &StatementAddress, right: &StatementAddress) -> Ordering {
        let order = self.cmp(&left.segment_id, &right.segment_id);
        (order, left.index).cmp(&(Ordering::Equal, right.index))
    }
}

impl Comparer<TokenAddress> for SegmentOrder {
    fn cmp(&self, left: &TokenAddress, right: &TokenAddress) -> Ordering {
        let order = self.cmp(&left.statement, &right.statement);
        (order, left.token_index).cmp(&(Ordering::Equal, right.token_index))
    }
}

impl<'a, T, C: Comparer<T>> Comparer<T> for &'a C {
    fn cmp(&self, left: &T, right: &T) -> Ordering {
        (*self).cmp(left, right)
    }
}

/// A statement is located by giving its segment and index within the segment.
#[derive(Copy,Clone,Eq,PartialEq,Hash,Debug,Default)]
pub struct StatementAddress {
    /// Segment which contains the statement.
    pub segment_id: SegmentId,
    /// Zero-based index of the statement.
    pub index: StatementIndex,
}

impl StatementAddress {
    /// Constructs a statement address from its parts.
    pub fn new(segment_id: SegmentId, index: StatementIndex) -> Self {
        StatementAddress {
            segment_id: segment_id,
            index: index,
        }
    }
}

impl StatementAddress {
    /// Convert a statement address into a statement range from here to the
    /// logical end of the database.
    pub fn unbounded_range(self) -> GlobalRange {
        GlobalRange {
            start: self,
            end: NO_STATEMENT,
        }
    }
}

/// A token is located within a $c or $v by giving the address of the declaring
/// statement and the zero-based index within the math string.
///
/// In most cases you will use `Atom` instead, so the size of this struct, while
/// a bit silly, doesn't matter so much.
#[derive(Copy,Clone,Eq,PartialEq,Debug,Default)]
pub struct TokenAddress {
    /// Address of the statement in which the token is defined.
    pub statement: StatementAddress,
    /// Index of the token within the defining statement's math string.
    pub token_index: TokenIndex,
}

impl TokenAddress {
    /// Constructs a token address from parts.
    pub fn new3(segment_id: SegmentId, index: StatementIndex, token: TokenIndex) -> Self {
        TokenAddress {
            statement: StatementAddress::new(segment_id, index),
            token_index: token,
        }
    }
}

/// Expresses a valid range for a statement or token.
#[derive(Copy,Clone,Debug,Default)]
pub struct GlobalRange {
    /// The starting position of the range, which is also the definition site.
    pub start: StatementAddress,
    /// The exclusive endpoint of the range.
    ///
    /// Since scope braces are not allowed to span segments, if a range ends at
    /// all it must be in the same segment where it started, so this can be a
    /// bare `StatementIndex`.  If the range extends to the logical end of the
    /// database, that is represented with the NO_STATEMENT constant.
    ///
    /// Since the endpoint always points at a `CloseGroup` statement (or, in
    /// erroneous cases, `Eof` or `FileInclude`) which has no label nor math
    /// string, inclusivity versus exclusivity rarely comes up.
    pub end: StatementIndex,
}

/// Semantic type for tokens which have been copied onto the heap.
///
/// Tokens are generally expected to be non-empty and consist of ASCII graphic
/// characters.  Notably, the construction of compressed math strings in the
/// verifier depends on tokens containing bytes less than 128.
pub type Token = Box<[u8]>;

/// Semantic type for tokens which have not been copied.
pub type TokenPtr<'a> = &'a [u8];

/// Copies a non-owned token onto the heap.
pub fn copy_token(ptr: TokenPtr) -> Token {
    ptr.to_owned().into_boxed_slice()
}

/// Extracted data for a top-level `$d` statement in a segment.
#[derive(Debug)]
pub struct GlobalDv {
    /// The location of the statement.
    pub start: StatementIndex,
    /// The variables used in the statement.
    pub vars: Vec<Token>,
}

/// Types of math symbols in declarations.
#[derive(Eq,PartialEq,Copy,Clone,Debug)]
pub enum SymbolType {
    /// `$v`
    Variable,
    /// `$c`
    Constant,
}

/// Extracted information for a statement label in a segment.
#[derive(Debug)]
pub struct LabelDef {
    /// The location of the labelled statement.
    pub index: StatementIndex,
}

/// Extracted information for a math symbol defined in a segment.
#[derive(Debug)]
pub struct SymbolDef {
    /// The character sequence representing the symbol.
    pub name: Token,
    /// The type of the statement which introduces the symbol.
    pub stype: SymbolType,
    /// The location of the statement which introduces the symbol.
    pub start: StatementIndex,
    /// Index of the symbol within its introducing statement.
    pub ordinal: TokenIndex,
}

/// Extracted information for a global `$f` statement in a segment.
#[derive(Debug)]
pub struct FloatDef {
    /// Location of the statement.
    pub start: StatementIndex,
    /// The math symbol which is the subject of the statement.
    pub name: Token,
    /// The label of the `$f` statement.
    pub label: Token,
    /// The typecode which is assigned to the symbol.
    pub typecode: Token,
}

/// Extracted information for a _non-global_ `$v` statement.
///
/// These are used to populate the atom table in nameck.
#[derive(Debug)]
pub struct LocalVarDef {
    /// Local index of the variable-declaring statement.
    pub index: StatementIndex,
    /// Index of variable within the statement.
    pub ordinal: TokenIndex,
}

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
    statements: Vec<Statement>,
    /// All math strings and proof strings in this segment, concatenated for
    /// fewer allocations.
    span_pool: Vec<Span>,
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
}

/// A pointer to a segment which knows its identity.
///
/// `SegmentRef` objects are constructed from outside by the `segment_set`.
#[derive(Copy,Clone)]
pub struct SegmentRef<'a> {
    /// The underlying segment from the parser.
    pub segment: &'a Arc<Segment>,
    /// The global ID which has been assigned to the segment.
    pub id: SegmentId,
}

impl<'a> Deref for SegmentRef<'a> {
    type Target = Arc<Segment>;

    #[inline]
    fn deref(&self) -> &Arc<Segment> {
        self.segment
    }
}

impl<'a> SegmentRef<'a> {
    /// Fetch a single statement from this segment by its local index.
    pub fn statement(self, index: StatementIndex) -> StatementRef<'a> {
        StatementRef {
            segment: self,
            statement: &self.segment.statements[index as usize],
            index: index,
        }
    }

    /// Returns the source size of the segment, a proxy for computational
    /// difficulty which drives the `database::Executor` bin-packing heuristics.
    pub fn bytes(self) -> usize {
        self.buffer.len()
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

/// An enumeration of statement types, most of which correspond to statements as
/// defined in the Metamath spec.
#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum StatementType {
    /// Psuedo statement used only to record end-of-file whitespace.
    Eof,
    /// Statement which is damaged enough that there's no sense passing it to
    /// later stages.
    Invalid,
    /// Comments between statements are recorded as statements in their own
    /// right to facilitate handling of date comments and other metadata.
    Comment,
    /// A comment which starts with a `$t` token and must be interpreted
    /// specially by the HTML generator.
    TypesettingComment,
    /// A `$[` directive; we process these as statements, and disallow them
    /// inside other statements, which violates the published Metamath spec but
    /// is allowed behavior as an erratum.
    ///
    /// Such statements always end the current segment.
    FileInclude,
    /// A spec `$a` statement.
    Axiom,
    /// A spec `$p` statement.
    Provable,
    /// A spec `$e` statement.
    Essential,
    /// A spec `$f` statement.
    Floating,
    /// A spec `$d` statement.
    Disjoint,
    /// A spec `${` statement.
    OpenGroup,
    /// A spec `$}` statement.
    CloseGroup,
    /// A spec `$c` statement.
    Constant,
    /// A spec `$v` statement.
    Variable,
}
use self::StatementType::*;

impl Default for StatementType {
    fn default() -> StatementType {
        Invalid
    }
}

impl StatementType {
    fn takes_label(self) -> bool {
        match self {
            Axiom | Provable | Essential | Floating => true,
            _ => false,
        }
    }

    fn takes_math(self) -> bool {
        match self {
            Axiom | Provable | Essential | Floating | Disjoint | Constant | Variable => true,
            _ => false,
        }
    }
}

/// Data stored inline in the segment for each statement.
///
/// Tokens and labels are not copied, but kept as references into the segment's
/// buffer; we do calculate and store the length, because recalculating it on
/// the fly would blow the branch miss budget.
///
/// The spans comprising the math and proof strings, and the parse errors if
/// any, are stored in separate arrays within the segment.
#[derive(Copy,Clone,Debug)]
struct Statement {
    /// Statement type, either a spec-defined type or one of the pseudo-types.
    stype: StatementType,
    /// Total span of the statement, not including trailing whitespace or
    /// surrounding comments.
    span: Span,
    /// Span of the statement label.
    ///
    /// This will be non-null iff the type requires a label; missing labels for
    /// types which use them cause an immediate rewrite to `Invalid`.
    label: Span,
    /// Start of the most deeply nested group for this statment, or
    /// NO_STATEMENT.
    group: StatementIndex,
    /// End of the most deeply nested group for this statment, or NO_STATEMENT.
    group_end: StatementIndex,
    /// Index into span_pool of the first math token.
    math_start: usize,
    /// Index into span_pool of the first proof token / after the last math
    /// token.
    proof_start: usize,
    /// Index into span_pool one after the last proof token.
    proof_end: usize,
}

/// A reference to a statement which knows its address and can be used to fetch
/// statement information.
#[derive(Copy,Clone)]
pub struct StatementRef<'a> {
    segment: SegmentRef<'a>,
    statement: &'a Statement,
    index: StatementIndex,
}

impl<'a> StatementRef<'a> {
    /// Fetch the segment-local index of this statement.
    pub fn index(self) -> StatementIndex {
        self.index
    }

    /// Back up from a statement reference to a segment reference.
    pub fn segment(self) -> SegmentRef<'a> {
        self.segment
    }

    /// Gets the type of this statement.  May be a pseudo-type.
    pub fn statement_type(self) -> StatementType {
        self.statement.stype
    }

    /// Obtain a globally-meaningful address for this statement.
    pub fn address(self) -> StatementAddress {
        StatementAddress {
            segment_id: self.segment.id,
            index: self.index,
        }
    }

    /// Constructs a range from this statement to the end of the database or
    /// innermost enclosing scope construct.
    ///
    /// This is the end range of a hypothesis or variable defined in this
    /// statement.
    pub fn scope_range(self) -> GlobalRange {
        GlobalRange {
            start: self.address(),
            end: self.statement.group_end,
        }
    }

    /// True if there is a `${ $}` group wrapping this statement.
    pub fn in_group(self) -> bool {
        self.statement.group_end != NO_STATEMENT
    }

    /// Obtain the statment label.
    ///
    /// This will be non-null iff the type requires a label; missing labels for
    /// types which use them cause an immediate rewrite to `Invalid`.
    pub fn label(&self) -> &'a [u8] {
        self.statement.label.as_ref(&self.segment.segment.buffer)
    }

    /// An iterator for the symbols in a statement's math string.
    pub fn math_iter(&self) -> TokenIter<'a> {
        let range = self.statement.math_start..self.statement.proof_start;
        TokenIter {
            slice_iter: self.segment.segment.span_pool[range].iter(),
            buffer: &self.segment.segment.buffer,
            stmt_address: self.address(),
            index: 0,
        }
    }

    /// The textual span of this statement within the segment's buffer.
    ///
    /// Does not include trailing white space or surrounding comments; will
    /// include leading white space, so a concatenation of spans for all
    /// statements will reconstruct the segment source.
    pub fn span(&self) -> Span {
        self.statement.span
    }

    /// Count of symbols in this statement's math string.
    pub fn math_len(&self) -> TokenIndex {
        (self.statement.proof_start - self.statement.math_start) as TokenIndex
    }

    /// Count of tokens in this statement's proof string.
    pub fn proof_len(&self) -> TokenIndex {
        (self.statement.proof_end - self.statement.proof_start) as TokenIndex
    }

    /// Given an index into this statement's math string, find a textual span
    /// into the segment buffer.
    pub fn math_span(&self, ix: TokenIndex) -> Span {
        self.segment.span_pool[self.statement.math_start + ix as usize]
    }

    /// Given an index into this statement's proof string, find a textual span
    /// into the segment buffer.
    pub fn proof_span(&self, ix: TokenIndex) -> Span {
        self.segment.span_pool[self.statement.proof_start + ix as usize]
    }

    /// Given an index into this statement's math string, get a reference to the
    /// math token.
    pub fn math_at(&self, ix: TokenIndex) -> TokenRef<'a> {
        TokenRef {
            slice: self.math_span(ix).as_ref(&self.segment.segment.buffer),
            address: TokenAddress {
                statement: self.address(),
                token_index: ix,
            },
        }
    }

    /// Obtains textual proof data by token index.
    pub fn proof_slice_at(&self, ix: TokenIndex) -> TokenPtr<'a> {
        self.proof_span(ix).as_ref(&self.segment.segment.buffer)
    }
}

/// An iterator over the statements in a segment.
///
/// This iterator knows the segment's global ID and can thus return proper
/// `StatementRef`s.
pub struct StatementIter<'a> {
    slice_iter: slice::Iter<'a, Statement>,
    segment: SegmentRef<'a>,
    index: StatementIndex,
}

impl<'a> Iterator for StatementIter<'a> {
    type Item = StatementRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.slice_iter.next().map(|st_ref| {
            let index = self.index;
            self.index += 1;
            StatementRef {
                segment: self.segment,
                statement: st_ref,
                index: index,
            }
        })
    }
}

/// An iterator over symbols in the math string of a statement.
pub struct TokenIter<'a> {
    slice_iter: slice::Iter<'a, Span>,
    buffer: &'a [u8],
    stmt_address: StatementAddress,
    index: TokenIndex,
}

/// A reference to a token within a math string that knows its address.
///
/// Primarily used for iteration.
#[derive(Copy,Clone)]
pub struct TokenRef<'a> {
    /// Textual content of the token.
    pub slice: TokenPtr<'a>,
    /// 3-component address of the token.
    pub address: TokenAddress,
}

impl<'a> Deref for TokenRef<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.slice
    }
}

impl<'a> TokenRef<'a> {
    /// Get the local index of the token within the statement under iteration.
    pub fn index(self) -> TokenIndex {
        self.address.token_index
    }
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = TokenRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.slice_iter.next().map(|spanref| {
            let index = self.index;
            self.index += 1;
            TokenRef {
                slice: spanref.as_ref(self.buffer),
                address: TokenAddress {
                    statement: self.stmt_address,
                    token_index: index,
                },
            }
        })
    }
}

/// State used by the scanning process
#[derive(Default)]
struct Scanner<'a> {
    /// Text being parsed.
    buffer: &'a [u8],
    /// Arc of text which can be linked into new Segments.
    buffer_ref: BufferRef,
    /// Current parsing position; will generally point immediately after a
    /// token, at whitespace.
    position: FilePos,
    /// Accumulated errors for this segment.  Reset on new segment.
    diagnostics: Vec<(StatementIndex, Diagnostic)>,
    /// Accumulated spans for this segment.
    span_pool: Vec<Span>,
    /// A span which was encountered, but needs to be processed again.
    ///
    /// This is used for error recovery if you leave off the `$.` which ends a
    /// math string, the parser will encounter the next keyword and needs to
    /// save that token to process it as a keyword.
    unget: Span,
    /// Labels accumulated for the current statement.
    labels: Vec<Span>,
    /// End of the previous statement
    statement_start: FilePos,
    /// Current write index into statement list
    statement_index: StatementIndex,
    /// Write indexes into span pools
    statement_math_start: usize,
    statement_proof_start: usize,
    /// Flag which can be set at any time during statement parse to cause the
    /// type to be overwritten with `Invalid`, if the statement would otherwise
    /// be too broken to continue with.
    invalidated: bool,
}

/// Bitmask of allowed whitespace characters.
///
/// A Metamath database is required to consist of graphic characters, SP, HT,
/// NL, FF, and CR.
const MM_VALID_SPACES: u64 = (1u64 << 9) | (1u64 << 10) | (1u64 << 12) | (1u64 << 13) |
                             (1u64 << 32);

/// Check if a character which is known to be <= 32 is a valid Metamath
/// whitespace.  May panic if out of range.
fn is_mm_space_c0(byte: u8) -> bool {
    (MM_VALID_SPACES & (1u64 << byte)) != 0
}

/// Check if a character is valid Metamath whitespace.
///
/// We generally accept any C0 control as whitespace, with a diagnostic; this
/// function only tests for fully legal whitespace though.
fn is_mm_space(byte: u8) -> bool {
    byte <= 32 && is_mm_space_c0(byte)
}

// TODO: add outline comment detection
#[derive(Eq,PartialEq,Copy,Clone)]
enum CommentType {
    Normal,
    Typesetting,
    Extra,
}

impl<'a> Scanner<'a> {
    /// Record a diagnostic against the nascent statement
    fn diag(&mut self, diag: Diagnostic) {
        self.diagnostics.push((self.statement_index, diag));
    }

    /// Get a single whitespace-delimited token from the source text without
    /// checking for comments or the unget area.
    ///
    /// This function accepts any C0 character as whitespace, with a diagnostic.
    /// DEL and non-7bit characters invalidate the current token and cause it to
    /// be omitted from the returned string.  `Span::null()` is returned when
    /// the end of the buffer is reached.
    ///
    /// This is _very_ hot, mostly due to the unpredicable branches in the
    /// whitespace testing.  It might be possible to write a version which is
    /// branch-free in typical cases, but it would be extremely fiddly and has
    /// not been attempted.
    fn get_raw(&mut self) -> Span {
        #[inline(never)]
        #[cold]
        fn badchar(slf: &mut Scanner, ix: usize) -> Span {
            let ch = slf.buffer[ix];
            slf.diag(Diagnostic::BadCharacter(ix, ch));
            // Restart the function from the beginning to reload self.buffer;
            // doing it this way lets it be kept in a register in the common
            // case
            return slf.get_raw();
        }

        let len = self.buffer.len();
        let mut ix = self.position as usize;

        while ix < len && self.buffer[ix] <= 32 {
            // For the purpose of error recovery, we consider C0 control
            // characters to be whitespace (following SMM2)
            if !is_mm_space_c0(self.buffer[ix]) {
                self.position = (ix + 1) as FilePos;
                return badchar(self, ix);
            }
            ix += 1;
        }

        let start = ix;
        while ix < len {
            if self.buffer[ix] <= 32 || self.buffer[ix] > 126 {
                if self.buffer[ix] <= 32 {
                    break;
                }
                // DEL or C1 control or non-ASCII bytes (presumably UTF-8)
                let badix = ix;
                // skip this "token"
                ix += 1;
                while ix < len && !is_mm_space(self.buffer[ix]) {
                    ix += 1;
                }
                self.position = ix as FilePos;
                return badchar(self, badix);
            }

            ix += 1;
        }

        self.position = ix as FilePos;
        if start == ix {
            Span::null()
        } else {
            Span::new(start, ix)
        }
    }

    /// Assuming that a `$(` token has just been read, read and skip a comment.
    ///
    /// If the comment appears to be special, notice that.  This currently
    /// detects `$j` and `$t` comments, it will later be responsible for
    /// detecting outline comments.
    fn get_comment(&mut self, opener: Span, mid_statement: bool) -> CommentType {
        let mut ctype = CommentType::Normal;
        let mut first = true;
        loop {
            let tok = self.get_raw();
            if tok.is_null() {
                break;
            }
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$)" {
                return ctype;
            } else if tok_ref == b"$j" || tok_ref == b"$t" {
                if !first {
                    self.diag(Diagnostic::CommentMarkerNotStart(tok))
                } else if mid_statement {
                    self.diag(Diagnostic::MidStatementCommentMarker(tok))
                } else {
                    ctype = if tok_ref == b"$j" {
                        CommentType::Extra
                    } else {
                        CommentType::Typesetting
                    }
                }
            } else if tok_ref.contains(&b'$') {
                let tok_str = str::from_utf8(tok_ref).unwrap();
                if tok_str.contains("$)") {
                    self.diag(Diagnostic::BadCommentEnd(tok, opener));
                }
                if tok_str.contains("$(") {
                    self.diag(Diagnostic::NestedComment(tok, opener));
                }
            }

            first = false;
        }

        let cspan = Span::new2(opener.start, self.buffer.len() as FilePos);
        self.diag(Diagnostic::UnclosedComment(cspan));
        ctype
    }

    /// Fetches a single normal token from the buffer, skipping over comments
    /// and handling unget.
    fn get(&mut self) -> Span {
        if !self.unget.is_null() {
            return mem::replace(&mut self.unget, Span::null());
        }

        loop {
            let tok = self.get_raw();
            if tok.is_null() {
                return Span::null();
            }
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$(" {
                self.get_comment(tok, true);
            } else {
                return tok;
            }
        }
    }

    /// This is where statements are constructed, factored out between comment
    /// statements and non-comment.
    fn out_statement(&mut self, stype: StatementType, label: Span) -> Statement {
        Statement {
            stype: stype,
            label: label,
            math_start: self.statement_math_start,
            proof_start: self.statement_proof_start,
            proof_end: self.span_pool.len(),
            group: NO_STATEMENT,
            group_end: NO_STATEMENT,
            span: Span::new2(mem::replace(&mut self.statement_start, self.position),
                             self.position),
        }
    }

    /// Check for and parse a comment statement at the current position.
    fn get_comment_statement(&mut self) -> Option<Statement> {
        let ftok = if self.unget.is_null() {
            self.get_raw()
        } else {
            mem::replace(&mut self.unget, Span::null())
        };
        if ftok != Span::null() {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let ctype = self.get_comment(ftok, false);
                let stype = if ctype == CommentType::Typesetting {
                    TypesettingComment
                } else {
                    Comment
                };
                return Some(self.out_statement(stype, Span::null()));
            } else {
                self.unget = ftok;
            }
        }
        None
    }

    /// Reads zero or more labels from the input stream.
    ///
    /// We haven't seen the statement-starting keyword yet, so we don't know if
    /// labels are actually expected; just read, validate and store them.
    fn read_labels(&mut self) {
        self.labels.clear();
        loop {
            let ltok = self.get();
            if ltok.is_null() {
                break;
            }
            let lref = ltok.as_ref(self.buffer);
            if lref.contains(&b'$') {
                self.unget = ltok;
                break;
            } else if !is_valid_label(lref) {
                self.diag(Diagnostic::BadLabel(ltok));
            } else {
                self.labels.push(ltok);
            }
        }
    }

    /// We now know we shouldn't have labels.  Issue errors if we do anyway.
    fn get_no_label(&mut self) {
        // none of these are invalidations...
        for &lspan in &self.labels {
            self.diagnostics.push((self.statement_index, Diagnostic::SpuriousLabel(lspan)));
        }
    }

    /// We now know we need exactly one label.  Error and invalidate if we don't
    /// have it.
    fn get_label(&mut self) -> Span {
        match self.labels.len() {
            1 => self.labels[0],
            0 => {
                self.diag(Diagnostic::MissingLabel);
                self.invalidated = true;
                Span::null()
            }
            _ => {
                for &addl in self.labels.iter().skip(1) {
                    self.diagnostics
                        .push((self.statement_index,
                               Diagnostic::RepeatedLabel(addl, self.labels[0])));
                }
                // have to invalidate because we don't know which to use
                self.invalidated = true;
                Span::null()
            }
        }
    }

    /// Handles parsing for math and proof strings.
    ///
    /// Set `is_proof` to parse a proof, else we are parsing a math string.
    /// Returns true if there is a proof following and generates diagnostics as
    /// appropriate depending on `expect_proof`.
    ///
    /// Directly populates the span pool; record the span pool offset before and
    /// after calling to get at the string.
    fn get_string(&mut self, expect_proof: bool, is_proof: bool) -> bool {
        loop {
            let tokn = self.get();
            if tokn.is_null() {
                break;
            }
            let toknref = tokn.as_ref(self.buffer);
            if toknref.contains(&b'$') {
                if toknref == b"$." {
                    // string is closed with no proof
                    if expect_proof {
                        self.diag(Diagnostic::MissingProof(tokn));
                    }
                    return false;
                } else if toknref == b"$=" && !is_proof {
                    // string is closed with a proof
                    if !expect_proof {
                        self.diag(Diagnostic::SpuriousProof(tokn));
                    }
                    return true;
                } else {
                    // string is closed with no proof and with an error, whoops
                    self.unget = tokn;
                    break;
                }
            } else {
                self.span_pool.push(tokn);
            }
        }

        self.diag(if is_proof {
            Diagnostic::UnclosedProof
        } else {
            Diagnostic::UnclosedMath
        });
        return false;
    }

    /// Parses math and proof strings for the current statement and records the
    /// offsets appropriately.
    fn get_strings(&mut self, want_proof: bool) {
        let has_proof = self.get_string(want_proof, false);
        self.statement_proof_start = self.span_pool.len();

        if self.statement_proof_start == self.statement_math_start {
            self.invalidated = true;
            // this is invalid for all types of math string
            self.diag(Diagnostic::EmptyMathString);
        }

        if has_proof {
            // diagnostic already generated if unwanted, but we still need to
            // eat the proof
            self.get_string(false, true);
        } else {
            // diagnostic already generated if unwanted.  this is NOT an
            // invalidation as $p statements don't need proofs (I mean you
            // should have a ? but we know what you mean)
        }
    }

    /// When we see an invalid statement keyword, eat tokens until we see
    /// another keyword or a statement end marker.
    fn eat_invalid(&mut self) {
        loop {
            let tok = self.get();
            if tok.is_null() {
                break;
            }
            let tref = tok.as_ref(self.buffer);
            if tref == b"$." {
                // we're probably synchronized
                break;
            } else if tref == b"$=" {
                // this is definitely not it
            } else if tref.contains(&b'$') {
                // might be the start of the next statement
                self.unget = tok;
                break;
            }
        }
    }

    /// Handles parsing the filename after a `$[` keyword has been seen.
    ///
    /// Per the spec, filenames are restricted to the syntax of math tokens.
    fn get_file_include(&mut self) -> Span {
        let mut res = Span::null();
        let mut count = 0;
        loop {
            let tok = self.get();
            if tok.is_null() {
                break;
            }
            let tref = tok.as_ref(self.buffer);
            if tref == b"$]" {
                if count == 0 {
                    self.diag(Diagnostic::EmptyFilename);
                    self.invalidated = true;
                } else if count > 1 {
                    self.diag(Diagnostic::FilenameSpaces);
                    self.invalidated = true;
                } else if res.as_ref(self.buffer).contains(&b'$') {
                    self.diag(Diagnostic::FilenameDollar);
                }
                return res;
            } else if tref.len() > 0 && tref[0] == b'$' {
                break;
            } else {
                count += 1;
                res = tok;
            }
        }
        self.diag(Diagnostic::UnclosedInclude);
        self.invalidated = true;
        return res;
    }

    /// Main function called to read a complete statement from the input buffer.
    fn get_statement(&mut self) -> Statement {
        self.statement_start = self.position;
        self.statement_math_start = self.span_pool.len();
        self.statement_proof_start = self.span_pool.len();

        // is there a freestanding comment?
        if let Some(stmt) = self.get_comment_statement() {
            return stmt;
        }

        // look for labels before the keyword
        self.read_labels();

        let kwtok = self.get();
        let stype = if kwtok.is_null() {
            Eof
        } else {
            let kwtok_ref = kwtok.as_ref(self.buffer);
            if kwtok_ref.len() == 2 && kwtok_ref[0] == b'$' {
                match kwtok_ref[1] {
                    b'[' => FileInclude,
                    b'a' => Axiom,
                    b'c' => Constant,
                    b'd' => Disjoint,
                    b'e' => Essential,
                    b'f' => Floating,
                    b'p' => Provable,
                    b'v' => Variable,
                    b'{' => OpenGroup,
                    b'}' => CloseGroup,
                    _ => Invalid,
                }
            } else {
                Invalid
            }
        };
        if stype == Invalid {
            self.diag(Diagnostic::UnknownKeyword(kwtok));
        }
        self.invalidated = false;

        // handle any labels recorded earlier appropriately
        let mut label = if stype.takes_label() {
            self.get_label()
        } else {
            self.get_no_label();
            Span::null()
        };

        // keyword is followed by strings; this also errors if the string is
        // empty
        if stype.takes_math() {
            self.get_strings(stype == Provable);
        }

        // $d and $f statements require at least two tokens, check that now
        let math_len = self.statement_proof_start - self.statement_math_start;
        match stype {
            FileInclude => label = self.get_file_include(),
            Disjoint => {
                // math.len = 1 was caught above
                if math_len == 1 {
                    self.diag(Diagnostic::DisjointSingle);
                    self.invalidated = true;
                }
            }
            Floating => {
                // math_len = 0 was already marked EmptyMathString
                if math_len != 0 && math_len != 2 {
                    self.diag(Diagnostic::BadFloating);
                    self.invalidated = true;
                }
            }
            // eat tokens to the next keyword rather than treating them as
            // labels
            Invalid => self.eat_invalid(),
            _ => {}
        }

        let stype = if self.invalidated {
            Invalid
        } else {
            stype
        };

        self.out_statement(stype, label)
    }

    /// Reads statements until EOF or an include statement, which breaks logical
    /// order and requires a new segment.
    ///
    /// Also does extractions for the benefit of nameck.  Second return value is
    /// true if we are at EOF.
    fn get_segment(&mut self) -> (Segment, bool) {
        let mut seg = Segment {
            statements: Vec::new(),
            next_file: Span::null(),
            symbols: Vec::new(),
            local_vars: Vec::new(),
            global_dvs: Vec::new(),
            labels: Vec::new(),
            floats: Vec::new(),
            buffer: self.buffer_ref.clone(),
            diagnostics: Vec::new(),
            span_pool: Vec::new(),
        };
        let mut top_group = NO_STATEMENT;
        let is_end;
        let end_diag;

        loop {
            let index = seg.statements.len() as StatementIndex;
            self.statement_index = index;
            let mut stmt = self.get_statement();
            stmt.group = top_group;
            seg.statements.push(stmt);

            // This manages the group stack, and sets `group` on all statements
            // to the `OpenGroup` of the innermost enclosing group (or the
            // matching opener, for `CloseGroup`).
            match seg.statements[index as usize].stype {
                OpenGroup => top_group = index,
                CloseGroup => {
                    if top_group == NO_STATEMENT {
                        self.diag(Diagnostic::UnmatchedCloseGroup);
                    } else {
                        seg.statements[top_group as usize].group_end = index;
                        top_group = seg.statements[top_group as usize].group;
                    }
                }
                Constant => {
                    if top_group != NO_STATEMENT {
                        self.diag(Diagnostic::ConstantNotTopLevel);
                    }
                }
                Essential => {
                    if top_group == NO_STATEMENT {
                        self.diag(Diagnostic::EssentialAtTopLevel);
                    }
                }
                FileInclude => {
                    // snag this _now_
                    seg.next_file = seg.statements[index as usize].label;
                    end_diag = Diagnostic::UnclosedBeforeInclude(index);
                    is_end = false;
                    break;
                }
                Eof => {
                    end_diag = Diagnostic::UnclosedBeforeEof;
                    is_end = true;
                    break;
                }
                _ => {}
            }
        }

        // make sure they're not trying to continue an open group past EOF or a
        // file include
        while top_group != NO_STATEMENT {
            seg.statements[top_group as usize].group_end = seg.statements.len() as StatementIndex;
            self.diagnostics.push((top_group, end_diag.clone()));
            top_group = seg.statements[top_group as usize].group;
        }

        // populate `group_end` for statements in groups; was set for
        // `OpenGroup` in the loop above, and we don't want to overwrite it
        for index in 0..seg.statements.len() {
            if seg.statements[index].group != NO_STATEMENT &&
               seg.statements[index].stype != OpenGroup {
                seg.statements[index].group_end =
                    seg.statements[seg.statements[index].group as usize].group_end;
            }
        }

        seg.diagnostics = mem::replace(&mut self.diagnostics, Vec::new());
        seg.span_pool = mem::replace(&mut self.span_pool, Vec::new());
        seg.span_pool.shrink_to_fit();
        seg.statements.shrink_to_fit();
        collect_definitions(&mut seg);
        (seg, is_end)
    }
}

/// Extracts certain types of statement from the segment so that nameck doesn't
/// need statement-specific intelligence.
fn collect_definitions(seg: &mut Segment) {
    let buf: &[u8] = &seg.buffer;
    for (index, &ref stmt) in seg.statements.iter().enumerate() {
        let index = index as StatementIndex;
        if stmt.stype.takes_label() {
            seg.labels.push(LabelDef { index: index });
        }

        if stmt.group_end != NO_STATEMENT {
            if stmt.stype == Variable {
                let math = &seg.span_pool[stmt.math_start..stmt.proof_start];
                for sindex in 0..math.len() {
                    seg.local_vars.push(LocalVarDef {
                        index: index,
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            continue;
        }

        let math = &seg.span_pool[stmt.math_start..stmt.proof_start];

        match stmt.stype {
            Constant => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Constant,
                        start: index,
                        name: copy_token(span.as_ref(buf)),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Variable => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Variable,
                        start: index,
                        name: copy_token(span.as_ref(buf)),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Disjoint => {
                seg.global_dvs.push(GlobalDv {
                    start: index,
                    vars: math.iter().map(|sp| copy_token(sp.as_ref(buf))).collect(),
                });
            }
            Floating => {
                seg.floats.push(FloatDef {
                    start: index,
                    typecode: copy_token(math[0].as_ref(buf)),
                    label: copy_token(stmt.label.as_ref(buf)),
                    name: copy_token(math[1].as_ref(buf)),
                });
            }
            _ => {}
        }
    }
}

/// Metamath spec valid label characters are `[-._a-zA-Z0-9]`
fn is_valid_label(label: &[u8]) -> bool {
    label.iter().all(|&c| {
        c == b'.' || c == b'-' || c == b'_' || (c >= b'a' && c <= b'z') ||
        (c >= b'0' && c <= b'9') || (c >= b'A' && c <= b'Z')
    })
}

/// Slightly set.mm specific hack to extract a section name from a byte buffer.
///
/// This is run before parsing so it can't take advantage of comment extraction;
/// instead we look for the first indented line, within a heuristic limit of 500
/// bytes.
pub fn guess_buffer_name(buffer: &[u8]) -> &str {
    let buffer = &buffer[0..cmp::min(500, buffer.len())];
    let mut index = 0;
    while index < buffer.len() {
        // is this line indented?
        if buffer[index] == b' ' {
            break;
        }
        // skip this line
        while index < buffer.len() && buffer[index] != b'\n' {
            index += 1;
        }
        // skip the newline, too
        if index < buffer.len() {
            index += 1;
        }
    }
    // index points at the beginning of an indented line, or EOF

    // trim horizontal whitespace
    while index < buffer.len() && buffer[index] == b' ' {
        index += 1;
    }

    let mut eol = index;
    while eol < buffer.len() && buffer[eol] != b'\n' {
        eol += 1;
    }
    while eol > index && (buffer[eol - 1] == b'\r' || buffer[eol - 1] == b' ') {
        eol -= 1;
    }

    // fail gracefully, this is a debugging aid only
    if eol == index {
        "<no section name found>"
    } else {
        str::from_utf8(&buffer[index..eol]).unwrap_or("<invalid UTF-8 in section name>")
    }
}

/// This function implements parsing stage 1, which breaks down the metalanguage
/// grammar, finding all identifier definitions and inclusion statements.
///
/// There is an argument to be made that we shouldn't tokenize or store the math
/// strings and proofs at this stage, since they're bulky and can easily be
/// generated on demand.
///
/// The current Metamath spec defines comments and file inclusions at the token
/// level.  It is useful for our purposes to parse comments that are strictly
/// between statements as if they were statements (SMM2 did this too; may
/// revisit) and we require file inclusions to be between statements at the top
/// nesting level (this has been approved by Norman Megill).
pub fn parse_segments(input: &BufferRef) -> Vec<Arc<Segment>> {
    let mut closed_spans = Vec::new();
    let mut scanner = Scanner {
        buffer_ref: input.clone(),
        buffer: input,
        ..Scanner::default()
    };
    assert!(input.len() < FilePos::max_value() as usize);

    loop {
        let (seg, last) = scanner.get_segment();
        // we can almost use seg.next_file == Span::null here, but for the error
        // case
        closed_spans.push(Arc::new(seg));
        if last {
            return closed_spans;
        }
    }
}

/// Creates a new empty segment as a container for an I/O error.
///
/// Every error must be associated with a statement in our design, so associate
/// it with the EOF statement of a zero-length segment.
pub fn dummy_segment(diag: Diagnostic) -> Arc<Segment> {
    let mut seg = parse_segments(&Arc::new(Vec::new())).pop().unwrap();
    Arc::get_mut(&mut seg).unwrap().diagnostics.push((0, diag));
    seg
}
