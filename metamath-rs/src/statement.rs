//! The `Statement` data structure and related API.
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

use std::{borrow::Cow, ops::Deref};

use crate::{
    comment_parser::{CommentParser, Discouragements, ParentheticalIter},
    parser::{HeadingComment, HeadingLevel},
    segment::SegmentRef,
};

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
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct Span {
    /// Index of first character of the range.
    pub start: FilePos,
    /// Index one past last character of the range.
    pub end: FilePos,
}

impl Span {
    /// Coercion from array index pairs.
    #[inline]
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Span {
        Span {
            start: start as FilePos,
            end: end as FilePos,
        }
    }

    /// Variant on `new` taking [`FilePos`] values.
    #[inline]
    #[must_use]
    pub const fn new2(start: FilePos, end: FilePos) -> Span {
        Span { start, end }
    }

    /// Returns the null span.
    pub const NULL: Span = Span::new(0, 0);

    /// Checks for the null span, i.e. zero length at offset zero.
    #[inline]
    #[must_use]
    pub const fn is_null(self) -> bool {
        self.end == 0
    }

    /// Get the length of the span.
    #[inline]
    #[must_use]
    pub const fn len(self) -> usize {
        self.end as usize - self.start as usize
    }

    /// Is this an empty span?
    #[inline]
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Given a position span, extract the corresponding characters from a
    /// buffer.
    #[inline]
    #[must_use]
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
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct SegmentId(pub u32);

/// Semantic type for the index of a token in a statement.
///
/// Each token consumes at least two characters, plus a three-byte keyword and
/// space to introduce the math string at the beginning of the file, so this
/// cannot overflow for files of valid length.
pub type TokenIndex = i32;

/// A statement is located by giving its segment and index within the segment.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct StatementAddress {
    /// Segment which contains the statement.
    pub(crate) segment_id: SegmentId,
    /// Zero-based index of the statement.
    pub(crate) index: StatementIndex,
}

impl StatementAddress {
    /// Constructs a statement address from its parts.
    #[inline]
    #[must_use]
    pub const fn new(segment_id: SegmentId, index: StatementIndex) -> Self {
        StatementAddress { segment_id, index }
    }

    /// Convert a statement address into a statement range from here to the
    /// logical end of the database.
    #[inline]
    #[must_use]
    pub const fn unbounded_range(self) -> GlobalRange {
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
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct TokenAddress {
    /// Address of the statement in which the token is defined.
    pub statement: StatementAddress,
    /// Index of the token within the defining statement's math string.
    pub token_index: TokenIndex,
}

impl TokenAddress {
    /// Constructs a token address from parts.
    #[inline]
    #[must_use]
    pub const fn new3(segment_id: SegmentId, index: StatementIndex, token: TokenIndex) -> Self {
        TokenAddress {
            statement: StatementAddress::new(segment_id, index),
            token_index: token,
        }
    }
}

/// Expresses a valid range for a statement or token.
#[derive(Copy, Clone, Debug, Default)]
pub struct GlobalRange {
    /// The starting position of the range, which is also the definition site.
    pub start: StatementAddress,
    /// The exclusive endpoint of the range.
    ///
    /// Since scope braces are not allowed to span segments, if a range ends at
    /// all it must be in the same segment where it started, so this can be a
    /// bare `StatementIndex`.  If the range extends to the logical end of the
    /// database, that is represented with the `NO_STATEMENT` constant.
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

/// Transmutes this token into a Rust string.
#[must_use]
pub fn as_str(ptr: TokenPtr<'_>) -> &str {
    std::str::from_utf8(ptr).expect("TokenPtr is supposed to be UTF8")
}

/// Locate a span uniquely in the database by appending a segment ID.
pub type GlobalSpan = (SegmentId, Span);

/// Extracted data for a top-level `$d` statement in a segment.
#[derive(Debug)]
pub struct GlobalDv {
    /// The location of the statement.
    pub start: StatementIndex,
    /// The variables used in the statement.
    pub vars: Vec<Token>,
}

/// Types of math symbols in declarations.
#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
pub enum SymbolType {
    /// `$v`
    Variable,
    /// `$c`
    Constant,
}

/// Extracted information for a statement label in a segment.
#[derive(Copy, Clone, Debug)]
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
#[derive(Copy, Clone, Debug)]
pub struct LocalVarDef {
    /// Local index of the variable-declaring statement.
    pub index: StatementIndex,
    /// Index of variable within the statement.
    pub ordinal: TokenIndex,
}

/// Extracted information for outline heading statements.
#[derive(Debug)]
pub struct HeadingDef {
    /// The name of the heading (this is not strictly speaking a token)
    pub name: Token,
    /// Local inder of the heading statement.
    pub index: StatementIndex,
    /// Level of this outline
    pub level: HeadingLevel,
}

#[inline]
pub(crate) fn unescape(
    mut buf: &[u8],
    out: &mut Vec<u8>,
    is_escape: impl FnOnce(u8) -> bool + Copy,
) {
    while let Some(n) = buf.iter().position(|&c| is_escape(c)) {
        out.extend_from_slice(&buf[..=n]);
        if buf.get(n + 1) == Some(&buf[n]) {
            buf = &buf[n + 2..];
        } else {
            // this will not normally happen, but in some cases unescaped escapes
            // are left uninterpreted because they appear in invalid position,
            // and in that case they should be left as is
            buf = &buf[n + 1..];
        }
    }
    out.extend_from_slice(buf);
}

/// An individual symbol in a command, either a string or other keyword.
#[derive(Clone, Copy, Debug)]
pub enum CommandToken {
    /// A keyword (an identifier or symbol not surrounded in quotes)
    Keyword(Span),
    /// A string surrounded by `'` or `"` quotes
    String(Span),
}

impl CommandToken {
    /// Get the string corresponding to this token.
    #[must_use]
    pub fn value(self, buf: &[u8]) -> Cow<'_, [u8]> {
        match self {
            Self::Keyword(s) => Cow::Borrowed(s.as_ref(buf)),
            Self::String(s) => Self::unescape_string(buf, s),
        }
    }

    /// Get the full span of the token, including exterior quotes.
    #[must_use]
    pub const fn full_span(self) -> Span {
        match self {
            Self::Keyword(s) => s,
            Self::String(s) => Span::new2(s.start - 1, s.end + 1),
        }
    }

    /// Remove doubled quote escapes from a [`CommandToken::String`]`(span)`.
    pub fn append_unescaped_string(buf: &[u8], span: Span, out: &mut Vec<u8>) {
        let quote = buf[(span.start - 1) as usize];
        unescape(span.as_ref(buf), out, |c| quote == c)
    }

    /// Remove doubled quote escapes from a [`CommandToken::String`]`(span)`.
    #[must_use]
    pub fn unescape_string(buf: &[u8], span: Span) -> Cow<'_, [u8]> {
        let quote = buf[(span.start - 1) as usize];
        let buf = span.as_ref(buf);
        if buf.contains(&quote) {
            let mut out = vec![];
            unescape(span.as_ref(buf), &mut out, |c| quote == c);
            out.into()
        } else {
            Cow::Borrowed(buf)
        }
    }
}

/// Extra information residing in a $j comment
pub type Command = (Span, Vec<CommandToken>);

/// An enumeration of statement types, most of which correspond to statements as
/// defined in the Metamath spec.
#[derive(Default, Copy, Clone, Debug, Eq, PartialEq)]
pub enum StatementType {
    /// Psuedo statement used only to record end-of-file whitespace.
    Eof,
    /// Statement which is damaged enough that there's no sense passing it to
    /// later stages.
    #[default]
    Invalid,
    /// Comments between statements are recorded as statements in their own
    /// right to facilitate handling of date comments and other metadata.
    Comment,
    /// A comment which starts with a `$t` token and must be interpreted
    /// specially by the HTML generator.
    TypesettingComment,
    /// A comment corresponding to the head of a chapter or section in the outline
    HeadingComment(HeadingLevel),
    /// A comment which starts with a `$j` token and must be interpreted
    /// specially by the grammar parser
    AdditionalInfoComment,
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

impl StatementType {
    /// Returns true if this statement is an `Axiom` (`$a`) or `Provable` (`$p`) statement.
    #[inline]
    #[must_use]
    pub const fn is_assertion(self) -> bool {
        matches!(self, Axiom | Provable)
    }

    /// Returns true if this statement has a label before the keyword: `$a $p $e $f`.
    #[inline]
    #[must_use]
    pub const fn takes_label(self) -> bool {
        matches!(self, Axiom | Provable | Essential | Floating)
    }

    /// Returns true if this statement is followed by math tokens: `$a $p $e $f $d $c $v`.
    #[inline]
    #[must_use]
    pub const fn takes_math(self) -> bool {
        matches!(
            self,
            Axiom | Provable | Essential | Floating | Disjoint | Constant | Variable
        )
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
#[derive(Copy, Clone, Debug)]
pub(crate) struct Statement {
    /// Statement type, either a spec-defined type or one of the pseudo-types.
    pub(crate) stype: StatementType,
    /// Total span of the statement, not including trailing whitespace or
    /// surrounding comments.
    pub(crate) span: Span,
    /// Span of the statement label.
    ///
    /// If the type does not require a label, this will be a length-zero span
    /// at the beginning of the keyword.
    pub(crate) label: Span,
    /// Start of the most deeply nested group for this statment, or
    /// `NO_STATEMENT`.
    pub(crate) group: StatementIndex,
    /// End of the most deeply nested group for this statment, or `NO_STATEMENT`.
    pub(crate) group_end: StatementIndex,
    /// Index into `span_pool` of the first math token.
    pub(crate) math_start: usize,
    /// Index into `span_pool` of the first proof token / after the last math
    /// token.
    pub(crate) proof_start: usize,
    /// Index into `span_pool` one after the last proof token.
    pub(crate) proof_end: usize,
}

pub(crate) const DUMMY_STATEMENT: Statement = Statement {
    stype: StatementType::Invalid,
    span: Span::NULL,
    label: Span::NULL,
    group: NO_STATEMENT,
    group_end: NO_STATEMENT,
    math_start: 0,
    proof_start: 0,
    proof_end: 0,
};

/// A reference to a statement which knows its address and can be used to fetch
/// statement information.
#[derive(Copy, Clone, Debug)]
pub struct StatementRef<'a> {
    pub(crate) segment: SegmentRef<'a>,
    pub(crate) statement: &'a Statement,
    pub(crate) index: StatementIndex,
}

impl<'a> StatementRef<'a> {
    /// Fetch the segment-local index of this statement.
    #[inline]
    #[must_use]
    pub const fn index(self) -> StatementIndex {
        self.index
    }

    /// Back up from a statement reference to a segment reference.
    #[inline]
    #[must_use]
    pub const fn segment(self) -> SegmentRef<'a> {
        self.segment
    }

    /// Gets the type of this statement.  May be a pseudo-type.
    #[inline]
    #[must_use]
    pub const fn statement_type(self) -> StatementType {
        self.statement.stype
    }

    /// Returns true if this statement is an `Axiom` (`$a`) or `Provable` (`$p`) statement.
    #[inline]
    #[must_use]
    pub const fn is_assertion(self) -> bool {
        self.statement.stype.is_assertion()
    }

    /// Obtain a globally-meaningful address for this statement.
    #[inline]
    #[must_use]
    pub const fn address(self) -> StatementAddress {
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
    #[inline]
    #[must_use]
    pub const fn scope_range(self) -> GlobalRange {
        GlobalRange {
            start: self.address(),
            end: self.statement.group_end,
        }
    }

    /// True if there is a `${ $}` group wrapping this statement.
    #[inline]
    #[must_use]
    pub const fn in_group(self) -> bool {
        self.statement.group_end != NO_STATEMENT
    }

    /// Obtain the span corresponding to the statment label.
    #[inline]
    #[must_use]
    pub const fn label_span(&self) -> Span {
        self.statement.label
    }

    /// Obtain the statment label.
    ///
    /// This will be non-null iff the type requires a label; missing labels for
    /// types which use them cause an immediate rewrite to `Invalid`.
    #[inline]
    #[must_use]
    pub fn label(&self) -> &'a [u8] {
        self.label_span().as_ref(&self.segment.segment.buffer)
    }

    /// An iterator for the symbols in a statement's math string.
    #[must_use]
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
    #[inline]
    #[must_use]
    pub const fn span_full(&self) -> Span {
        self.statement.span
    }

    /// The textual span of this statement within the segment's buffer.
    ///
    /// Does not include surrounding white space or comments, unlike `span_full()`.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> Span {
        Span::new2(self.statement.label.start, self.span_full().end)
    }

    /// Count of symbols in this statement's math string.
    #[inline]
    #[must_use]
    pub const fn math_len(&self) -> TokenIndex {
        (self.statement.proof_start - self.statement.math_start) as TokenIndex
    }

    /// Count of tokens in this statement's proof string.
    #[inline]
    #[must_use]
    pub const fn proof_len(&self) -> TokenIndex {
        (self.statement.proof_end - self.statement.proof_start) as TokenIndex
    }

    /// Given an index into this statement's math string, find a textual span
    /// into the segment buffer.
    #[inline]
    #[must_use]
    pub fn math_span(&self, ix: TokenIndex) -> Span {
        self.segment.span_pool[self.statement.math_start + ix as usize]
    }

    /// Given an index into this statement's proof string, find a textual span
    /// into the segment buffer.
    #[inline]
    #[must_use]
    pub fn proof_span(&self, ix: TokenIndex) -> Span {
        self.segment.span_pool[self.statement.proof_start + ix as usize]
    }

    /// Get the list of spans of tokens in the proof.
    #[inline]
    #[must_use]
    pub fn proof_spans(&self) -> &'a [Span] {
        &self.segment.segment.span_pool[self.statement.proof_start..self.statement.proof_end]
    }

    /// Returns an iterator over the statements referenced in the proof.
    #[must_use]
    pub fn use_iter(&self) -> UseIter<'a> {
        let spans = self.proof_spans();
        let mut iter = spans.iter();
        if spans.first().map(|sp| sp.as_ref(&self.segment.buffer)) == Some(b"(") {
            iter.next();
        }
        UseIter {
            iter,
            buf: &self.segment.segment.buffer,
        }
    }

    /// Given an index into this statement's math string, get a reference to the
    /// math token.
    #[must_use]
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
    #[inline]
    #[must_use]
    pub fn proof_slice_at(&self, ix: TokenIndex) -> TokenPtr<'a> {
        self.proof_span(ix).as_ref(&self.segment.segment.buffer)
    }

    /// Get the "documentation" comment immediately preceding a $a $p
    /// statement, if it exists.
    #[must_use]
    pub fn associated_comment(&self) -> Option<StatementRef<'a>> {
        if self.index == 0 {
            return None;
        }
        let sref = self.segment.statement(self.index - 1);
        if sref.statement_type() == Comment {
            Some(sref)
        } else {
            None
        }
    }

    /// The contents of a comment statement, excluding the `$(` and `$)` delimiters.
    #[must_use]
    pub const fn comment_contents(&self) -> Span {
        Span::new2(self.statement.label.start + 2, self.span_full().end - 2)
    }

    /// Get an iterator over the markup items in this comment.
    #[must_use]
    pub fn comment_parser(&self) -> CommentParser<'a> {
        CommentParser::new(&self.segment.segment.buffer, self.comment_contents())
    }

    /// Parse the associated commment to get the discouragements
    /// (Proof modification / new usage discouraged) for this theorem.
    pub fn discouragements(&self) -> Discouragements {
        self.associated_comment()
            .map_or_else(Discouragements::default, |c| {
                Discouragements::new(c.comment_contents().as_ref(&self.segment.buffer))
            })
    }

    /// Return an iterator over the parentheticals (like `(Contributed by ...)`)
    /// in this comment statement.
    #[must_use]
    pub fn parentheticals(&self) -> ParentheticalIter<'a> {
        ParentheticalIter::new(&self.segment.segment.buffer, self.comment_contents())
    }

    /// Returns a `HeadingComment` object for a heading comment (if it is actually a heading).
    #[must_use]
    pub fn as_heading_comment(&self) -> Option<HeadingComment> {
        let StatementType::HeadingComment(lvl) = self.statement_type() else {
            return None;
        };
        HeadingComment::parse(&self.segment.buffer, lvl, self.comment_contents())
    }
}

/// An iterator over the statements in a segment.
///
/// This iterator knows the segment's global ID and can thus return proper
/// `StatementRef`s.
#[derive(Clone, Debug)]
pub struct StatementIter<'a> {
    pub(crate) slice_iter: std::slice::Iter<'a, Statement>,
    pub(crate) segment: SegmentRef<'a>,
    pub(crate) index: StatementIndex,
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
                index,
            }
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl DoubleEndedIterator for StatementIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.slice_iter.next_back().map(|st_ref| StatementRef {
            segment: self.segment,
            statement: st_ref,
            index: self.index + self.slice_iter.len() as StatementIndex,
        })
    }
}

impl ExactSizeIterator for StatementIter<'_> {
    fn len(&self) -> usize {
        self.slice_iter.len()
    }
}

/// An iterator over symbols in the math string of a statement.
#[derive(Clone, Debug)]
pub struct TokenIter<'a> {
    slice_iter: std::slice::Iter<'a, Span>,
    buffer: &'a [u8],
    stmt_address: StatementAddress,
    index: TokenIndex,
}

/// A reference to a token within a math string that knows its address.
///
/// Primarily used for iteration.
#[derive(Copy, Clone, Debug)]
pub struct TokenRef<'a> {
    /// Textual content of the token.
    pub slice: TokenPtr<'a>,
    /// 3-component address of the token.
    pub address: TokenAddress,
}

impl Deref for TokenRef<'_> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        self.slice
    }
}

impl TokenRef<'_> {
    /// Get the local index of the token within the statement under iteration.
    #[must_use]
    pub const fn index(self) -> TokenIndex {
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

/// An iterator over the statements referenced in a proof.
/// (Supports normal and compressed proofs; for packed/explicit proofs the
/// returned tokens must be parsed to remove the extra fields.)
#[derive(Debug, Clone)]
pub struct UseIter<'a> {
    buf: &'a [u8],
    iter: std::slice::Iter<'a, Span>,
}

impl<'a> Iterator for UseIter<'a> {
    type Item = (Span, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let sp = *self.iter.next()?;
        let tk = sp.as_ref(self.buf);
        if tk == b")" {
            return None;
        }
        Some((sp, tk))
    }
}
