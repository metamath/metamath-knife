//! Implements markup parsing for metamath theorem comments.
//!
//! The [set.mm](https://github.com/metamath/set.mm/) library contains many
//! theorems with comments, and those comments contain markup in a special syntax
//! implemented by [metamath.exe](https://github.com/metamath/metamath-exe),
//! and specified in Section 4.4.1 of the
//! [metamath book](http://us.metamath.org/downloads/metamath.pdf).
//! This module implements a SAX-style parser which yields events about the
//! beginning and end of each syntax event.
//!
//! The [`CommentItem`] type does not contain any byte buffers directly;
//! instead everything uses spans relative to the segment in which this comment
//! appeared. Note that for many of the [`Span`]-containing fields the
//! corresponding byte string in the file has to be unescaped before
//! interpretation, using the [`CommentParser::unescape_text`] and
//! [`CommentParser::unescape_math`] functions.
use std::{fmt::Display, sync::OnceLock};

use regex::bytes::{CaptureMatches, Match, Regex, RegexSet};

use crate::{statement::unescape, Span};

/// A comment markup item, which represents either a piece of text from the input
/// or some kind of metadata item like the start or end of an italicized group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentItem {
    /// A piece of regular text. The characters in the buffer at the given
    /// span should be interpreted literally, except for the escapes.
    /// Use `unescape_text` to strip the text escapes `[`, `~`, `` ` ``, and `_`.
    /// Note that `[` and `_` can also appear unescaped.
    Text(Span),
    /// A paragraph break, caused by two or more consecutive newlines in the input.
    /// This is a zero-length item (all characters will be present in `Text` nodes
    /// before and after the element), but corresponds roughly to a `<p>` tag in HTML.
    LineBreak(usize),
    /// Start math mode, indicated by a backtick character. The usize points to the character.
    /// Between [`CommentItem::StartMathMode`] and [`CommentItem::EndMathMode`],
    /// there will be no comment items other than [`CommentItem::MathToken`].
    StartMathMode(usize),
    /// End math mode, indicated by a backtick character. The usize points to the character.
    /// Between [`CommentItem::StartMathMode`] and [`CommentItem::EndMathMode`],
    /// there will be no comment items other than [`CommentItem::MathToken`].
    EndMathMode(usize),
    /// A single math token. After unescaping this should correspond to a `$c` or `$v` statement
    /// in the database.
    /// Use `unescape_math` to strip the escape character `` ` ``.
    MathToken(Span),
    /// A label of an existing theorem. The `usize` points to the `~` character.
    /// Use `unescape_text` to strip the text escapes `[`, `~`, `` ` ``, and `_`.
    /// Note that `[`, `~`, `_` can also appear unescaped.
    Label(usize, Span),
    /// A link to a web site URL. The `usize` points to the `~` character.
    /// Use `unescape_text` to strip the text escapes `[`, `~`, `` ` ``, and `_`.
    /// Note that `[`, `~`, `_` can also appear unescaped.
    Url(usize, Span),
    /// The `<HTML>` keyword, which starts HTML mode
    /// (it doesn't actually put `<HTML>` in the output).
    /// In HTML mode subscripts and italics are disabled, and HTML markup is interpreted.
    StartHtml(usize),
    /// The `</HTML>` keyword, which ends HTML mode
    /// (it doesn't actually put `</HTML>` in the output).
    EndHtml(usize),
    /// The start of a subscript `x_0`. The `usize` points at the `_` character.
    StartSubscript(usize),
    /// The end of a subscript like `x_0`. The `usize` points just after the end of the word.
    EndSubscript(usize),
    /// The start of an italic section `_italic text_`. The `usize` points at the `_` character.
    StartItalic(usize),
    /// The end of an italic section `_italic text_`. The `usize` points at the `_` character.
    EndItalic(usize),
    /// A bibliographic label `[foo]`. No escapes are needed inside the tag body.
    BibTag(Span),
}

/// Returns true if this is a character that is escaped in [`CommentItem::Text`] fields,
/// meaning that doubled occurrences are turned into single occurrences.
#[inline]
#[must_use]
pub const fn is_text_escape(html_mode: bool, c: u8) -> bool {
    matches!(c, b'`' | b'[' | b'~') || !html_mode && c == b'_'
}

/// Returns true if this is a character that is escaped in
/// [`CommentItem::Label`] and [`CommentItem::Url`] fields,
/// meaning that doubled occurrences are turned into single occurrences.
#[inline]
#[must_use]
pub const fn is_label_escape(c: u8) -> bool {
    matches!(c, b'`' | b'[' | b'~')
}

/// Returns true if this is a character that is escaped in [`CommentItem::MathToken`] fields,
/// meaning that doubled occurrences are turned into single occurrences.
#[inline]
#[must_use]
pub const fn is_math_escape(c: u8) -> bool {
    c == b'`'
}

impl CommentItem {
    /// Remove text escapes from a markup segment `buf`, generally coming from the
    /// [`CommentItem::Text`] field.
    pub fn unescape_text(html_mode: bool, buf: &[u8], out: &mut Vec<u8>) {
        unescape(buf, out, |c| is_text_escape(html_mode, c))
    }

    /// Remove text escapes from a markup segment `buf`, generally coming from the
    /// [`CommentItem::Label`] or [`CommentItem::Url`] fields.
    pub fn unescape_label(buf: &[u8], out: &mut Vec<u8>) {
        unescape(buf, out, is_label_escape)
    }

    /// Remove math escapes from a markup segment `buf`, generally coming from the
    /// [`CommentItem::MathToken`] field.
    pub fn unescape_math(buf: &[u8], out: &mut Vec<u8>) {
        unescape(buf, out, is_math_escape)
    }

    const fn token(math: bool, span: Span) -> Self {
        if math {
            Self::MathToken(span)
        } else {
            Self::Text(span)
        }
    }
}

/// An iterator over a metamath text comment, yielding markup items.
#[derive(Debug, Clone)]
pub struct CommentParser<'a> {
    buf: &'a [u8],
    pos: usize,
    math_mode: bool,
    html_mode: bool,
    item: Option<CommentItem>,
    end_italic: usize,
    end_subscript: usize,
}

const CLOSING_PUNCTUATION: &[u8] = b".,;)?!:]'\"_-";

impl<'a> CommentParser<'a> {
    /// Construct a new `CommentParser` from a sub-span of a buffer.
    /// The returned comment items will have spans based on the input span,
    /// and the portion of the buffer outside `buf[span.start..span.end]` will be ignored.
    #[must_use]
    pub fn new(buf: &'a [u8], span: Span) -> Self {
        Self {
            buf: &buf[..span.end as usize],
            pos: span.start as _,
            math_mode: false,
            html_mode: false,
            item: None,
            end_italic: usize::MAX,
            end_subscript: 0,
        }
    }

    /// Remove text escapes from a markup segment `span`, generally coming from the
    /// [`CommentItem::Text`] field.
    pub fn unescape_text(&self, span: Span, out: &mut Vec<u8>) {
        CommentItem::unescape_text(self.html_mode, span.as_ref(self.buf), out)
    }

    /// Remove text escapes from a markup segment `span`, generally coming from the
    /// [`CommentItem::Label`] or [`CommentItem::Url`] fields.
    pub fn unescape_label(&self, span: Span, out: &mut Vec<u8>) {
        CommentItem::unescape_label(span.as_ref(self.buf), out)
    }

    /// Remove math escapes from a markup segment `span`, generally coming from the
    /// [`CommentItem::MathToken`] field.
    pub fn unescape_math(&self, span: Span, out: &mut Vec<u8>) {
        CommentItem::unescape_math(span.as_ref(self.buf), out)
    }

    fn parse_bib(&self) -> Option<Span> {
        let start = self.pos + 1;
        let mut end = start;
        while let Some(&c) = self.buf.get(end) {
            match c {
                b']' => return Some(Span::new(start, end)),
                b'`' if self.buf.get(end + 1) == Some(&c) => end += 2,
                b'`' => break,
                _ if c.is_ascii_whitespace() => break,
                _ => end += 1,
            }
        }
        None
    }

    fn parse_subscript(&self) -> Option<usize> {
        let c = self.buf.get(self.pos + 1)?;
        if c.is_ascii_whitespace() || CLOSING_PUNCTUATION.contains(c) {
            return None;
        }
        let start = self.pos + 1;
        let mut end = start;
        while let Some(c) = self.buf.get(end) {
            if c.is_ascii_whitespace() || CLOSING_PUNCTUATION.contains(c) {
                break;
            }
            end += 1;
        }
        Some(end)
    }

    fn parse_italic(&self) -> Option<usize> {
        if !self.buf.get(self.pos + 1)?.is_ascii_alphanumeric() {
            return None;
        }
        let mut end = self.pos + 2;
        loop {
            if *self.buf.get(end)? == b'_' {
                if self.buf.get(end + 1) == Some(&b'_') {
                    end += 2
                } else {
                    break;
                }
            } else {
                end += 1
            }
        }
        if !self.buf[end - 1].is_ascii_alphanumeric()
            || matches!(self.buf.get(end + 1), Some(c) if c.is_ascii_alphanumeric())
        {
            return None;
        }
        Some(end)
    }

    fn parse_underscore(&mut self) -> Option<(usize, CommentItem)> {
        const OPENING_PUNCTUATION: &[u8] = b"(['\"";
        let start = self.pos;
        let is_italic = self.pos == self.end_subscript
            || (self.pos.checked_sub(1).and_then(|pos| self.buf.get(pos)))
                .is_none_or(|c| c.is_ascii_whitespace() || OPENING_PUNCTUATION.contains(c));
        let item = if is_italic {
            let it_end = self.parse_italic()?;
            self.pos += 1;
            self.end_italic = it_end;
            CommentItem::StartItalic(start)
        } else {
            let sub_end = self.parse_subscript()?;
            self.pos += 1;
            self.end_subscript = sub_end;
            CommentItem::StartSubscript(start)
        };
        Some((start, item))
    }

    fn parse_html(&mut self) -> Option<(usize, CommentItem)> {
        if self.html_mode {
            if self.buf[self.pos..].starts_with(b"</HTML>") {
                self.html_mode = false;
                let start = self.pos;
                self.pos += 7;
                Some((start, CommentItem::EndHtml(start)))
            } else {
                None
            }
        } else if self.buf[self.pos..].starts_with(b"<HTML>") {
            self.html_mode = true;
            let start = self.pos;
            self.pos += 6;
            Some((start, CommentItem::StartHtml(start)))
        } else {
            None
        }
    }

    const fn parse_math_delim(&mut self, at: usize) -> CommentItem {
        if self.math_mode {
            self.math_mode = false;
            CommentItem::EndMathMode(at)
        } else {
            self.math_mode = true;
            CommentItem::StartMathMode(at)
        }
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.buf.get(self.pos), Some(c) if c.is_ascii_whitespace()) {
            self.pos += 1;
        }
    }

    fn parse_newline(&self, last_nl: Option<usize>) -> Option<()> {
        self.buf[last_nl? + 1..self.pos]
            .iter()
            .all(u8::is_ascii_whitespace)
            .then_some(())
    }

    fn parse_label(&mut self) -> CommentItem {
        let tilde = self.pos;
        self.pos += 1;
        while matches!(self.buf.get(self.pos), Some(c) if c.is_ascii_whitespace()) {
            self.pos += 1;
        }
        let label_start = self.pos;
        while let Some(&c) = self.buf.get(self.pos) {
            match c {
                b'[' | b'`' if self.buf.get(self.pos + 1) == Some(&c) => self.pos += 2,
                b' ' | b'\r' | b'\n' | b'`' => break,
                b'[' if self.parse_bib().is_some() => break,
                b'<' if self.buf[self.pos..].starts_with(b"<HTML>")
                    || self.buf[self.pos..].starts_with(b"</HTML>") =>
                {
                    break
                }
                _ => self.pos += 1,
            }
        }
        let label = &self.buf[label_start..self.pos];
        if label.starts_with(b"http://")
            || label.starts_with(b"https://")
            || label.starts_with(b"mm")
        {
            CommentItem::Url(tilde, Span::new(label_start, self.pos))
        } else {
            CommentItem::Label(tilde, Span::new(label_start, self.pos))
        }
    }

    fn trim_space_before_open(&self, lo: usize, pos: usize) -> bool {
        lo + 2 <= pos
            && self.buf[pos - 1] == b' '
            && (b"([".contains(&self.buf[pos - 2])
                || self.buf[pos - 2] == b'\"'
                    && pos
                        .checked_sub(3)
                        .and_then(|i| self.buf.get(i))
                        .is_none_or(u8::is_ascii_whitespace))
    }

    fn trim_space_after_close(&self) -> bool {
        self.buf.get(self.pos) == Some(&b' ')
            && self
                .buf
                .get(self.pos + 1)
                .is_some_and(|c| CLOSING_PUNCTUATION.contains(c))
    }
}

impl Iterator for CommentParser<'_> {
    type Item = CommentItem;

    #[allow(clippy::cognitive_complexity)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.item.take() {
            return Some(item);
        }
        let math_token = self.math_mode;
        if math_token {
            self.skip_whitespace()
        }
        let start = self.pos;
        let mut end = self.buf.len();
        let mut last_nl = None;
        while let Some(&c) = self.buf.get(self.pos) {
            if c == b'`' {
                if self.buf.get(self.pos + 1) == Some(&b'`') {
                    self.pos += 2;
                } else {
                    end = self.pos;
                    self.pos += 1;
                    self.item = Some(self.parse_math_delim(end));
                    if self.math_mode && self.trim_space_before_open(start, end) {
                        // trim a single space if we are opening math mode after opening punct
                        end -= 1;
                    } else if !self.math_mode && self.trim_space_after_close() {
                        // trim a single space if we are exiting math mode before closing punct
                        self.pos += 1;
                    }
                    break;
                }
            } else if math_token {
                if matches!(self.buf.get(self.pos), Some(c) if !c.is_ascii_whitespace()) {
                    self.pos += 1;
                } else if self.pos > start {
                    return Some(CommentItem::MathToken(Span::new(start, self.pos)));
                } else {
                    return None;
                }
            } else if c == b'<' {
                if let Some((start, item)) = self.parse_html() {
                    end = start;
                    self.item = Some(item);
                    break;
                }
                self.pos += 1;
            } else if c == b'~' {
                if self.buf.get(self.pos + 1) == Some(&b'~') {
                    self.pos += 2;
                } else {
                    end = self.pos;
                    if self.trim_space_before_open(start, end) {
                        // trim a single space if we have a label after opening punct
                        end -= 1;
                    }
                    self.item = Some(self.parse_label());
                    if self.trim_space_after_close() {
                        // trim a single space if we have a label before closing punct
                        self.pos += 1;
                    }
                    break;
                }
            } else if c == b'[' {
                if self.buf.get(self.pos + 1) == Some(&b'[') {
                    self.pos += 2;
                } else if let Some(span) = self.parse_bib() {
                    end = self.pos;
                    self.pos = span.end as usize + 1;
                    self.item = Some(CommentItem::BibTag(span));
                    break;
                } else {
                    self.pos += 1;
                }
            } else if self.html_mode {
                self.pos += 1;
            } else if c == b'\n' {
                if self.parse_newline(last_nl.replace(self.pos)).is_some() {
                    end = self.pos;
                    self.item = Some(CommentItem::LineBreak(end));
                    break;
                }
                self.pos += 1;
            } else if c == b'_' {
                if self.buf.get(self.pos + 1) == Some(&b'_') {
                    self.pos += 2;
                } else if self.end_italic == self.pos {
                    end = self.pos;
                    self.pos += 1;
                    self.item = Some(CommentItem::EndItalic(end));
                    break;
                } else if let Some((pos, item)) = self.parse_underscore() {
                    end = pos;
                    self.item = Some(item);
                    break;
                } else {
                    self.pos += 1;
                }
            } else {
                self.pos += 1;
            }
            if self.pos == self.end_subscript {
                end = self.pos;
                self.item = Some(CommentItem::EndSubscript(end));
                break;
            }
        }
        if end > start {
            return Some(CommentItem::token(math_token, Span::new(start, end)));
        }
        self.item.take()
    }
}

/// Discouragement information about a theorem.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct Discouragements {
    /// Is proof modification discouraged for this theorem?
    pub modification_discouraged: bool,
    /// Is new usage discouraged for this theorem?
    pub usage_discouraged: bool,
}

impl Discouragements {
    /// Parse the text of a statement's comment to determine whether proof usage or modification
    /// is discouraged.
    #[must_use]
    pub fn new(buf: &[u8]) -> Self {
        static MODIFICATION: OnceLock<RegexSet> = OnceLock::new();
        let modification = MODIFICATION.get_or_init(|| {
            RegexSet::new([
                r"\(Proof[ \r\n]+modification[ \r\n]+is[ \r\n]+discouraged\.\)",
                r"\(New[ \r\n]+usage[ \r\n]+is[ \r\n]+discouraged\.\)",
            ])
            .unwrap()
        });
        let m = modification.matches(buf);
        Self {
            modification_discouraged: m.matched(0),
            usage_discouraged: m.matched(1),
        }
    }
}

/// Information about "parentheticals" in the comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Parenthetical {
    /// A comment like `(Contributed by Foo Bar, 12-Mar-2020.)`.
    ContributedBy {
        /// The span of the author in the parenthetical
        author: Span,
        /// The date, in the form `DD-MMM-YYYY`.
        /// To parse this further into a date, use the [`Date`] type's [`TryFrom`] impl.
        date: Span,
    },
    /// A comment like `(Revised by Foo Bar, 12-Mar-2020.)`.
    RevisedBy {
        /// The span of the author in the parenthetical
        author: Span,
        /// The date, in the form `DD-MMM-YYYY`.
        /// To parse this further into a date, use the [`Date`] type's [`TryFrom`] impl.
        date: Span,
    },
    /// A comment like `(Proof shortened by Foo Bar, 12-Mar-2020.)`.
    ProofShortenedBy {
        /// The span of the author in the parenthetical
        author: Span,
        /// The date, in the form `DD-MMM-YYYY`.
        /// To parse this further into a date, use the [`Date`] type's [`TryFrom`] impl.
        date: Span,
    },
    /// The `(Proof modification is discouraged.)` comment
    ProofModificationDiscouraged,
    /// The `(New usage is discouraged.)` comment
    NewUsageDiscouraged,
}

/// An iterator over the parentheticals in a comment.
#[derive(Debug)]
pub struct ParentheticalIter<'a> {
    matches: CaptureMatches<'static, 'a>,
    off: u32,
}

impl<'a> ParentheticalIter<'a> {
    /// Construct a new parenthetical iterator given a segment buffer and a span in it.
    #[must_use]
    pub fn new(buf: &'a [u8], span: Span) -> Self {
        static PARENTHETICALS: OnceLock<Regex> = OnceLock::new();
        let parentheticals = PARENTHETICALS.get_or_init(|| {
            Regex::new(concat!(
                r"\((Contributed|Revised|Proof[ \r\n]+shortened)",
                r"[ \r\n]+by[ \r\n]+([^,)]+),[ \r\n]+([0-9]{1,2}-[A-Z][a-z]{2}-[0-9]{4})\.\)|",
                r"\((Proof[ \r\n]+modification|New[ \r\n]+usage)[ \r\n]+is[ \r\n]+discouraged\.\)",
            ))
            .unwrap()
        });
        Self {
            matches: parentheticals.captures_iter(span.as_ref(buf)),
            off: span.start,
        }
    }

    fn to_span(&self, m: Match<'_>) -> Span {
        Span {
            start: self.off + m.start() as u32,
            end: self.off + m.end() as u32,
        }
    }
}

impl Iterator for ParentheticalIter<'_> {
    type Item = (Span, Parenthetical);

    fn next(&mut self) -> Option<Self::Item> {
        let groups = self.matches.next()?;
        let all = groups.get(0).unwrap();
        let item = if let Some(m) = groups.get(1) {
            let author = self.to_span(groups.get(2).unwrap());
            let date = self.to_span(groups.get(3).unwrap());
            match m.as_bytes()[0] {
                b'C' => Parenthetical::ContributedBy { author, date },
                b'R' => Parenthetical::RevisedBy { author, date },
                b'P' => Parenthetical::ProofShortenedBy { author, date },
                _ => unreachable!(),
            }
        } else {
            match all.as_bytes()[1] {
                b'P' => Parenthetical::ProofModificationDiscouraged,
                b'N' => Parenthetical::NewUsageDiscouraged,
                _ => unreachable!(),
            }
        };
        Some((self.to_span(all), item))
    }
}

/// A date, as understood by metamath tools.
/// This is just a `dd-mmm-yyyy` field after parsing,
/// so it has weak calendrical restrictions.
#[derive(Debug, Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Date {
    /// A year, which must be a 4 digit number (0-9999).
    pub year: u16,
    /// A month, parsed from three letter names: `Jan`, `Feb`, etc. (1-12)
    pub month: u8,
    /// A day, parsed from a 1 or 2 digit number (0-99).
    pub day: u8,
}

impl Display for Date {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const MONTHS: [&str; 12] = [
            "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
        ];
        write!(
            f,
            "{day}-{month}-{year:04}",
            day = self.day,
            month = MONTHS[(self.month - 1) as usize],
            year = self.year
        )
    }
}

impl TryFrom<&[u8]> for Date {
    type Error = ();

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let (day, month, year) = match value.len() {
            10 => (&value[..1], &value[2..5], &value[6..]),
            11 => (&value[..2], &value[3..6], &value[7..]),
            _ => return Err(()),
        };
        Ok(Date {
            year: std::str::from_utf8(year)
                .map_err(|_| ())?
                .parse()
                .map_err(|_| ())?,
            month: match month {
                b"Jan" => 1,
                b"Feb" => 2,
                b"Mar" => 3,
                b"Apr" => 4,
                b"May" => 5,
                b"Jun" => 6,
                b"Jul" => 7,
                b"Aug" => 8,
                b"Sep" => 9,
                b"Oct" => 10,
                b"Nov" => 11,
                b"Dec" => 12,
                _ => return Err(()),
            },
            day: std::str::from_utf8(day)
                .map_err(|_| ())?
                .parse()
                .map_err(|_| ())?,
        })
    }
}
