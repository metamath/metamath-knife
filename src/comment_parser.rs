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
use crate::parser::Span;

/// A comment markup item, which represents either a piece of text from the input
/// or some kind of metadata item like the start or end of an italicized group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentItem {
    /// A piece of regular text. The characters in the buffer at the given
    /// span should be interpreted literally, except for the escapes.
    /// Use `unescape_text` to strip the text escapes.
    Text(Span),
    /// A paragraph break, caused by two or more consecutive newlines in the input.
    /// This is a zero-length item (all characters will be present in `Text` nodes
    /// before and after the element), but corresponds roughly to a `<p>` tag in HTML.
    LineBreak(usize),
    /// Start math mode, indicated by a backtick character. The usize points to the character.
    /// Between [`StartMathMode`] and [`EndMathMode`],
    /// there will be no comment items other than [`MathToken`].
    StartMathMode(usize),
    /// End math mode, indicated by a backtick character. The usize points to the character.
    /// Between [`StartMathMode`] and [`EndMathMode`],
    /// there will be no comment items other than [`MathToken`].
    EndMathMode(usize),
    /// A single math token. Beware that [`Escaped`] can split a math token,
    /// so this may not correspond to a `$c` or `$v` token directly.
    /// Use `unescape_math` to strip the escapes.
    MathToken(Span),
    /// A label of an existing theorem. The `usize` points to the `~` character.
    /// Use `unescape_text` to strip the text escapes.
    Label(usize, Span),
    /// A link to a web site URL. The `usize` points to the `~` character.
    /// Use `unescape_text` to strip the text escapes.
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

impl CommentItem {
    /// Remove text escapes from a markup segment `buf`, generally coming from the
    /// [`CommentItem::Text`], [`CommentItem::Label`], or [`CommentItem::Url`] fields.
    pub fn unescape_text(mut buf: &[u8], out: &mut Vec<u8>) {
        while let Some(n) = buf.iter().position(|&c| matches!(c, b'`' | b'[' | b'~')) {
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

    /// Remove math escapes from a markup segment `buf`, generally coming from the
    /// [`CommentItem::MathToken`] field.
    pub fn unescape_math(mut buf: &[u8], out: &mut Vec<u8>) {
        while let Some(n) = buf.iter().position(|&c| c == b'`') {
            out.extend_from_slice(&buf[..=n]);
            if buf.get(n + 1) == Some(&buf[n]) {
                buf = &buf[n + 2..];
            } else {
                // This should never happen if we are given `MathToken` text
                buf = &buf[n + 1..];
            }
        }
        out.extend_from_slice(buf);
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
    /// [`CommentItem::Text`], [`CommentItem::Label`], or [`CommentItem::Url`] fields.
    pub fn unescape_text(&self, span: Span, out: &mut Vec<u8>) {
        CommentItem::unescape_text(span.as_ref(self.buf), out)
    }

    /// Remove math escapes from a markup segment `span`, generally coming from the
    /// [`CommentItem::MathToken`] field.
    pub fn unescape_math(&self, span: Span, out: &mut Vec<u8>) {
        CommentItem::unescape_math(span.as_ref(self.buf), out)
    }

    fn parse_bib(&self) -> Option<Span> {
        let start = self.pos + 1;
        let mut end = start;
        loop {
            if let Some(&c) = self.buf.get(end) {
                if c == b']' {
                    return Some(Span::new(start, end));
                }
                if !c.is_ascii_whitespace() {
                    end += 1;
                    continue;
                }
            }
            return None;
        }
    }

    fn is_subscript(&self) -> Option<()> {
        const OPENING_PUNCTUATION: &[u8] = b"(['\"";
        if self.pos == self.end_subscript {
            return None;
        }
        let c = self.buf.get(self.pos.checked_sub(1)?)?;
        if c.is_ascii_whitespace() || OPENING_PUNCTUATION.contains(c) {
            return None;
        }
        Some(())
    }

    fn parse_subscript(&self) -> Option<usize> {
        const CLOSING_PUNCTUATION: &[u8] = b".,;)?!:]'\"_-";
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
        let end = (self.pos + 2) + self.buf[self.pos + 2..].iter().position(|&c| c == b'_')?;
        if !self.buf[end - 1].is_ascii_alphanumeric()
            || matches!(self.buf.get(end + 1), Some(c) if c.is_ascii_alphanumeric())
        {
            return None;
        }
        Some(end)
    }

    fn parse_underscore(&mut self) -> Option<(usize, CommentItem)> {
        let start = self.pos;
        let item = if self.is_subscript().is_some() {
            let sub_end = self.parse_subscript()?;
            self.pos += 1;
            self.end_subscript = sub_end;
            CommentItem::StartSubscript(start)
        } else {
            let it_end = self.parse_italic()?;
            self.pos += 1;
            self.end_italic = it_end;
            CommentItem::StartItalic(start)
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

    fn parse_math_delim(&mut self, at: usize) -> CommentItem {
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
            .then(|| ())
    }

    fn parse_label(&mut self) -> CommentItem {
        let tilde = self.pos;
        self.pos += 1;
        while matches!(self.buf.get(self.pos), Some(c) if c.is_ascii_whitespace()) {
            self.pos += 1;
        }
        let label_start = self.pos;
        while matches!(self.buf.get(self.pos), Some(c) if !c.is_ascii_whitespace()) {
            self.pos += 1;
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
}

impl<'a> Iterator for CommentParser<'a> {
    type Item = CommentItem;

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
                    self.item = Some(self.parse_label());
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
                if self.end_italic == self.pos {
                    end = self.pos;
                    self.pos += 1;
                    self.item = Some(CommentItem::EndItalic(end));
                    break;
                }
                if let Some((pos, item)) = self.parse_underscore() {
                    end = pos;
                    self.item = Some(item);
                    break;
                }
                self.pos += 1;
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
