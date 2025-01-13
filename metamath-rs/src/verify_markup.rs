//! Verification of comment markup and other niceties for HTML generation.
//!
//! This is a clone of metamath.exe's `VERIFY MARKUP` command, although the
//! implementation is somewhat more robust. The intention is to use these
//! checks for checking the main databases that appear on the Metamath website,
//! such as [set.mm](https://github.com/metamath/set.mm/). As such, they are
//! rather more opinionated than the usual checks (for example, labels should
//! not use underscores), and they also include a number of set.mm-specific
//! references, because this is what metamath.exe did. (Ideally, most or all of
//! these hardcoded references can be replaced by `$j` commands in the future.)

use crate::comment_parser::{
    is_label_escape, is_text_escape, CommentItem, CommentParser, Date, Parenthetical,
};
use crate::diag::{BibError, Diagnostic};
use crate::parser::{HeadingComment, HeadingLevel};
use crate::scopeck::Hyp;
use crate::segment::{Comparer, SegmentRef};
use crate::segment_set::SourceInfo;
use crate::statement::{StatementAddress, NO_STATEMENT};
use crate::util::{HashMap, HashSet};
use crate::{Database, Span, StatementRef, StatementType};
use html5ever::tendril::{stream::Utf8LossyDecoder, Tendril, TendrilSink as _};
use regex::bytes::Regex;
use std::ops::Range;
use std::sync::OnceLock;

fn windows_reserved_names() -> &'static Regex {
    static WINDOWS_RESERVED_NAMES: OnceLock<Regex> = OnceLock::new();
    WINDOWS_RESERVED_NAMES
        .get_or_init(|| Regex::new("(?i-u)^(?:CON|PRN|AUX|NUL|(?:COM|LPT)[1-9])$").unwrap())
}

impl Database {
    /// Run the verify markup pass on the database.
    /// Requires: [`Database::scope_pass`], [`Database::typesetting_pass`]
    #[allow(clippy::cognitive_complexity)]
    #[must_use]
    pub fn verify_markup(
        &self,
        bib2: Option<&Bibliography2>,
    ) -> Vec<(StatementAddress, Diagnostic)> {
        let mut diags = vec![];
        let tdata = &**self.typesetting_result();
        let order = &*self.parse_result().order;

        let ext_start = tdata.ext_html_label.as_ref().and_then(|(sp, tk)| {
            if let Some(stmt) = self.name_result().lookup_label(tk) {
                Some(stmt.address)
            } else {
                diags.push((
                    StatementAddress::new(sp.0, NO_STATEMENT),
                    Diagnostic::UnknownLabel(sp.1),
                ));
                None
            }
        });

        let mut bib = bib2.map(|bib| &bib.base);
        let mut mbox_start = None;
        let mut cur_mbox = None;
        let mut mbox_map = HashMap::default();
        for stmt in self.statements() {
            if stmt.label().contains(&b'_') {
                diags.push((
                    stmt.address(),
                    Diagnostic::LabelContainsUnderscore(stmt.label_span()),
                ))
            }
            if stmt.label().get(..2) == Some(b"mm") {
                diags.push((
                    stmt.address(),
                    Diagnostic::MMReservedLabel(stmt.label_span()),
                ))
            } else if windows_reserved_names().is_match(stmt.label()) {
                diags.push((
                    stmt.address(),
                    Diagnostic::WindowsReservedLabel(stmt.label_span()),
                ))
            } else if stmt.label() == b"mathbox" {
                bib = bib2.map(|bib| &bib.base);
                mbox_start = Some(stmt.address());
            }
            match stmt.statement_type() {
                StatementType::Axiom => {
                    if *stmt.math_at(0) == *b"|-"
                        && !matches!(stmt.label().get(..3), Some(b"ax-" | b"df-"))
                    {
                        diags.push((
                            stmt.address(),
                            Diagnostic::UnconventionalAxiomLabel(stmt.label_span()),
                        ))
                    }
                    if stmt.label().get(..3) == Some(b"ax-") {
                        let mut label = Vec::from(*b"ax");
                        label.extend_from_slice(&stmt.label()[3..]);
                        if let Some(stmt2) = self.statement(&label) {
                            if !eq_statement(self, stmt, stmt2) {
                                diags.push((
                                    stmt.address(),
                                    Diagnostic::InvalidAxiomRestatement(
                                        stmt.label_span(),
                                        stmt2.label_span(),
                                    ),
                                ))
                            }
                        }
                    }
                }
                StatementType::Constant | StatementType::Variable => {
                    let buf = &stmt.segment.segment.buffer;
                    for sp in (0..stmt.math_len()).map(|i| stmt.math_span(i)) {
                        let tk = sp.as_ref(buf);
                        if tk.contains(&b'@') {
                            diags.push((stmt.address(), Diagnostic::ReservedAtToken(sp)))
                        }
                        if tk.contains(&b'?') {
                            diags.push((stmt.address(), Diagnostic::ReservedQToken(sp)))
                        }
                        let html = !tdata.html_defs.contains_key(tk);
                        let alt_html = !tdata.alt_html_defs.contains_key(tk);
                        let latex = !tdata.latex_defs.contains_key(tk);
                        if html || alt_html || latex {
                            diags.push((
                                stmt.address(),
                                Diagnostic::MissingMarkupDef([html, alt_html, latex], sp),
                            ))
                        }
                    }
                }
                StatementType::HeadingComment(lvl) => {
                    let buf = &stmt.segment.segment.buffer;
                    if let Some(header) = HeadingComment::parse(buf, lvl, stmt.comment_contents()) {
                        if mbox_start.is_some() && lvl == HeadingLevel::Section {
                            let span = header.parse_mathbox_header(buf).unwrap_or_else(|| {
                                diags.push((
                                    stmt.address(),
                                    Diagnostic::MathboxHeaderFormat(header.header),
                                ));
                                Span::NULL
                            });
                            cur_mbox = Some((stmt.address(), span.as_ref(buf)));
                        }
                        verify_markup_comment(self, bib, buf, header.content, |diag| {
                            diags.push((stmt.address(), diag))
                        })
                    } else {
                        diags.push((stmt.address(), Diagnostic::HeaderCommentParseError(lvl)))
                    }
                }
                StatementType::Provable => {
                    if let (Some(mbox_start), Some(cur_mbox)) = (mbox_start, cur_mbox) {
                        for (sp, tk) in stmt.use_iter() {
                            if let Some(stmt2) = self.name_result().lookup_label(tk) {
                                let tgt = stmt2.address;
                                if order.le(&mbox_start, &tgt) && order.lt(&tgt, &cur_mbox.0) {
                                    diags.push((
                                        stmt.address(),
                                        Diagnostic::MathboxCrossReference(Box::new((
                                            sp,
                                            stmt.label_span(),
                                            self.statement_by_address(stmt2.address).label_span(),
                                            cur_mbox.1.into(),
                                            <&[_]>::into(mbox_map.get(&tgt).map_or(&[], |x| *x)),
                                        ))),
                                    ))
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            if stmt.is_assertion() {
                if let Some(mbox) = cur_mbox {
                    mbox_map.insert(stmt.address(), mbox.1);
                }
                if matches!(ext_start, Some(a) if a == stmt.address()) {
                    bib = bib2.and_then(|bib| bib.ext.as_ref());
                }
                let buf = &stmt.segment.segment.buffer;
                let mut contributor = None;
                let mut laters = vec![];
                let mut proof_mod = None;
                let mut new_usage_discouraged = false;
                let mut prev_date = None;
                if let Some(comment) = stmt.associated_comment() {
                    verify_markup_comment(self, bib, buf, comment.comment_contents(), |diag| {
                        diags.push((stmt.address(), diag))
                    });
                    for (sp, paren) in comment.parentheticals() {
                        let mut check_paren = |author: Span, date_sp: Span| {
                            if author.as_ref(buf) == b"?who?" {
                                diags.push((stmt.address(), Diagnostic::DefaultAuthor(author)))
                            }

                            if let Ok(date) = Date::try_from(date_sp.as_ref(buf)) {
                                if let Some((prev_sp, prev)) = prev_date.replace((date_sp, date)) {
                                    if prev > date {
                                        diags.push((
                                            stmt.address(),
                                            Diagnostic::DateOrderError(prev_sp, date_sp),
                                        ))
                                    }
                                }
                            } else {
                                diags.push((stmt.address(), Diagnostic::DateParseError(date_sp)))
                            }
                        };
                        match paren {
                            Parenthetical::ContributedBy { author, date } => {
                                check_paren(author, date);
                                if let Some(sp1) = contributor.replace(sp) {
                                    diags.push((
                                        stmt.address(),
                                        Diagnostic::DuplicateContributor(sp1, sp),
                                    ))
                                }
                            }
                            Parenthetical::RevisedBy { author, date }
                            | Parenthetical::ProofShortenedBy { author, date } => {
                                check_paren(author, date);
                                laters.push(sp)
                            }
                            Parenthetical::ProofModificationDiscouraged => proof_mod = Some(sp),
                            Parenthetical::NewUsageDiscouraged => new_usage_discouraged = true,
                        }
                    }
                }

                if let Some(first) = contributor {
                    for later in laters {
                        if first.start > later.start {
                            diags.push((stmt.address(), Diagnostic::ParenOrderError(first, later)))
                        }
                    }
                } else if stmt.statement_type() != StatementType::Axiom
                    || matches!(stmt.label().get(..3), Some(b"ax-" | b"df-"))
                {
                    diags.push((stmt.address(), Diagnostic::MissingContributor))
                }

                if stmt.statement_type() == StatementType::Axiom {
                    if let Some(proof_mod) = proof_mod {
                        diags.push((stmt.address(), Diagnostic::ProofModOnAxiom(proof_mod)))
                    }
                }

                if (stmt.label().ends_with(b"OLD") || stmt.label().ends_with(b"ALT"))
                    && (!new_usage_discouraged
                        || (stmt.statement_type() != StatementType::Axiom && proof_mod.is_none()))
                {
                    diags.push((stmt.address(), Diagnostic::OldAltNotDiscouraged))
                }
            }
        }

        for seg in self.parse_result().segments(..) {
            #[inline]
            fn eol_check(
                diags: &mut Vec<(StatementAddress, Diagnostic)>,
                seg: &SegmentRef<'_>,
                line_start: usize,
                i: usize,
            ) {
                const MAX_LINE_LENGTH: usize = 79;
                if i - line_start > MAX_LINE_LENGTH {
                    diags.push((
                        StatementAddress::new(seg.id, NO_STATEMENT),
                        Diagnostic::LineLengthExceeded(Span::new(line_start + MAX_LINE_LENGTH, i)),
                    ))
                }
                if i.checked_sub(1).and_then(|j| seg.buffer.get(j)) == Some(&b' ') {
                    let start = seg.buffer[..i]
                        .iter()
                        .rposition(|&c| c != b' ')
                        .map_or(0, |j| j + 1);
                    diags.push((
                        StatementAddress::new(seg.id, NO_STATEMENT),
                        Diagnostic::TrailingWhitespace(Span::new(start, i)),
                    ))
                }
            }
            let mut line_start = 0;
            let mut iter = seg.buffer.iter().enumerate();
            while let Some((i, &c)) = iter.next() {
                match c {
                    b'\n' => {
                        eol_check(&mut diags, &seg, line_start, i);
                        line_start = i + 1;
                    }
                    b'\r' => {
                        eol_check(&mut diags, &seg, line_start, i);
                        line_start = if seg.buffer.get(i + 1) == Some(&b'\n') {
                            iter.next();
                            i + 2
                        } else {
                            i + 1
                        }
                    }
                    b'\t' => {
                        let count = seg.buffer[i..].iter().take_while(|&&c| c == b'\t').count();
                        for _ in 1..count {
                            iter.next();
                        }
                        diags.push((
                            StatementAddress::new(seg.id, NO_STATEMENT),
                            Diagnostic::TabUsed(Span::new(i, i + count)),
                        ))
                    }
                    _ => {}
                }
            }
            eol_check(&mut diags, &seg, line_start, seg.buffer.len());
        }

        for map in [&tdata.html_defs, &tdata.alt_html_defs, &tdata.latex_defs] {
            for (tk, (sp, (seg_id, _), _)) in map {
                if self.name_result().lookup_symbol(tk).is_none() {
                    diags.push((
                        StatementAddress::new(*seg_id, NO_STATEMENT),
                        Diagnostic::UndefinedToken(*sp, tk.clone()),
                    ))
                }
            }
        }

        // omitted: check that files in IMG SRC="..." of html_defs exist
        // omitted: check that html_home has HREF="..." and IMG SRC="..."
        // omitted: check that ext_html_home has HREF="..." and IMG SRC="..."
        // omitted: top date check

        diags
    }
}

// TODO: use Iterator::eq_by, rust#64295
fn eq_by<T, U>(
    iter1: impl IntoIterator<Item = T>,
    iter2: impl IntoIterator<Item = U>,
    f: impl Fn(T, U) -> bool,
) -> bool {
    let mut iter1 = iter1.into_iter();
    let mut iter2 = iter2.into_iter();
    loop {
        match (iter1.next(), iter2.next()) {
            (None, None) => return true,
            (Some(a), Some(b)) => {
                if !f(a, b) {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

fn eq_statement(db: &Database, stmt1: StatementRef<'_>, stmt2: StatementRef<'_>) -> bool {
    let it1 = stmt1.math_iter().map(|tk| tk.slice);
    let it2 = stmt2.math_iter().map(|tk| tk.slice);
    it1.eq(it2) && {
        let fr1 = db.scope_result().get(stmt1.label()).unwrap();
        let fr2 = db.scope_result().get(stmt2.label()).unwrap();
        eq_by(
            fr1.mandatory_hyps(),
            fr2.mandatory_hyps(),
            |h1, h2| match (h1, h2) {
                (Hyp::Essential(_, e1), Hyp::Essential(_, e2)) => {
                    let eq_span = |s1: &Range<usize>, s2: &Range<usize>| {
                        fr1.const_pool[s1.clone()] == fr2.const_pool[s2.clone()]
                    };
                    e1.typecode == e2.typecode
                        && eq_by(&*e1.tail, &*e2.tail, |frag1, frag2| {
                            eq_span(&frag1.prefix, &frag2.prefix) && frag1.var == frag2.var
                        })
                        && eq_span(&e1.rump, &e2.rump)
                }
                (Hyp::Floating(_, i1, tc1), Hyp::Floating(_, i2, tc2)) => i1 == i2 && tc1 == tc2,
                _ => false,
            },
        ) && fr1.mandatory_dv == fr2.mandatory_dv
    }
}

fn verify_markup_comment(
    db: &Database,
    bib: Option<&Bibliography>,
    buf: &[u8],
    span: Span,
    mut diag: impl FnMut(Diagnostic),
) {
    fn ensure_space_before(buf: &[u8], i: usize, diag: &mut impl FnMut(Diagnostic)) {
        if i.checked_sub(1)
            .map(|j| buf[j])
            .is_some_and(|c| !c.is_ascii_whitespace())
        {
            diag(Diagnostic::MarkupNeedsWhitespace(i as u32))
        }
    }
    fn ensure_space_after(buf: &[u8], i: usize, diag: &mut impl FnMut(Diagnostic)) {
        if buf.get(i + 1).is_some_and(|c| !c.is_ascii_whitespace()) {
            diag(Diagnostic::MarkupNeedsWhitespace(i as u32))
        }
    }

    fn check_uninterpreted_escapes(
        buf: &[u8],
        sp: Span,
        escape: impl Fn(u8) -> bool,
        mut diag: impl FnMut(u8, Diagnostic),
    ) {
        let mut i = sp.start as usize;
        while i < sp.end as usize {
            let c = buf[i];
            if escape(c) {
                if buf.get(i + 1) == Some(&c) {
                    i += 1;
                } else {
                    diag(c, Diagnostic::UninterpretedEscape(i as u32))
                }
            }
            i += 1;
        }
    }

    fn check_uninterpreted_html(buf: &[u8], sp: Span, diag: &mut impl FnMut(Diagnostic)) {
        static HTML: OnceLock<Regex> = OnceLock::new();
        let html = HTML.get_or_init(|| Regex::new("(?i-u)</?HTML>").unwrap());
        let text = sp.as_ref(buf);
        if html.is_match(text) {
            if let Some(m) = html.find(text) {
                diag(Diagnostic::UninterpretedHtml(Span::new2(
                    sp.start + m.start() as u32,
                    sp.start + m.end() as u32,
                )))
            }
        }
    }

    let mut temp_buffer = vec![];
    let mut in_math = None;
    let mut in_html = None::<HtmlParser>;
    for item in CommentParser::new(buf, span) {
        match item {
            CommentItem::Text(sp) => {
                let escape = |c| is_text_escape(in_html.is_some(), c);
                check_uninterpreted_escapes(buf, sp, escape, |c, d| {
                    // Don't report on unescaped [ in regular text
                    if c != b'[' {
                        diag(d)
                    }
                });
                check_uninterpreted_html(buf, sp, &mut diag);
                if let Some(parser) = &mut in_html {
                    parser.feed(sp.as_ref(buf))
                }
            }
            CommentItem::StartMathMode(i) => {
                in_math = Some(i);
                ensure_space_after(buf, i, &mut diag)
            }
            CommentItem::EndMathMode(i) => {
                in_math = None;
                ensure_space_before(buf, i, &mut diag)
            }
            CommentItem::MathToken(sp) => {
                temp_buffer.clear();
                CommentItem::unescape_math(sp.as_ref(buf), &mut temp_buffer);
                if db.name_result().lookup_symbol(&temp_buffer).is_none() {
                    diag(Diagnostic::UndefinedToken(sp, (&*temp_buffer).into()))
                }
            }
            CommentItem::Label(i, sp) | CommentItem::Url(i, sp) => {
                ensure_space_before(buf, i, &mut diag);
                ensure_space_after(buf, i, &mut diag);
                check_uninterpreted_escapes(buf, sp, is_label_escape, |_, d| diag(d));
                check_uninterpreted_html(buf, sp, &mut diag);
                if matches!(item, CommentItem::Label(..)) {
                    temp_buffer.clear();
                    CommentItem::unescape_label(sp.as_ref(buf), &mut temp_buffer);
                    if temp_buffer.is_empty() {
                        diag(Diagnostic::EmptyLabel(i as u32))
                    } else if db.name_result().lookup_label(&temp_buffer).is_none() {
                        diag(Diagnostic::UnknownLabel(sp))
                    }
                }
            }
            CommentItem::StartHtml(i) => in_html = Some(HtmlParser::new(i)),
            CommentItem::EndHtml(i) => in_html.take().unwrap().validate(i + 7, &mut diag),
            CommentItem::LineBreak(_)
            | CommentItem::StartSubscript(_)
            | CommentItem::EndSubscript(_)
            | CommentItem::StartItalic(_)
            | CommentItem::EndItalic(_) => {}
            CommentItem::BibTag(sp) => {
                // Escapes in this position don't work properly in metamath.exe,
                // so warn on any use, not just unescaped
                for i in sp.start as usize..sp.end as usize {
                    if matches!(buf[i], b'`' | b'~') {
                        diag(Diagnostic::BibEscape(i as u32, sp))
                    }
                }
                if let Some(bib) = bib {
                    if !bib.contains(sp.as_ref(buf)) {
                        diag(Diagnostic::UndefinedBibTag(sp))
                    }
                }
            }
        }
    }
    if let Some(i) = in_math {
        diag(Diagnostic::UnclosedMathMarkup(i as u32, span.end))
    }
    if let Some(parser) = in_html {
        diag(Diagnostic::UnclosedHtml(parser.start as u32, span.end))
    }
}

/// A parsed bibliography file.
///
/// A bibliography file is nothing more than an HTML
/// file with some anchors (`<A NAME="foo">`) in it; the anchor names are
/// scraped so that we can cross reference them against bibliography tags
/// `[foo]` appearing in comments.
#[derive(Debug)]
pub struct Bibliography(HashSet<Box<[u8]>>);

/// A pair of bibliography files.
///
/// This is used to support `set.mm`, which
/// contains two separate-ish databases inside one metamath file. Bibliography
/// references in the first part of the file refer to the
/// [`html_bibliography`][crate::typesetting::TypesettingData::html_bibliography],
/// while references after the [`ext_html_label`][crate::typesetting::TypesettingData::ext_html_label] go to the
/// [`ext_html_bibliography`][crate::typesetting::TypesettingData::ext_html_bibliography].
#[derive(Debug)]
pub struct Bibliography2 {
    /// The main bibliography file.
    pub base: Bibliography,
    /// The "extended" bibliography file.
    pub ext: Option<Bibliography>,
}

impl From<Bibliography> for Bibliography2 {
    fn from(base: Bibliography) -> Self {
        Self { base, ext: None }
    }
}

impl Bibliography {
    /// Parse bibliography file data out of the given [`SourceInfo`], and put
    /// any parse errors in `diags`.
    pub fn parse<'a>(source: &'a SourceInfo, diags: &mut Vec<(&'a SourceInfo, BibError)>) -> Self {
        static A_NAME: OnceLock<Regex> = OnceLock::new();
        let a_name = A_NAME.get_or_init(|| {
            #[allow(clippy::invalid_regex)] // https://github.com/rust-lang/rust-clippy/issues/10825
            Regex::new("(?i-u)<a[[:space:]]name=['\"]?([^&>]*?)['\"]?>").unwrap()
        });
        let mut bib = HashMap::default();
        for captures in a_name.captures_iter(&source.text) {
            let m = captures.get(0).unwrap();
            let sp = Span::new(m.start(), m.end());
            if let Some(sp2) = bib.insert(captures.get(1).unwrap().as_bytes().into(), sp) {
                diags.push((source, BibError::DuplicateBib(sp2, sp)))
            }
        }
        Self(bib.into_iter().map(|x| x.0).collect())
    }

    /// Does this bibliography contain a definition for the given tag?
    #[must_use]
    pub fn contains(&self, tag: &[u8]) -> bool {
        self.0.contains(tag)
    }
}

struct HtmlParser {
    start: usize,
    parser: Utf8LossyDecoder<html5ever::Parser<scraper::Html>>,
    string: String,
}

impl HtmlParser {
    fn new(start: usize) -> Self {
        use html5ever::{local_name, namespace_url, ns};
        let parser = html5ever::driver::parse_fragment(
            scraper::Html::new_fragment(),
            html5ever::ParseOpts::default(),
            html5ever::QualName::new(None, ns!(html), local_name!("div")),
            vec![],
        );
        Self {
            start,
            parser: parser.from_utf8(),
            string: String::new(),
        }
    }

    fn feed(&mut self, text: &[u8]) {
        self.parser.process(Tendril::from_slice(text));
        self.string += crate::as_str(text);
    }

    fn validate(self, end: usize, diag: &mut impl FnMut(Diagnostic)) {
        let mut errors = self.parser.finish().errors;
        if !errors.is_empty() {
            // html5ever has garbage error messages (https://github.com/servo/html5ever/issues/492)
            // but apparently there aren't any other HTML validators and I'm not going to write one
            // myself
            errors.sort();
            errors.dedup();
            diag(Diagnostic::HtmlParseError(
                Span::new(self.start, end),
                errors,
            ))
        }
    }
}
