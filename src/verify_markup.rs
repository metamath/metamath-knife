use std::ops::Range;

use regex::bytes::Regex;

use crate::{
    comment_parser::{Date, Parenthetical},
    diag::{Diagnostic, MarkupKind},
    scopeck::Hyp,
    segment::SegmentRef,
    statement::{StatementAddress, NO_STATEMENT},
    Database, Span, StatementRef, StatementType,
};

#[derive(Copy, Clone, Debug)]
pub struct VerifyMarkup {
    pub check_dates: bool,
    pub check_external_files: bool,
    pub check_underscores: bool,
    pub check_mathbox_ref: bool,
}

impl Default for VerifyMarkup {
    fn default() -> Self {
        Self {
            check_dates: false,
            check_external_files: false,
            check_underscores: true,
            check_mathbox_ref: true,
        }
    }
}

impl VerifyMarkup {
    /// Check dates for consistency with the current date (default: false)
    pub fn check_dates(&mut self, check: bool) -> &mut Self {
        self.check_dates = check;
        self
    }

    /// Check that external files exist (default: false)
    pub fn check_external_files(&mut self, check: bool) -> &mut Self {
        self.check_external_files = check;
        self
    }

    /// Check labels for underscores (default: true)
    pub fn check_underscores(&mut self, check: bool) -> &mut Self {
        self.check_underscores = check;
        self
    }

    /// Check for mathbox cross-references (default: true)
    pub fn check_mathbox_ref(&mut self, check: bool) -> &mut Self {
        self.check_mathbox_ref = check;
        self
    }

    /// Run the verify markup pass on the given database.
    pub fn run(self, db: &Database) -> Vec<(StatementAddress, Diagnostic)> {
        db.verify_markup(self)
    }
}

lazy_static::lazy_static! {
    static ref WINDOWS_RESERVED_NAMES: Regex =
        Regex::new("(?i)^(?:CON|PRN|AUX|NUL|(?:COM|LPT)[1-9])$").unwrap();
}

impl Database {
    /// Run the verify markup pass on the database.
    /// Requires: [`Database::scope_pass`], [`Database::typesetting_pass`]
    #[allow(clippy::cognitive_complexity)]
    #[must_use]
    pub fn verify_markup(&self, opts: VerifyMarkup) -> Vec<(StatementAddress, Diagnostic)> {
        let mut diags = vec![];
        let tdata = &**self.typesetting_result();

        for stmt in self.statements() {
            if opts.check_underscores && stmt.label().contains(&b'_') {
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
            }
            if WINDOWS_RESERVED_NAMES.is_match(stmt.label()) {
                diags.push((
                    stmt.address(),
                    Diagnostic::WindowsReservedLabel(stmt.label_span()),
                ))
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
                _ => {}
            }
            if stmt.is_assertion() {
                let buf = &stmt.segment.segment.buffer;
                let mut contributor = None;
                let mut laters = vec![];
                let mut proof_mod = None;
                let mut new_usage_discouraged = false;
                let mut prev_date = None;
                if let Some(comment) = stmt.associated_comment() {
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

        for (kind, map) in [
            (MarkupKind::Html, &tdata.html_defs),
            (MarkupKind::AltHtml, &tdata.alt_html_defs),
            (MarkupKind::Latex, &tdata.latex_defs),
        ] {
            for (tk, (sp, (seg_id, _), _)) in map {
                if self.name_result().lookup_symbol(tk).is_none() {
                    diags.push((
                        StatementAddress::new(*seg_id, NO_STATEMENT),
                        Diagnostic::UndefinedMarkupDef(kind, *sp),
                    ))
                }
            }
        }

        if let Some((sp, tk)) = &tdata.ext_html_label {
            if self.name_result().lookup_label(tk).is_none() {
                diags.push((
                    StatementAddress::new(sp.0, NO_STATEMENT),
                    Diagnostic::UnknownLabel(sp.1),
                ))
            }
        }

        // omitted: check that files in IMG SRC="..." of html_defs exist
        // omitted: check that html_home has HREF="..." and IMG SRC="..."
        // omitted: check that ext_html_home has HREF="..." and IMG SRC="..."
        // omitted: top date check

        // todo: section header comments
        // todo: bibliographic references
        // todo: mathbox independence

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
