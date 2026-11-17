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

use crate::diag::{Diagnostic, MarkupKind};
use crate::segment::{BufferRef, Segment};
use crate::segment_set::SegmentSet;
use crate::statement::{
    Command, CommandToken, FilePos, FloatDef, GlobalDv, GlobalSpan, HeadingDef, LabelDef,
    LocalVarDef, Span, Statement, StatementAddress, StatementIndex, SymbolDef, SymbolType, Token,
    TokenIndex, TokenPtr, NO_STATEMENT,
};
use crate::typesetting::TypesettingData;
use crate::StatementType::{self, *};
use regex::bytes::Regex;
use std::cmp;
use std::collections::hash_map::Entry;
use std::fmt::Debug;
use std::mem;
use std::str;
use std::sync::{Arc, OnceLock};

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
const MM_VALID_SPACES: u64 =
    (1u64 << 9) | (1u64 << 10) | (1u64 << 12) | (1u64 << 13) | (1u64 << 32);

/// Check if a character which is known to be <= 32 is a valid Metamath
/// whitespace.  May panic if out of range.
const fn is_mm_space_c0(byte: u8) -> bool {
    (MM_VALID_SPACES & (1u64 << byte)) != 0
}

/// Check if a character is valid Metamath whitespace.
///
/// We generally accept any C0 control as whitespace, with a diagnostic; this
/// function only tests for fully legal whitespace though.
const fn is_mm_space(byte: u8) -> bool {
    byte <= 32 && is_mm_space_c0(byte)
}

#[derive(Default, Debug, Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
/// The different types of heading markers, as defined in the Metamath book, section 4.4.1
pub enum HeadingLevel {
    /// Virtual top-level heading, used as a root node
    #[default]
    Database,
    /// Major part
    MajorPart,
    /// Section
    Section,
    /// Subsection
    SubSection,
    /// Subsubsection
    SubSubSection,
    /// Statement
    Statement,
}

#[derive(Eq, PartialEq, Copy, Clone)]
enum CommentType {
    Normal,
    Typesetting,
    Extra,
    Heading(HeadingLevel),
}

impl Scanner<'_> {
    /// Record a diagnostic against the nascent statement
    fn diag(&mut self, diag: Diagnostic) {
        self.diagnostics.push((self.statement_index, diag));
    }

    /// Get a single whitespace-delimited token from the source text without
    /// checking for comments or the unget area.
    ///
    /// This function accepts any C0 character as whitespace, with a diagnostic.
    /// DEL and non-7bit characters invalidate the current token and cause it to
    /// be omitted from the returned string.  `Span::NULL` is returned when
    /// the end of the buffer is reached.
    ///
    /// This is _very_ hot, mostly due to the unpredicable branches in the
    /// whitespace testing.  It might be possible to write a version which is
    /// branch-free in typical cases, but it would be extremely fiddly and has
    /// not been attempted.
    fn get_raw(&mut self) -> Span {
        #[inline(never)]
        #[cold]
        fn badchar(slf: &mut Scanner<'_>, ix: usize) -> Span {
            let ch = slf.buffer[ix];
            slf.diag(Diagnostic::BadCharacter(ix, ch));
            // Restart the function from the beginning to reload self.buffer;
            // doing it this way lets it be kept in a register in the common
            // case
            slf.get_raw()
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
            Span::NULL
        } else {
            Span::new(start, ix)
        }
    }

    /// Assuming that a `$(` token has just been read, read and skip a comment.
    ///
    /// If the comment appears to be special, notice that.  This currently
    /// detects `$j`, `$t` comments, and outline comments.
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
            } else if first && tok_ref.len() >= 4 {
                if tok_ref[..4] == *b"####" {
                    ctype = CommentType::Heading(HeadingLevel::MajorPart);
                } else if tok_ref[..4] == *b"#*#*" {
                    ctype = CommentType::Heading(HeadingLevel::Section);
                } else if tok_ref[..4] == *b"=-=-" {
                    ctype = CommentType::Heading(HeadingLevel::SubSection);
                } else if tok_ref[..4] == *b"-.-." {
                    ctype = CommentType::Heading(HeadingLevel::SubSubSection);
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
            return mem::replace(&mut self.unget, Span::NULL);
        }

        loop {
            let tok = self.get_raw();
            if tok.is_null() {
                return Span::NULL;
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
    const fn out_statement(&mut self, stype: StatementType, label: Span) -> Statement {
        Statement {
            stype,
            label,
            math_start: self.statement_math_start,
            proof_start: self.statement_proof_start,
            proof_end: self.span_pool.len(),
            group: NO_STATEMENT,
            group_end: NO_STATEMENT,
            span: Span::new2(
                mem::replace(&mut self.statement_start, self.position),
                self.position,
            ),
        }
    }

    /// Check for and parse a comment statement at the current position.
    fn get_comment_statement(&mut self) -> Option<Statement> {
        let ftok = if self.unget.is_null() {
            self.get_raw()
        } else {
            mem::replace(&mut self.unget, Span::NULL)
        };
        if ftok != Span::NULL {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let ctype = self.get_comment(ftok, false);
                let s_type = match ctype {
                    CommentType::Typesetting => TypesettingComment,
                    CommentType::Heading(level) => HeadingComment(level),
                    CommentType::Extra => AdditionalInfoComment,
                    CommentType::Normal => Comment,
                };
                return Some(self.out_statement(s_type, Span::new2(ftok.start, ftok.start)));
            }
            self.unget = ftok;
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
            } else if is_valid_label(lref) {
                self.labels.push(ltok);
            } else {
                self.diag(Diagnostic::BadLabel(ltok));
            }
        }
    }

    /// We now know we shouldn't have labels.  Issue errors if we do anyway.
    fn get_no_label(&mut self, kwtok: Span) -> Span {
        // none of these are invalidations...
        for &lspan in &self.labels {
            self.diagnostics
                .push((self.statement_index, Diagnostic::SpuriousLabel(lspan)));
        }

        // If this is a valid no-label statement, kwtok will have the keyword.
        // Otherwise it may be Span(0,0) = null, in which case we also return Span(0,0).
        Span::new2(kwtok.start, kwtok.start)
    }

    /// We now know we need exactly one label.  Error and invalidate if we don't
    /// have it.
    fn get_label(&mut self) -> Span {
        match self.labels.len() {
            1 => self.labels[0],
            0 => {
                self.diag(Diagnostic::MissingLabel);
                self.invalidated = true;
                Span::NULL
            }
            _ => {
                for &addl in self.labels.iter().skip(1) {
                    self.diagnostics.push((
                        self.statement_index,
                        Diagnostic::RepeatedLabel(addl, self.labels[0]),
                    ));
                }
                // have to invalidate because we don't know which to use
                self.invalidated = true;
                Span::NULL
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
                }
                // string is closed with no proof and with an error, whoops
                self.unget = tokn;
                break;
            }
            self.span_pool.push(tokn);
        }

        self.diag(if is_proof {
            Diagnostic::UnclosedProof
        } else {
            Diagnostic::UnclosedMath
        });
        false
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
        let mut res = Span::NULL;
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
            } else if !tref.is_empty() && tref[0] == b'$' {
                break;
            }
            count += 1;
            res = tok;
        }
        self.diag(Diagnostic::UnclosedInclude);
        self.invalidated = true;
        res
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
            self.get_no_label(kwtok)
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

        let stype = if self.invalidated { Invalid } else { stype };

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
            next_file: Span::NULL,
            symbols: Vec::new(),
            local_vars: Vec::new(),
            global_dvs: Vec::new(),
            labels: Vec::new(),
            floats: Vec::new(),
            buffer: self.buffer_ref.clone(),
            diagnostics: Vec::new(),
            span_pool: Vec::new(),
            outline: Vec::new(),
            t_commands: Vec::new(),
            j_commands: Vec::new(),
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
                CloseGroup if top_group != NO_STATEMENT => {
                    seg.statements[top_group as usize].group_end = index;
                    top_group = seg.statements[top_group as usize].group;
                }
                CloseGroup => self.diag(Diagnostic::UnmatchedCloseGroup),
                Constant if top_group != NO_STATEMENT => {
                    self.diag(Diagnostic::ConstantNotTopLevel);
                }
                Essential if top_group == NO_STATEMENT => {
                    self.diag(Diagnostic::EssentialAtTopLevel)
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
            if seg.statements[index].group != NO_STATEMENT
                && seg.statements[index].stype != OpenGroup
            {
                seg.statements[index].group_end =
                    seg.statements[seg.statements[index].group as usize].group_end;
            }
        }

        seg.diagnostics = mem::take(&mut self.diagnostics);
        seg.span_pool = mem::take(&mut self.span_pool);
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
    for (index, stmt) in seg.statements.iter().enumerate() {
        let index = index as StatementIndex;
        if stmt.stype.takes_label() {
            seg.labels.push(LabelDef { index });
        }

        if stmt.group_end != NO_STATEMENT {
            if stmt.stype == Variable {
                let math = &seg.span_pool[stmt.math_start..stmt.proof_start];
                for sindex in 0..math.len() {
                    seg.local_vars.push(LocalVarDef {
                        index,
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            // Skip further treatment if the statement is not at top-level, except for $j commands.
            if stmt.stype != AdditionalInfoComment {
                continue;
            }
        }

        let math = &seg.span_pool[stmt.math_start..stmt.proof_start];

        match stmt.stype {
            Constant => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Constant,
                        start: index,
                        name: span.as_ref(buf).into(),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Variable => {
                for (sindex, &span) in math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Variable,
                        start: index,
                        name: span.as_ref(buf).into(),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Disjoint => {
                seg.global_dvs.push(GlobalDv {
                    start: index,
                    vars: math.iter().map(|sp| sp.as_ref(buf).into()).collect(),
                });
            }
            Floating => {
                seg.floats.push(FloatDef {
                    start: index,
                    typecode: math[0].as_ref(buf).into(),
                    label: stmt.label.as_ref(buf).into(),
                    name: math[1].as_ref(buf).into(),
                });
            }
            HeadingComment(level) => {
                seg.outline.push(HeadingDef {
                    name: get_heading_name(buf, stmt.span.start).into(),
                    index,
                    level,
                });
            }
            TypesettingComment => match commands(buf, b't', stmt.span.start) {
                Ok(commands) => {
                    for result in commands {
                        match result {
                            Ok(command) => seg.t_commands.push((index, command)),
                            Err(diag) => seg.diagnostics.push((index, diag)),
                        }
                    }
                }
                Err(diag) => seg.diagnostics.push((index, diag)),
            },
            AdditionalInfoComment => match commands(buf, b'j', stmt.span.start) {
                Ok(commands) => {
                    for result in commands {
                        match result {
                            Ok(command) => seg.j_commands.push((index, command)),
                            Err(diag) => seg.diagnostics.push((index, diag)),
                        }
                    }
                }
                Err(diag) => seg.diagnostics.push((index, diag)),
            },
            _ => {}
        }
    }
}

/// Metamath spec valid label characters are `[-._a-zA-Z0-9]`
#[must_use]
pub fn is_valid_label(label: &[u8]) -> bool {
    label
        .iter()
        .all(|&c| c == b'.' || c == b'-' || c == b'_' || c.is_ascii_alphanumeric())
}

/// Extract a section name from a comment
fn get_heading_name(buffer: &[u8], pos: FilePos) -> TokenPtr<'_> {
    let mut index = pos as usize;
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
    &buffer[index..eol]
}

/// Extract the parser commands out of a $t or $j special comment
pub(crate) fn commands(buffer: &[u8], ch: u8, pos: FilePos) -> Result<CommandIter<'_>, Diagnostic> {
    let mut iter: CommandIter<'_> = CommandIter {
        buffer,
        index: pos as usize,
    };
    let _ = iter.skip_white_spaces()?;
    iter.expect(b'$')?;
    iter.expect(b'(')?;
    let _ = iter.skip_white_spaces()?;
    iter.expect(b'$')?;
    iter.expect(ch)?;
    Ok(iter)
}

pub(crate) struct CommandIter<'a> {
    buffer: &'a [u8],
    index: usize,
}

impl CommandIter<'_> {
    const fn has_more(&self) -> bool {
        self.index < self.buffer.len()
    }

    const fn next_char(&self) -> u8 {
        self.buffer[self.index]
    }

    fn skip_white_spaces(&mut self) -> Result<Option<()>, Diagnostic> {
        'outer_loop: while self.has_more() {
            match self.next_char() {
                b' ' | b'\t' | b'\n' | b'\r' => {} // Skip white spaces and line feeds
                // End upon comment closing, $)
                b'$' => return Ok(None),
                // Found a comment start
                b'/' if self.buffer.get(self.index + 1) == Some(&b'*') => {
                    for i in self.index + 2..self.buffer.len() - 1 {
                        // found the end of the comment
                        if self.buffer[i] == b'*' && self.buffer[i + 1] == b'/' {
                            self.index = i + 2;
                            continue 'outer_loop;
                        }
                    }
                    // unclosed comment, advance self.index to end
                    let cspan = Span::new(self.index, self.buffer.len());
                    self.index = self.buffer.len();
                    return Err(Diagnostic::UnclosedCommandComment(cspan));
                }
                // Else stop
                _ => break,
            }
            self.index += 1;
        }
        Ok(Some(()))
    }

    #[allow(clippy::if_not_else)]
    const fn expect(&mut self, c: u8) -> Result<(), Diagnostic> {
        if !self.has_more() {
            let cspan = Span::new(self.index, self.buffer.len());
            Err(Diagnostic::UnclosedComment(cspan))
        } else if self.next_char() != c {
            let cspan = Span::new(self.index, self.buffer.len());
            Err(Diagnostic::MalformedAdditionalInfo(cspan))
        } else {
            self.index += 1;
            Ok(())
        }
    }
}

impl Iterator for CommandIter<'_> {
    type Item = Result<Command, Diagnostic>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.skip_white_spaces() {
            Ok(Some(())) => {}
            Ok(None) => return None,
            Err(diag) => return Some(Err(diag)),
        }

        let command_start = self.index;
        let mut command = Vec::new();
        while self.has_more() {
            let token = if let quote @ (b'\'' | b'\"') = self.next_char() {
                self.index += 1;
                let token_start = self.index;
                // Stop if end quote
                loop {
                    if !self.has_more() {
                        let cspan = Span::new(token_start, self.buffer.len());
                        return Some(Err(Diagnostic::UnclosedCommandString(cspan)));
                    }
                    let ch = self.next_char();
                    self.index += 1;
                    if ch == quote {
                        if self.has_more() && self.next_char() == quote {
                            self.index += 1;
                        } else {
                            break;
                        }
                    }
                }
                if self.has_more()
                    && !matches!(self.next_char(), b' ' | b'\t' | b'\n' | b'\r' | b';')
                {
                    let cspan = Span::new(token_start, self.index);
                    return Some(Err(Diagnostic::MissingSpaceAfterCommandToken(cspan)));
                }
                CommandToken::String(Span::new(token_start, self.index - 1))
            } else {
                let token_start = self.index;
                // Stop if unquoted white spaces, line feeds or semicolon
                while self.has_more()
                    && !matches!(self.next_char(), b' ' | b'\t' | b'\n' | b'\r' | b';')
                {
                    self.index += 1;
                }
                CommandToken::Keyword(Span::new(token_start, self.index))
            };
            command.push(token);

            if let Err(diag) = self.skip_white_spaces() {
                return Some(Err(diag));
            }
            if !self.has_more() {
                let cspan = Span::new(command_start, self.index);
                return Some(Err(Diagnostic::UnclosedCommand(cspan)));
            }
            if self.next_char() == b';' {
                // Stop if unquoted semicolon $)
                self.index += 1;
                return Some(Ok((Span::new(command_start, self.index), command)));
            }
        }
        None
    }
}

/// Slightly set.mm specific hack to extract a section name from a byte buffer.
///
/// This is run before parsing so it can't take advantage of comment extraction;
/// instead we look for the first indented line, within a heuristic limit of 500
/// bytes.
#[must_use]
pub fn guess_buffer_name(buffer: &[u8]) -> &str {
    let buffer = &buffer[0..cmp::min(500, buffer.len())];
    let ptr = get_heading_name(buffer, 0);

    // fail gracefully, this is a debugging aid only
    if ptr.is_empty() {
        "<no section name found>"
    } else {
        str::from_utf8(ptr).unwrap_or("<invalid UTF-8 in section name>")
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
#[must_use]
pub fn parse_segments(input: &BufferRef) -> Vec<Arc<Segment>> {
    let mut closed_spans = Vec::new();
    let mut scanner = Scanner {
        buffer_ref: input.clone(),
        buffer: input,
        ..Scanner::default()
    };
    assert!(input.len() < FilePos::MAX as usize);

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
#[must_use]
pub fn dummy_segment(diag: Diagnostic) -> Arc<Segment> {
    let mut seg = parse_segments(&Arc::new(Vec::new())).pop().unwrap();
    Arc::get_mut(&mut seg).unwrap().diagnostics.push((0, diag));
    seg
}

impl SegmentSet {
    pub(crate) fn build_typesetting_data(&self) -> TypesettingData {
        fn parse_one(
            data: &mut TypesettingData,
            buf: &[u8],
            addr: StatementAddress,
            span: Span,
            command: &[CommandToken],
        ) -> Result<(), Diagnostic> {
            const fn as_string(span: Span, tok: Option<&CommandToken>) -> Result<Span, Diagnostic> {
                match tok {
                    Some(&CommandToken::String(s)) => Ok(s),
                    None => Err(Diagnostic::CommandIncomplete(span)),
                    Some(&CommandToken::Keyword(s)) => Err(Diagnostic::CommandExpectedString(s)),
                }
            }

            let (cmd, mut rest) = match command.split_first() {
                Some((&CommandToken::Keyword(k), rest)) => (k, rest.iter()),
                _ => return Err(Diagnostic::BadCommand(span)),
            };

            let sum = |mut rest: std::slice::Iter<'_, CommandToken>| {
                let mut span_out = as_string(span, rest.next())?;
                let mut accum: Vec<u8> = CommandToken::unescape_string(buf, span_out).into();
                span_out.start -= 1;
                loop {
                    match rest.next() {
                        None => {
                            span_out.end += 1;
                            return Ok(((addr.segment_id, span_out), accum.into()));
                        }
                        Some(CommandToken::Keyword(plus)) if plus.as_ref(buf) == b"+" => {}
                        _ => return Err(Diagnostic::CommandIncomplete(span)),
                    }
                    let span2 = as_string(span, rest.next())?;
                    CommandToken::append_unescaped_string(buf, span2, &mut accum);
                    span_out.end = span2.end
                }
            };

            let as_ = |rest: &mut std::slice::Iter<'_, CommandToken>| {
                let s = as_string(span, rest.next())?;
                match rest.next() {
                    Some(CommandToken::Keyword(as_)) if as_.as_ref(buf) == b"as" => Ok(s),
                    None => Err(Diagnostic::CommandIncomplete(span)),
                    Some(tk) => Err(Diagnostic::CommandExpectedAs(tk.full_span())),
                }
            };
            let mut insert = |kind: MarkupKind, sp: Span, (sp2, val): (GlobalSpan, Token)| {
                let map = match kind {
                    MarkupKind::Html => &mut data.html_defs,
                    MarkupKind::AltHtml => &mut data.alt_html_defs,
                    MarkupKind::Latex => &mut data.latex_defs,
                };
                match map.entry(CommandToken::unescape_string(buf, sp).into()) {
                    Entry::Occupied(e) => {
                        let (sp2, (id2, _), _) = *e.get();
                        data.diagnostics
                            .push((addr, Diagnostic::DuplicateMarkupDef(kind, (id2, sp2), sp)))
                    }
                    Entry::Vacant(e) => {
                        e.insert((sp, sp2, val));
                    }
                }
            };
            match cmd.as_ref(buf) {
                b"latexdef" => insert(MarkupKind::Latex, as_(&mut rest)?, sum(rest)?),
                b"htmldef" => insert(MarkupKind::Html, as_(&mut rest)?, sum(rest)?),
                b"althtmldef" => insert(MarkupKind::AltHtml, as_(&mut rest)?, sum(rest)?),
                b"htmlvarcolor" => data.html_var_color.push(sum(rest)?),
                b"htmltitle" => data.html_title = Some(sum(rest)?),
                b"htmlhome" => data.html_home = Some(sum(rest)?),
                b"exthtmltitle" => data.ext_html_title = Some(sum(rest)?),
                b"exthtmlhome" => data.ext_html_home = Some(sum(rest)?),
                b"exthtmllabel" => data.ext_html_label = Some(sum(rest)?),
                b"htmldir" => data.html_dir = Some(sum(rest)?),
                b"althtmldir" => data.alt_html_dir = Some(sum(rest)?),
                b"htmlbibliography" => data.html_bibliography = Some(sum(rest)?),
                b"exthtmlbibliography" => data.ext_html_bibliography = Some(sum(rest)?),
                b"htmlcss" => data.html_css = Some(sum(rest)?),
                b"htmlfont" => data.html_font = Some(sum(rest)?),
                b"htmlexturl" => data.html_ext_url = Some(sum(rest)?),
                _ => return Err(Diagnostic::UnknownTypesettingCommand(cmd)),
            }
            Ok(())
        }

        let mut data = TypesettingData::default();
        for seg in self.segments(..) {
            for &(ix, (span, ref command)) in &seg.t_commands {
                let address = StatementAddress::new(seg.id, ix);
                if let Err(diag) = parse_one(&mut data, &seg.buffer, address, span, command) {
                    data.diagnostics.push((address, diag))
                }
            }
        }
        data
    }
}

/// A parsed heading comment.
#[derive(Debug, Clone, Copy)]
pub struct HeadingComment {
    /// The header part of the heading comment (the text of the header)
    pub header: Span,
    /// The content part of the heading comment (descriptive text regarding the header)
    pub content: Span,
}

impl HeadingComment {
    /// Parses a heading comment at the given span in a segment buffer,
    /// with the specified heading level and span. Returns `None` if this is not a heading comment
    /// or it is malformed.
    #[must_use]
    pub fn parse(buf: &[u8], lvl: HeadingLevel, sp: Span) -> Option<Self> {
        static MAJOR_PART: OnceLock<Regex> = OnceLock::new();
        static SECTION: OnceLock<Regex> = OnceLock::new();
        static SUBSECTION: OnceLock<Regex> = OnceLock::new();
        static SUBSUBSECTION: OnceLock<Regex> = OnceLock::new();
        let regex = match lvl {
            HeadingLevel::MajorPart => MAJOR_PART.get_or_init(|| {
                Regex::new(r"^[ \r\n]+#{4,}\r?\n *([^\n]*)\r?\n#{4,}\r?\n").unwrap()
            }),
            HeadingLevel::Section => SECTION.get_or_init(|| {
                Regex::new(r"^[ \r\n]+(?:#\*){2,}#?\r?\n *([^\n]*)\r?\n(?:#\*){2,}#?\r?\n").unwrap()
            }),
            HeadingLevel::SubSection => SUBSECTION.get_or_init(|| {
                Regex::new(r"^[ \r\n]+(?:=-){2,}=?\r?\n *([^\n]*)\r?\n(?:=-){2,}=?\r?\n").unwrap()
            }),
            HeadingLevel::SubSubSection => SUBSUBSECTION.get_or_init(|| {
                Regex::new(r"^[ \r\n]+(?:-\.){2,}-?\r?\n *([^\n]*)\r?\n(?:-\.){2,}-?\r?\n").unwrap()
            }),
            _ => unreachable!(),
        };
        let groups = regex.captures(sp.as_ref(buf))?;
        let m = groups.get(1)?;
        Some(Self {
            header: Span::new2(sp.start + m.start() as u32, sp.start + m.end() as u32),
            content: Span::new2(sp.start + groups.get(0)?.end() as u32, sp.end),
        })
    }

    /// Parses a mathbox heading comment, returning the span of the author name.
    #[must_use]
    pub fn parse_mathbox_header(&self, buf: &[u8]) -> Option<Span> {
        static MATHBOX_FOR: OnceLock<Regex> = OnceLock::new();
        let mathbox_for = MATHBOX_FOR.get_or_init(|| Regex::new(r"^Mathbox for (.*)$").unwrap());
        let m = mathbox_for.captures(self.header.as_ref(buf))?.get(1)?;
        Some(Span::new2(
            self.header.start + m.start() as u32,
            self.header.start + m.end() as u32,
        ))
    }
}
