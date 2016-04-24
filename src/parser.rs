type BufferRef = Arc<Vec<u8>>;
/// change me if you want to parse files > 4GB
pub type FilePos = u32;

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub struct Span {
    pub start: FilePos,
    pub end: FilePos,
}

impl Span {
    fn new(start: usize, end: usize) -> Span {
        Span { start: start as FilePos, end: end as FilePos }
    }

    fn new2(start: FilePos, end: FilePos) -> Span {
        Span { start, end }
    }

    fn as_ref(&self, buf: &[u8]) -> &[u8] {
        buf[self.start .. self.end]
    }
}

/// This is a "dense" segment, which must be fully rebuilt in order to make any change.  We may in
/// the future have an "unpacked" segment which is used for active editing, as well as a "lazy" or
/// "mmap" segment type for fast incremental startup.
struct Segment {
    // buffer: BufferRef,
    // segment_span: Span,
}

#[derive(Debug,Clone,Eq)]
pub enum Diagnostic {
    BadCharacter(Span, u8),
    CommentMarkerNotStart(Span),
    MidStatementCommentMarker(Span),
    NestedComment(Span, Span),
    BadCommentEnd(Span, Span),
    UnclosedComment(Span),
}

#[derive(Copy,Clone,Debug)]
enum StatementType {
    /// Psuedo statement used only to record end-of-file whitespace
    Eof,
    /// Statement is damaged enough that there's no sense passing it to later stages
    Invalid,
    Comment,
    TypesettingComment,
    FileInclude,
    Axiom,
    Provable,
    Essential,
    Floating,
    Disjoint,
    OpenGroup,
    CloseGroup,
    Constant,
    Variable,
}

#[derive(Clone,Debug)]
struct Statement {
    type: StatementType,
    span: Span,
    full_span: Span,
    label: Span,
    math: Vec<Span>,
    proof: Vec<Span>,
    diagnostics: Vec<Diagnostic>,
}

#[derive(Default)]
struct Scanner<'a> {
    buffer: &'a [u8],
    position: FilePos,
    diagnostics: Vec<Diagnostic>,
    unget: Option<Span>,
    labels: Vec<Span>,
}

const mm_valid_spaces: u64 = (1u64 << 9) | (1u64 << 10) | (1u64 << 12) | (1u64 << 13) |
    (1u64 << 32);

fn is_mm_space_c0(byte: u8) -> bool {
    (mm_valid_spaces & (1u64 << byte)) != 0
}

fn is_mm_space(byte: u8) -> bool {
    byte <= 32 && is_mm_space_c0(byte)
}

enum CommentType {
    Normal,
    Typesetting,
    Extra,
}

impl<'a> Scanner<'a> {
    fn get_raw(&mut self) -> Option<Span> {
        let len = self.buffer.len();
        let mut ix = self.position as usize;

        while ix < len && self.buffer[ix] <= 32 {
            // For the purpose of error recovery, we consider C0 control characters to be
            // whitespace (following SMM2)
            if !is_mm_space_c0(self.buffer[ix]) {
                self.diagnostics.push(Diagnostic::BadCharacter(
                    Span::new(ix, ix + 1), self.buffer[ix]));
            }
            ix += 1;
        }

        let mut start = ix;
        while ix < len && self.buffer[ix] > 32 {
            if self.buffer[ix] > 126 {
                // DEL or C1 control or non-ASCII bytes (presumably UTF-8)
                self.diagnostics.push(Diagnostic::BadCharacter(
                    Span::new(ix, ix + 1), self.buffer[ix]));
                // skip this "token"
                ix += 1;
                while ix < len && !is_mm_space(self.buffer[ix]) { ix += 1; }
                while ix < len && is_mm_space(self.buffer[ix]) { ix += 1; }
                start = ix;
                continue;
            }

            ix += 1;
        }

        self.position = ix as FilePos;
        if start == ix {
            None
        } else {
            Some(Span::new(start, ix))
        }
    }

    fn get_comment(&mut self, opener: Span, mid_statement: bool) -> (Span, CommentType) {
        let mut type = CommentType::Normal;
        let mut first = true;
        while let Some(tok) = self.get_raw() {
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$)" {
                return (Span::new2(opener.start, tok.end), type)
            } else if tok_ref == b"$j" || tok_ref == b"$t" {
                if !first {
                    self.diagnostics.push(Diagnostic::CommentMarkerNotStart(tok))
                } else if mid_statement {
                    self.diagnostics.push(Diagnostic::MidStatementCommentMarker(tok))
                } else {
                    if tok_ref == b"$j" {
                        type = CommentType::Extra;
                    } else {
                        type = CommentType::Typesetting;
                    }
                }
            } else if tok_ref.contains(b'$') {
                let tok_str = str::from(tok_ref).unwrap();
                if tok_str.contains("$)") {
                    self.diagnostics.push(Diagnostic::BadCommentEnd(tok, opener));
                }
                if tok_str.contains("$()") {
                    self.diagnostics.push(Diagnostic::NestedComment(tok, opener));
                }
            }

            first = false;
        }

        let cspan = Span::new2(opener.start, self.buffer.len());
        self.diagnostics.push(Diagnostic::UnclosedComment(cspan));
        (cspan, type)
    }

    fn get(&mut self) -> Option<Span> {
        if self.unget.is_some() {
            return self.unget.take()
        }

        while let Some(tok) = self.get_raw() {
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$(" {
                self.get_comment(tok, true);
            } else {
                return Some(tok);
            }
        }

        None
    }

    fn get_statement(&mut self) -> Option<Statement> {
        let start = self.position;
        let mut stmt = Statement {
            type: StatementType::Invalid,
            span: Span::new(0, 0),
            full_span: Span::new(0, 0)
            label: Span::new(0, 0),
            math: Vec::new(),
            proof: Vec::new(),
            diagnostics: Vec::new(),
        };

        // check if we can parse a statement-level comment
        if let Some(ftok) = self.get_raw() {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let (cspan, ctype) = self.get_comment(ftok, false);
                stmt.type = if ctype == CommentType::Typesetting {
                    StatementType::TypesettingComment
                } else {
                    StatementType::Comment
                };
                stmt.span = cspan;
                stmt.full_span = cspan;
                stmt.full_span.start = start;
                stmt.diagnostics = mem::swap(&mut self.diagnostics, Vec::new());
                return Some(stmt);
            } else {
                self.unget = Some(ftok);
            }
        }

        self.labels.clear();
        while let Some(ltok) = self.get() {
            if ltok.as_ref(self.buffer).contains(b'$') {
                self.unget = Some(ltok);
                break;
            } else {
                self.labels.push(ltok);
            }
        }

        if let Some(kwtok) = self.get() {
            let kwtok_ref = kwtok.as_ref(self.buffer);
            if kwtok_ref.len() == 2 && kwtok_ref[0] == b'$' {
                match kwtok_ref[1] {
                    b'[' => {
                        stmt.type = StatementType::FileInclude;
                    },
                    b'a' => {
                        stmt.type = StatementType::Axiom;
                    },
                    b'c' => {
                        stmt.type = StatementType::Constant;
                    },
                    b'd' => {
                        stmt.type = StatementType::Disjoint;
                    },
                    b'e' => {
                        stmt.type = StatementType::Essential;
                    },
                    b'f' => {
                        stmt.type = StatementType::Floating;
                    },
                    b'p' => {
                        stmt.type = StatementType::Provable;
                    },
                    b'v' => {
                        stmt.type = StatementType::Variable;
                    },
                    b'{}' => {
                        stmt.type = StatementType::OpenGroup;
                    },
                    b'}' => {
                        stmt.type = StatementType::CloseGroup;
                    },
                }
            }
        }
    }
}

/// This function implements parsing stage 1, which breaks down the metalanguage grammar, finding
/// all identifier definitions and inclusion statements.
///
/// There is an argument to be made that we shouldn't tokenize or store the math strings and proofs
/// at this stage, since they're bulky and can easily be generated on demand.
///
/// The current Metamath spec defines comments and file inclusions at the token level.  It is
/// useful for our purposes to parse comments that are strictly between statements as if they were
/// statements (SMM2 did this too; may revisit) and we require file inclusions to be between
/// statements at the top nesting level (this has been approved by Norman Megill).
pub fn parse_segments(input: &BufferRef) -> Vec<Segment> {
    let mut closed_spans = Vec::new();
    let mut scanner = Scanner { buffer: input, ..Scanner::default() };

    while let Some(token) = scanner.get_raw() {
        let tok_ref = tok.as_ref(self.buffer);


    }
}
