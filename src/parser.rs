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

    fn null() -> Span {
        Span::new(0, 0)
    }

    fn as_ref(&self, buf: &[u8]) -> &[u8] {
        buf[self.start .. self.end]
    }
}

/// This is a "dense" segment, which must be fully rebuilt in order to make any change.  We may in
/// the future have an "unpacked" segment which is used for active editing, as well as a "lazy" or
/// "mmap" segment type for fast incremental startup.
pub struct Segment {
    // straight outputs
    pub statements: Vec<Statement>,
    pub next_file: Span,
    // crossed outputs
}

#[derive(Debug,Clone,Eq)]
pub enum Diagnostic {
    BadCharacter(Span, u8),
    CommentMarkerNotStart(Span),
    MidStatementCommentMarker(Span),
    NestedComment(Span, Span),
    BadCommentEnd(Span, Span),
    UnclosedComment(Span),
    BadLabel(Span),
    UnclosedMath,
    UnclosedProof,
}

#[derive(Copy,Clone,Debug,Eq,PartialEq)]
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
use StatementType::*;

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

#[derive(Clone,Debug)]
struct Statement {
    type: StatementType,
    span: Span,
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
    statement_start: FilePos,
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

    fn out_statement(&mut self, type: StatementType, label: Span, math: Vec<Span>, proof: Vec<Span>) -> Statement {
        Statement {
            type, label, math, proof,
            diagnostics: mem::replace(&mut self.diagnostics, Vec::new()),
            span: Span::new2(mem::replace(&mut self.statement_start, self.position), self.position),
        }
    }

    fn get_comment_statement(&mut self) -> Option<Statement> {
        if let Some(ftok) = self.get_raw() {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let (cspan, ctype) = self.get_comment(ftok, false);
                let type if ctype == CommentType::Typesetting {
                    TypesettingComment
                } else {
                    Comment
                };
                return Some(self.out_statement(type, Span::null(), Vec::new(), Vec::new()));
            } else {
                self.unget = Some(ftok);
            }
        }
        None
    }

    fn read_labels(&mut self) {
        self.has_bad_labels = false;
        self.labels.clear();
        while let Some(ltok) = self.get() {
            let lref = ltok.as_ref(self.buffer);
            if lref.contains(b'$') {
                self.unget = Some(ltok);
                break;
            } else if !is_valid_label(lref) {
                self.diagnostics.push(Diagnostic::BadLabel(ltok));
                self.has_bad_labels = true;
            } else {
                self.labels.push(ltok);
            }
        }
    }

    fn get_no_label(&mut self) {
        // none of these are invalidations...
        for lspan in &self.labels {
            self.diagnostics.push(Diagnostic::SpuriousLabel(lspan));
        }
    }

    fn get_label(&mut self) -> Span {
        if self.labels.len() == 1 {
            self.labels[0]
        } else if self.labels.len() == 0 {
            self.diagnostics.push(Diagnostic::MissingLabel);
            self.invalidated = true;
            Span::null()
        } else {
            for addl in self.labels.iter().skip(1) {
                self.diagnostics.push(Diagnostic::RepeatedLabel(addl, self.labels[0]));
            }
            // have to invalidate because we don't know which to use
            self.invalidated = true;
            Span::null()
        }
    }

    fn get_string(&mut self, expect_proof: bool, is_proof: bool) -> (Vec<Span>, bool) {
        let mut out = Vec::new();
        while let Some(tokn) = self.get() {
            let toknref = tokn.as_ref(self.buffer);
            if toknref.contains(b'$') {
                if toknref == b"$." {
                    // string is closed with no proof
                    if expect_proof {
                        self.diagnostics.push(Diagnostic::MissingProof(tokn));
                    }
                    return (out, false);
                } else if toknref == b"$=" && !is_proof {
                    // string is closed with a proof
                    if !expect_proof {
                        self.diagnostics.push(Diagnostic::SpuriousProof(tokn));
                    }
                    return (out, true);
                } else {
                    // string is closed with no proof and with an error, whoops
                    self.unget = true;
                    break;
                }
            } else {
                out.push(tokn);
            }
        }

        self.diagnostics.push(if is_proof { Diagnostic::UnclosedProof } else { Diagnostic::UnclosedMath });
        return (out, false);
    }

    fn get_strings(&mut self, want_proof: bool) -> (Vec<Span>, Vec<Span>) {
        let (math_str, has_proof) = self.get_string(want_proof, false);

        if math_str.len() == 0 {
            self.invalidated = true;
            // this is invalid for all types of math string
            self.diagnostics.push(Diagnostic::EmptyMathString);
        }

        let (proof_str, _) = if has_proof {
            // diagnostic already generated if unwanted, but we still need to eat the proof
            self.get_string(false, true)
        } else {
            // diagnostic already generated if unwanted.  this is NOT an invalidation as $p
            // statements don't need proofs (I mean you should have a ? but we know what you mean)
            (Vec::new(), false)
        }
        (math_str, proof_str)
    }

    fn eat_invalid(&mut self) {
        while let Some(tok) = self.get() {
            let tref = tok.as_ref(self.buffer);
            if tref == b"$." {
                // we're probably synchronized
                break;
            } else if tref == b"$=" {
                // this is definitely not it
            } else if tref.contains(b'$') {
                // might be the start of the next statement
                self.unget = true;
                break;
            }
        }
    }

    fn get_file_include(&mut self) -> Span {
        let mut res = Span::null();
        let mut count = 0;
        while let Some(tok) = self.get() {
            let tref = tok.as_ref(self.buffer);
            if tref == b"$]" {
                if count == 0 {
                    self.diagnostics.push(Diagnostic::EmptyFilename);
                    self.invalidated = true;
                } else if count > 1 {
                    self.diagnostics.push(Diagnostic::FilenameSpaces);
                    self.invalidated = true;
                } else if res.as_ref(self.buffer).contains(b'$') {
                    self.diagnostics.push(Diagnostic::FilenameDollar);
                }
                return res;
            } else if tref.len() > 0 && tref[0] == b'$' {
                break;
            } else {
                count += 1;
                res = tok;
            }
        }
        self.diagnostics.push(Diagnostic::UnclosedInclude);
        self.invalidated = true;
        return res;
    }

    fn get_statement(&mut self) -> Statement {
        self.statement_start = self.position;

        if let Some(stmt) = self.get_comment_statement() {
            return stmt;
        }

        self.read_labels();

        let mut type = Eof;
        if let Some(kwtok) = self.get() {
            let kwtok_ref = kwtok.as_ref(self.buffer);
            type = if kwtok_ref.len() == 2 && kwtok_ref[0] == b'$' {
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
                Invalid,
            };
        }
        self.invalidated = false;

        let label = if type.takes_label() {
            self.get_label()
        } else {
            self.get_no_label();
            Span::null()
        };

        let (math, proof) = if type.takes_math() {
            self.get_strings(type == Provable)
        } else {
            (Vec::new(), Vec::new())
        };

        match type {
            FileInclude => {
                label = self.get_file_include();
            }
            Disjoint => {
                // math.len = 1 was caught above
                if math.len() == 1 {
                    self.diagnostics.push(Diagnostic::DisjointSingle);
                    self.invalidated = true;
                }
            }
            Floating => {
                if math.len() != 0 && math.len() != 2 {
                    self.diagnostics.push(Diagnostics::BadFloating);
                    self.invalidated = true;
                }
            }
            Invalid => {
                // eat tokens to the next keyword rather than treating them as labels
                self.eat_invalid();
            }
            _ => {}
        }

        if self.invalidated {
            type = Invalid;
        }

        self.out_statement(type, label, math, proof)
    }
}

fn is_valid_label(label: &[u8]) -> bool {
    for c in label {
        if !(c == b'.' || c == b'-' || c == b'_' || (c >= b'a' && c <= b'z') || (c >= b'0' && c <= b'9') || (c >= b'A' && c <= b'Z')) {
            return false;
        }
    }
    true
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
