use std::mem;
use std::str;
use std::sync::Arc;
use std::slice;
use std::cmp::Ordering;

pub type BufferRef = Arc<Vec<u8>>;
/// change me if you want to parse files > 4GB
pub type FilePos = u32;
pub type StatementIndex = i32;
pub const NO_STATEMENT: StatementIndex = -1; // TODO: evaluate just using Option

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
        Span { start: start, end: end }
    }

    fn null() -> Span {
        Span::new(0, 0)
    }

    fn as_ref(self, buf: &[u8]) -> &[u8] {
        &buf[self.start as usize .. self.end as usize]
    }
}

#[derive(Copy,Clone,Debug,Eq,PartialEq,Hash)]
pub struct SegmentId(pub u32);
pub type TokenIndex = i32;

// This is an example of an "order-maintenance data structure", actually a very simple one.
// We can plug in the Dietz & Sleator 1987 algorithm if this gets too slow.
#[derive(Clone,Debug)]
pub struct SegmentOrder {
    high_water: u32,
    free_list: Vec<SegmentId>,
    order: Vec<SegmentId>,
    reverse: Vec<usize>,
}

impl SegmentOrder {
    pub fn new() -> Self {
        let mut n = SegmentOrder {
            high_water: 1,
            free_list: Vec::new(),
            order: Vec::new(),
            reverse: Vec::new()
        };
        n.alloc_id();
        n.reindex();
        n
    }

    pub fn start(&self) -> SegmentId { SegmentId(1) }

    fn alloc_id(&mut self) -> SegmentId {
        self.free_list.pop().unwrap_or_else(|| {
            let index = self.high_water;
            self.high_water += 1;
            SegmentId(index)
        })
    }

    fn reindex(&mut self) {
        self.reverse = vec![0; self.high_water as usize];
        for (ordinal, &id) in self.order.iter().enumerate() {
            self.reverse[id.0 as usize] = ordinal;
        }
    }

    pub fn free_id(&mut self, id: SegmentId) {
        self.order.remove(self.reverse[id.0 as usize] as usize);
        self.free_list.push(id);
        self.reindex();
    }

    pub fn new_after(&mut self, after: SegmentId) -> SegmentId {
        let id = self.alloc_id();
        self.order.insert(self.reverse[after.0 as usize] as usize + 1, id);
        self.reindex();
        id
    }

    pub fn cmp(&self, left: SegmentId, right: SegmentId) -> Ordering {
        self.reverse[left.0 as usize].cmp(&self.reverse[right.0 as usize])
    }

    pub fn cmp_2(&self, left: StatementAddress, right: StatementAddress) -> Ordering {
        let order = self.cmp(left.segment_id, right.segment_id);
        (order, left.index).cmp(&(Ordering::Equal, right.index))
    }

    pub fn cmp_3(&self, left: TokenAddress, right: TokenAddress) -> Ordering {
        let order = self.cmp_2(left.statement, right.statement);
        (order, left.token_index).cmp(&(Ordering::Equal, right.token_index))
    }
}

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub struct StatementAddress {
    pub segment_id: SegmentId,
    pub index: StatementIndex,
}

impl StatementAddress {
    pub fn unbounded_range(self) -> GlobalRange {
        GlobalRange { start: self, end: NO_STATEMENT }
    }
}

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub struct TokenAddress {
    pub statement: StatementAddress,
    pub token_index: TokenIndex,
}

#[derive(Copy,Clone,Debug)]
pub struct GlobalRange {
    pub start: StatementAddress,
    pub end: StatementIndex, // or NO_STATEMENT
}

pub type Token = Vec<u8>;

// TODO this is rather meh.  I'd kind of like a consoldiated struct and I'd rather avoid the Strings
pub struct GlobalDv {
    pub start: StatementIndex,
    pub vars: Vec<Token>,
}

#[derive(Eq,PartialEq,Copy,Clone,Debug)]
pub enum SymbolType {
    Variable,
    Constant,
}

pub struct LabelDef {
    pub label: Token,
    pub index: StatementIndex,
}

pub struct SymbolDef {
    pub name: Token,
    pub stype: SymbolType,
    pub start: StatementIndex,
    pub ordinal: TokenIndex,
}

pub struct FloatDef {
    pub start: StatementIndex,
    pub name: Token,
    pub label: Token,
    pub typecode: Token,
}

/// This is a "dense" segment, which must be fully rebuilt in order to make any change.  We may in
/// the future have an "unpacked" segment which is used for active editing, as well as a "lazy" or
/// "mmap" segment type for fast incremental startup.
pub struct Segment {
    pub buffer: BufferRef,
    // straight outputs
    pub statements: Vec<Statement>,
    pub next_file: Span,
    // crossed outputs
    pub global_dvs: Vec<GlobalDv>,
    pub symbols: Vec<SymbolDef>,
    pub labels: Vec<LabelDef>,
    pub floats: Vec<FloatDef>,
}

impl<'a> SegmentRef<'a> {
    pub fn statement_iter(self) -> StatementIter<'a> {
        StatementIter {
            slice_iter: self.segment.statements.iter(),
            segment: self,
            index: 0,
        }
    }
}

#[derive(Clone)]
pub struct ParserResult {
    segments: Vec<Option<Arc<Segment>>>
}

impl ParserResult {
    pub fn get_segment(&self, id: SegmentId) -> &Segment {
        self.segments[id.0 as usize].as_ref().unwrap()
    }
}

#[derive(Debug,Clone,Eq,PartialEq)]
pub enum Diagnostic {
    BadCharacter(Span, u8),
    CommentMarkerNotStart(Span),
    MidStatementCommentMarker(Span),
    NestedComment(Span, Span),
    BadCommentEnd(Span, Span),
    UnclosedComment(Span),
    UnknownKeyword(Span),
    BadLabel(Span),
    UnclosedMath,
    UnclosedProof,
    SpuriousLabel(Span),
    MissingLabel,
    RepeatedLabel(Span, Span),
    MissingProof(Span),
    SpuriousProof(Span),
    EmptyMathString,
    EmptyFilename,
    FilenameSpaces,
    FilenameDollar,
    UnclosedInclude,
    DisjointSingle,
    BadFloating,
    UnmatchedCloseGroup,
    UnclosedBeforeInclude(StatementIndex),
    UnclosedBeforeEof,
    ConstantNotTopLevel,
    EssentialNotTopLevel,
    DuplicateLabel(StatementAddress),
    SymbolDuplicatesLabel(TokenIndex, StatementAddress),
    SymbolRedeclared(TokenIndex, TokenAddress),
    VariableRedeclaredAsConstant(TokenIndex, TokenAddress),
    NotActiveSymbol(TokenIndex),
    DjNotVariable(TokenIndex),
    DjRepeatedVariable(TokenIndex, TokenIndex),
    ExprNotConstantPrefix(TokenIndex),
    FloatNotConstant(TokenIndex),
    FloatNotVariable(TokenIndex),
    FloatRedeclared(StatementAddress),
    VariableMissingFloat(TokenIndex),
}

#[derive(Copy,Clone,Debug,Eq,PartialEq)]
pub enum StatementType {
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
use self::StatementType::*;

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
pub struct Statement {
    pub stype: StatementType,
    span: Span,
    label: Span,
    pub group: StatementIndex,
    pub group_end: StatementIndex,
    math: Vec<Span>,
    proof: Vec<Span>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Copy,Clone)]
pub struct SegmentRef<'a> {
    pub segment: &'a Segment,
    pub id: SegmentId,
}

#[derive(Copy,Clone)]
pub struct StatementRef<'a> {
    pub segment: SegmentRef<'a>,
    pub statement: &'a Statement,
    pub index: StatementIndex,
}

impl<'a> StatementRef<'a> {
    pub fn address(&self) -> StatementAddress {
        StatementAddress { segment_id: self.segment.id, index: self.index }
    }

    pub fn scope_range(&self) -> GlobalRange {
        GlobalRange { start: self.address(), end: self.statement.group_end }
    }

    pub fn label(&self) -> &[u8] {
        self.statement.label.as_ref(&self.segment.segment.buffer)
    }

    pub fn math_iter(&self) -> TokenIter {
        TokenIter { slice_iter: self.statement.math.iter(), buffer: &self.segment.segment.buffer, stmt_address: self.address(), index: 0 }
    }

    pub fn math_len(&self) -> TokenIndex {
        self.statement.math.len() as TokenIndex
    }

    pub fn math_at(&self, ix: TokenIndex) -> TokenRef {
        TokenRef {
            slice: self.statement.math[ix as usize].as_ref(&self.segment.segment.buffer),
            address: TokenAddress {
                statement: self.address(),
                token_index: ix,
            }
        }
    }
}

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

pub struct TokenIter<'a> {
    slice_iter: slice::Iter<'a, Span>,
    buffer: &'a [u8],
    stmt_address: StatementAddress,
    index: TokenIndex,
}

#[derive(Copy,Clone)]
pub struct TokenRef<'a> {
    pub slice: &'a [u8],
    pub address: TokenAddress,
}

impl<'a> TokenRef<'a> {
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
                }
            }
        })
    }
}

#[derive(Default)]
struct Scanner<'a> {
    buffer: &'a [u8],
    buffer_ref: BufferRef,
    position: FilePos,
    diagnostics: Vec<Diagnostic>,
    unget: Option<Span>,
    labels: Vec<Span>,
    statement_start: FilePos,
    has_bad_labels: bool,
    invalidated: bool,
}

const MM_VALID_SPACES: u64 = (1u64 << 9) | (1u64 << 10) | (1u64 << 12) | (1u64 << 13) |
    (1u64 << 32);

fn is_mm_space_c0(byte: u8) -> bool {
    (MM_VALID_SPACES & (1u64 << byte)) != 0
}

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

    fn get_comment(&mut self, opener: Span, mid_statement: bool) -> CommentType {
        let mut ctype = CommentType::Normal;
        let mut first = true;
        while let Some(tok) = self.get_raw() {
            let tok_ref = tok.as_ref(self.buffer);
            if tok_ref == b"$)" {
                return ctype
            } else if tok_ref == b"$j" || tok_ref == b"$t" {
                if !first {
                    self.diagnostics.push(Diagnostic::CommentMarkerNotStart(tok))
                } else if mid_statement {
                    self.diagnostics.push(Diagnostic::MidStatementCommentMarker(tok))
                } else {
                    if tok_ref == b"$j" {
                        ctype = CommentType::Extra;
                    } else {
                        ctype = CommentType::Typesetting;
                    }
                }
            } else if tok_ref.contains(&b'$') {
                let tok_str = str::from_utf8(tok_ref).unwrap();
                if tok_str.contains("$)") {
                    self.diagnostics.push(Diagnostic::BadCommentEnd(tok, opener));
                }
                if tok_str.contains("$()") {
                    self.diagnostics.push(Diagnostic::NestedComment(tok, opener));
                }
            }

            first = false;
        }

        let cspan = Span::new2(opener.start, self.buffer.len() as FilePos);
        self.diagnostics.push(Diagnostic::UnclosedComment(cspan));
        ctype
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

    fn out_statement(&mut self, stype: StatementType, label: Span, math: Vec<Span>, proof: Vec<Span>) -> Statement {
        Statement {
            stype: stype, label: label, math: math, proof: proof,
            group: NO_STATEMENT, group_end: NO_STATEMENT,
            diagnostics: mem::replace(&mut self.diagnostics, Vec::new()),
            span: Span::new2(mem::replace(&mut self.statement_start, self.position), self.position),
        }
    }

    fn get_comment_statement(&mut self) -> Option<Statement> {
        if let Some(ftok) = self.get_raw() {
            let ftok_ref = ftok.as_ref(self.buffer);
            if ftok_ref == b"$(" {
                let ctype = self.get_comment(ftok, false);
                let stype = if ctype == CommentType::Typesetting {
                    TypesettingComment
                } else {
                    Comment
                };
                return Some(self.out_statement(stype, Span::null(), Vec::new(), Vec::new()));
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
            if lref.contains(&b'$') {
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
        for &lspan in &self.labels {
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
            for &addl in self.labels.iter().skip(1) {
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
            if toknref.contains(&b'$') {
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
                    self.unget = Some(tokn);
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
        };
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
            } else if tref.contains(&b'$') {
                // might be the start of the next statement
                self.unget = Some(tok);
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
                } else if res.as_ref(self.buffer).contains(&b'$') {
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

        let mut stype = Eof;
        if let Some(kwtok) = self.get() {
            let kwtok_ref = kwtok.as_ref(self.buffer);
            stype = if kwtok_ref.len() == 2 && kwtok_ref[0] == b'$' {
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
            };
            if stype == Invalid {
                self.diagnostics.push(Diagnostic::UnknownKeyword(kwtok));
            }
        }
        self.invalidated = false;

        let mut label = if stype.takes_label() {
            self.get_label()
        } else {
            self.get_no_label();
            Span::null()
        };

        let (math, proof) = if stype.takes_math() {
            self.get_strings(stype == Provable)
        } else {
            (Vec::new(), Vec::new())
        };

        match stype {
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
                    self.diagnostics.push(Diagnostic::BadFloating);
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
            stype = Invalid;
        }

        self.out_statement(stype, label, math, proof)
    }

    fn get_segment(&mut self) -> Segment {
        let mut seg = Segment {
            statements: Vec::new(), next_file: Span::null(),
            symbols: Vec::new(), global_dvs: Vec::new(), labels: Vec::new(),
            floats: Vec::new(), buffer: self.buffer_ref.clone(),
        };
        let mut top_group = NO_STATEMENT;
        let end_diag;

        loop {
            let index = seg.statements.len() as StatementIndex;
            let mut stmt = self.get_statement();
            stmt.group = top_group;
            seg.statements.push(stmt);

            // TODO record name usage
            match seg.statements[index as usize].stype {
                OpenGroup => {
                    top_group = index;
                }
                CloseGroup => {
                    if top_group == NO_STATEMENT {
                        seg.statements[index as usize].diagnostics.push(Diagnostic::UnmatchedCloseGroup);
                    } else {
                        seg.statements[top_group as usize].group_end = index;
                        top_group = seg.statements[top_group as usize].group;
                    }
                }
                Constant => {
                    if top_group != NO_STATEMENT {
                        seg.statements[index as usize].diagnostics.push(Diagnostic::ConstantNotTopLevel);
                    }
                }
                Essential => {
                    if top_group != NO_STATEMENT {
                        seg.statements[index as usize].diagnostics.push(Diagnostic::EssentialNotTopLevel);
                    }
                }
                FileInclude => {
                    seg.next_file = seg.statements[index as usize].label;
                    end_diag = Diagnostic::UnclosedBeforeInclude(index);
                    break;
                }
                Eof => {
                    end_diag = Diagnostic::UnclosedBeforeEof;
                    break;
                }
                _ => {}
            }
        }

        while top_group != NO_STATEMENT {
            seg.statements[top_group as usize].group_end =
                seg.statements.len() as StatementIndex;
            seg.statements[top_group as usize].diagnostics.push(end_diag.clone());
            top_group = seg.statements[top_group as usize].group;
        }

        for index in 0 .. seg.statements.len() {
            if seg.statements[index].group != NO_STATEMENT && seg.statements[index].stype != OpenGroup {
                seg.statements[index].group_end = seg.statements[seg.statements[index].group as usize].group_end;
            }
        }

        collect_definitions(&mut seg);
        seg
    }
}

fn collect_definitions(seg: &mut Segment) {
    let buf: &[u8] = &seg.buffer;
    for (index, &ref stmt) in seg.statements.iter().enumerate() {
        let index = index as StatementIndex;
        if stmt.stype.takes_label() {
            seg.labels.push(LabelDef {
                index: index, label: stmt.label.as_ref(buf).to_owned()
            });
        }

        if stmt.group_end != NO_STATEMENT {
            continue;
        }

        match stmt.stype {
            Constant => {
                for (sindex, &span) in stmt.math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Constant,
                        start: index, name: span.as_ref(buf).to_owned(),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Variable => {
                for (sindex, &span) in stmt.math.iter().enumerate() {
                    seg.symbols.push(SymbolDef {
                        stype: SymbolType::Variable,
                        start: index, name: span.as_ref(buf).to_owned(),
                        ordinal: sindex as TokenIndex,
                    });
                }
            }
            Disjoint => {
                seg.global_dvs.push(GlobalDv {
                    start: index,
                    vars: stmt.math.iter().map(|sp| sp.as_ref(buf).to_owned()).collect(),
                });
            }
            Floating => {
                seg.floats.push(FloatDef {
                    start: index,
                    typecode: stmt.math[0].as_ref(buf).to_owned(),
                    label: stmt.label.as_ref(buf).to_owned(),
                    name: stmt.math[1].as_ref(buf).to_owned(),
                });
            }
            _ => {}
        }
    }
}

fn is_valid_label(label: &[u8]) -> bool {
    for &c in label {
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
    let mut scanner = Scanner { buffer_ref: input.clone(), buffer: input, ..Scanner::default() };
    assert!(input.len() < FilePos::max_value() as usize);

    loop {
        let seg = scanner.get_segment();
        let last = seg.next_file == Span::null();
        closed_spans.push(seg);
        if last {
            return closed_spans;
        }
    }
}
