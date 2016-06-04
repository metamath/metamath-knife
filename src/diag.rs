use parser::{Comparer, Span, StatementIndex, StatementAddress, StatementRef, SourceInfo, Token,
             TokenIndex, TokenAddress};
use segment_set::SegmentSet;
use std::fmt::Display;
use std::sync::Arc;

#[derive(Debug,Clone,Eq,PartialEq)]
pub enum Diagnostic {
    BadCharacter(Span, u8),
    BadCommentEnd(Span, Span),
    BadFloating,
    BadLabel(Span),
    CommentMarkerNotStart(Span),
    ConstantNotTopLevel,
    DisjointSingle,
    DjNotVariable(TokenIndex),
    DjRepeatedVariable(TokenIndex, TokenIndex),
    DuplicateLabel(StatementAddress),
    EmptyFilename,
    EmptyMathString,
    EssentialAtTopLevel,
    ExprNotConstantPrefix(TokenIndex),
    FilenameDollar,
    FilenameSpaces,
    FloatNotConstant(TokenIndex),
    FloatNotVariable(TokenIndex),
    FloatRedeclared(StatementAddress),
    IoError(String),
    MidStatementCommentMarker(Span),
    MissingLabel,
    MissingProof(Span),
    NestedComment(Span, Span),
    NotActiveSymbol(TokenIndex),
    ProofDvViolation,
    ProofExcessEnd,
    ProofIncomplete,
    ProofInvalidSave,
    ProofMalformedVarint,
    ProofNoSteps,
    ProofUnderflow,
    ProofUnterminatedRoster,
    ProofWrongExprEnd,
    ProofWrongTypeEnd,
    RepeatedLabel(Span, Span),
    SpuriousLabel(Span),
    SpuriousProof(Span),
    StepEssenWrong,
    StepEssenWrongType,
    StepFloatWrongType,
    StepMissing(Token),
    StepOutOfRange,
    StepUsedAfterScope(Token),
    StepUsedBeforeDefinition(Token),
    SymbolDuplicatesLabel(TokenIndex, StatementAddress),
    SymbolRedeclared(TokenIndex, TokenAddress),
    UnclosedBeforeEof,
    UnclosedBeforeInclude(StatementIndex),
    UnclosedComment(Span),
    UnclosedInclude,
    UnclosedMath,
    UnclosedProof,
    UnknownKeyword(Span),
    UnmatchedCloseGroup,
    VariableMissingFloat(TokenIndex),
    VariableRedeclaredAsConstant(TokenIndex, TokenAddress),
}

#[derive(Debug)]
pub enum Level {
    Note,
    Warning,
    Error,
}
use self::Level::*;

pub struct Notation {
    pub source: Arc<SourceInfo>,
    pub message: &'static str,
    pub span: Span,
    pub level: Level,
    pub args: Vec<(&'static str, String)>,
}

pub fn to_annotations(sset: &SegmentSet,
                      mut diags: Vec<(StatementAddress, Diagnostic)>)
                      -> Vec<Notation> {
    diags.sort_by(|x, y| sset.order.cmp(&x.0, &y.0));
    let mut out = Vec::new();
    for (saddr, diag) in diags {
        annotate_diagnostic(&mut out, sset, sset.statement(saddr), &diag);
    }
    out
}

fn annotate(notes: &mut Vec<Notation>,
            stmt: StatementRef,
            message: &'static str,
            span: Span,
            level: Level,
            args: Vec<(&'static str, String)>) {
    notes.push(Notation {
        source: stmt.segment.segment.source.clone(),
        message: message,
        span: span,
        level: level,
        args: args,
    })
}

fn annotate_diagnostic(notes: &mut Vec<Notation>,
                       sset: &SegmentSet,
                       stmt: StatementRef,
                       diag: &Diagnostic) {
    use self::Diagnostic::*;
    fn d<V: Display>(v: V) -> String {
        format!("{}", v)
    }

    fn t(v: &Token) -> String {
        String::from_utf8(v.to_owned()).expect("utf-8 is checked before making Token")
    }

    match *diag {
        BadCharacter(span, byte) => {
            let s = "Invalid character (byte value {byte}); Metamath source files are limited to \
                     US-ASCII with controls TAB, CR, LF, FF)";
            annotate(notes, stmt, s, span, Error, vec![("byte", d(byte))]);
        }
        BadCommentEnd(tok, opener) => {
            let s = "$) sequence must be surrounded by whitespace to end a comment";
            annotate(notes, stmt, s, tok, Warning, Vec::new());
            let s = "Comment started here";
            annotate(notes, stmt, s, opener, Note, Vec::new());
        }
        BadFloating => {
            let s = "A $f statement must have exactly two math tokens";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        BadLabel(lbl) => {
            let s = "Statement labels may contain only alphanumeric characters and - _ .";
            annotate(notes, stmt, s, lbl, Error, Vec::new());
        }
        CommentMarkerNotStart(marker) => {
            let s = "This comment marker must be the first token in the comment to be effective";
            annotate(notes, stmt, s, marker, Warning, Vec::new());
        }
        ConstantNotTopLevel => {
            let s = "$c statements are not allowed in nested groups";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        DisjointSingle => {
            let s = "A $d statement which lists only one variable is meaningless";
            annotate(notes, stmt, s, stmt.span(), Warning, Vec::new());
        }
        DjNotVariable(index) => {
            let s = "$d constraints are not applicable to constants";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        DjRepeatedVariable(index1, index2) => {
            let s = "A variable may not be used twice in the same $d constraint";
            annotate(notes, stmt, s, stmt.math_span(index1), Error, Vec::new());
            let s = "Previous appearance was here";
            annotate(notes, stmt, s, stmt.math_span(index2), Note, Vec::new());
        }
        DuplicateLabel(prevstmt) => {
            let s = "Statement labels must be unique";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
            let stmt2 = sset.statement(prevstmt);
            let s = "Label was previously used here";
            annotate(notes, stmt2, s, stmt2.span(), Note, Vec::new());
        }
        EmptyFilename => {
            let s = "Filename included by a $[ directive must not be empty";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        EmptyMathString => {
            let s = "A math string must have at least one token";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        EssentialAtTopLevel => {
            let s = "$e statements must be inside scope brackets, not at the top level";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        ExprNotConstantPrefix(index) => {
            let s = "The math string of an $a, $e, or $p assertion must start with a constant, \
                     not a variable";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        FilenameDollar => {
            let s = "Filenames included by $[ are not allowed to contain the $ character";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        FilenameSpaces => {
            let s = "Filenames included by $[ are not allowed to contain whitespace";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        FloatNotConstant(index) => {
            let s = "The first token of a $f statement must be a declared constant (typecode)";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        FloatNotVariable(index) => {
            let s = "The second token of a $f statement must be a declared variable (to \
                     associate the type)";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        FloatRedeclared(saddr) => {
            let s = "There is already an active $f for this variable";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
            let stmt2 = sset.statement(saddr);
            let s = "Previous $f was here";
            annotate(notes, stmt2, s, stmt2.span(), Note, Vec::new());
        }
        IoError(ref err) => {
            let s = "Source file could not be read (error: {error})";
            let p = vec![("error", err.clone())];
            annotate(notes, stmt, s, stmt.span(), Error, p);
        }
        MidStatementCommentMarker(marker) => {
            let s = "Marked comments are only effective between statements, not inside them";
            annotate(notes, stmt, s, marker, Warning, Vec::new());
        }
        MissingLabel => {
            let s = "This statement type requires a label";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        MissingProof(math_end) => {
            let s = "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                     if you do not have a proof yet";
            annotate(notes, stmt, s, math_end, Error, Vec::new());
        }
        NestedComment(tok, opener) => {
            let s = "Nested comments are not supported - comment will end at the first $)";
            annotate(notes, stmt, s, tok, Warning, Vec::new());
            let s = "Comment started here";
            annotate(notes, stmt, s, opener, Note, Vec::new());
        }
        NotActiveSymbol(index) => {
            let s = "Token used here must be active in the current scope";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        ProofDvViolation => {
            let s = "Disjoint variable constraint violated";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofExcessEnd => {
            let s = "Must be exactly one statement on stack at end of proof";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofIncomplete => {
            let s = "Proof is incomplete";
            annotate(notes, stmt, s, stmt.span(), Warning, vec![]);
        }
        ProofInvalidSave => {
            let s = "Z must appear immediately after a complete step integer";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofMalformedVarint => {
            let s = "Proof step number too long or missing terminator";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofNoSteps => {
            let s = "Proof must have at least one step (use ? if deliberately incomplete)";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofUnderflow => {
            let s = "Too few statements on stack to satisfy step's mandatory hypotheses";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofUnterminatedRoster => {
            let s = "List of referenced assertions in a compressed proof must be terminated by )";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofWrongExprEnd => {
            let s = "Final step statement does not match assertion";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        ProofWrongTypeEnd => {
            let s = "Final step typecode does not match assertion";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        RepeatedLabel(lspan, fspan) => {
            let s = "A statement may have only one label";
            annotate(notes, stmt, s, lspan, Error, Vec::new());
            annotate(notes, stmt, "First label was here", fspan, Note, Vec::new());
        }
        SpuriousLabel(lspan) => {
            let s = "Labels are only permitted for statements of type $a, $e, $f, or $p";
            annotate(notes, stmt, s, lspan, Error, Vec::new());
        }
        SpuriousProof(math_end) => {
            let s = "Proofs are only allowed on $p assertions";
            annotate(notes, stmt, s, math_end, Error, Vec::new());
        }
        StepEssenWrong => {
            let s = "Step used for $e hypothesis does not match statement";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        StepEssenWrongType => {
            let s = "Step used for $e hypothesis does not match typecode";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        StepFloatWrongType => {
            let s = "Step used for $f hypothesis does not match typecode";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        StepMissing(ref tok) => {
            let s = "Step {step} referenced by proof does not correspond to a $p statement (or is \
                     malformed)";
            annotate(notes, stmt, s, stmt.span(), Error, vec![("step", t(tok))]);
        }
        StepOutOfRange => {
            let s = "Step in compressed proof is out of range of defined steps";
            annotate(notes, stmt, s, stmt.span(), Error, vec![]);
        }
        StepUsedAfterScope(ref tok) => {
            let s = "Step {step} referenced by proof is a hypothesis not active in this scope";
            annotate(notes, stmt, s, stmt.span(), Error, vec![("step", t(tok))]);
        }
        StepUsedBeforeDefinition(ref tok) => {
            let s = "Step {step} referenced by proof has not yet been proved";
            annotate(notes, stmt, s, stmt.span(), Error, vec![("step", t(tok))]);
        }
        SymbolDuplicatesLabel(index, saddr) => {
            let s = "Metamath spec forbids symbols which are the same as labels in the same \
                     database";
            annotate(notes, stmt, s, stmt.math_span(index), Warning, Vec::new());
            let stmt2 = sset.statement(saddr);
            let s = "Symbol was used as a label here";
            annotate(notes, stmt2, s, stmt2.span(), Note, Vec::new());
        }
        SymbolRedeclared(index, taddr) => {
            let s = "This symbol is already active in this scope";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
            let stmt2 = sset.statement(taddr.statement);
            let s = "Symbol was previously declared here";
            let sp = stmt2.math_span(taddr.token_index);
            annotate(notes, stmt2, s, sp, Note, Vec::new());
        }
        UnclosedBeforeEof => {
            let s = "${ group must be closed with a $} before end of file";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        UnclosedBeforeInclude(index) => {
            let s = "${ group must be closed with a $} before another file can be included";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
            let stmt2 = stmt.segment.statement(index);
            let s = "Include statement is here";
            annotate(notes, stmt2, s, stmt2.span(), Note, Vec::new());
        }
        UnclosedComment(comment) => {
            let s = "Comment requires closing $) before end of file";
            annotate(notes, stmt, s, comment, Error, Vec::new());
        }
        UnclosedInclude => {
            let s = "$[ requires a matching $]";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        UnclosedMath => {
            let s = "A math string must be closed with $= or $.";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        UnclosedProof => {
            let s = "A proof must be closed with $.";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        UnknownKeyword(kwspan) => {
            let s = "Statement-starting keyword must be one of $a $c $d $e $f $p $v";
            annotate(notes, stmt, s, kwspan, Error, Vec::new());
        }
        UnmatchedCloseGroup => {
            let s = "This $} does not match any open ${";
            annotate(notes, stmt, s, stmt.span(), Error, Vec::new());
        }
        VariableMissingFloat(index) => {
            let s = "Variable token used in statement must have an active $f";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
        }
        VariableRedeclaredAsConstant(index, taddr) => {
            let s = "Symbol cannot be used as a variable here and as a constant later";
            annotate(notes, stmt, s, stmt.math_span(index), Error, Vec::new());
            let stmt2 = sset.statement(taddr.statement);
            let s = "Symbol will be used as a constant here";
            let sp = stmt2.math_span(taddr.token_index);
            annotate(notes, stmt2, s, sp, Note, Vec::new());
        }
    }
}
