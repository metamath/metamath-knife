use parser::{Comparer, Span, StatementIndex, StatementAddress, StatementRef, SourceInfo,
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
    RepeatedLabel(Span, Span),
    SpuriousLabel(Span),
    SpuriousProof(Span),
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

    match *diag {
        BadCharacter(span, byte) => {
            annotate(notes,
                     stmt,
                     "Invalid character (byte value {byte}); Metamath source files are limited \
                      to US-ASCII with controls TAB, CR, LF, FF)",
                     span,
                     Error,
                     vec![("byte", d(byte))]);
        }
        BadCommentEnd(tok, opener) => {
            annotate(notes,
                     stmt,
                     "$) sequence must be surrounded by whitespace to end a comment",
                     tok,
                     Warning,
                     Vec::new());
            annotate(notes,
                     stmt,
                     "Comment started here",
                     opener,
                     Note,
                     Vec::new());
        }
        BadFloating => {
            annotate(notes,
                     stmt,
                     "A $f statement must have exactly two math tokens",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        BadLabel(lbl) => {
            annotate(notes,
                     stmt,
                     "Statement labels may contain only alphanumeric characters and - _ .",
                     lbl,
                     Error,
                     Vec::new());
        }
        CommentMarkerNotStart(marker) => {
            annotate(notes,
                     stmt,
                     "This comment marker must be the first token in the comment to be effective",
                     marker,
                     Warning,
                     Vec::new());
        }
        ConstantNotTopLevel => {
            annotate(notes,
                     stmt,
                     "$c statements are not allowed in nested groups",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        DisjointSingle => {
            annotate(notes,
                     stmt,
                     "A $d statement which lists only one variable is meaningless",
                     stmt.span(),
                     Warning,
                     Vec::new());
        }
        DjNotVariable(index) => {
            annotate(notes,
                     stmt,
                     "$d constraints are not applicable to constants",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        DjRepeatedVariable(index1, index2) => {
            annotate(notes,
                     stmt,
                     "A variable may not be used twice in the same $d constraint",
                     stmt.math_span(index1),
                     Error,
                     Vec::new());
            annotate(notes,
                     stmt,
                     "Previous appearance was here",
                     stmt.math_span(index2),
                     Note,
                     Vec::new());
        }
        DuplicateLabel(prevstmt) => {
            annotate(notes,
                     stmt,
                     "Statement labels must be unique",
                     stmt.span(),
                     Error,
                     Vec::new());
            let stmt2 = sset.statement(prevstmt);
            annotate(notes,
                     stmt2,
                     "Label was previously used here",
                     stmt2.span(),
                     Note,
                     Vec::new());
        }
        EmptyFilename => {
            annotate(notes,
                     stmt,
                     "Filename included by a $[ directive must not be empty",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        EmptyMathString => {
            annotate(notes,
                     stmt,
                     "A math string must have at least one token",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        EssentialAtTopLevel => {
            annotate(notes,
                     stmt,
                     "$e statements must be inside scope brackets, not at the top level",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        ExprNotConstantPrefix(index) => {
            annotate(notes,
                     stmt,
                     "The math string of an $a, $e, or $p assertion must start with a constant, \
                      not a variable",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        FilenameDollar => {
            annotate(notes,
                     stmt,
                     "Filenames included by $[ are not allowed to contain the $ character",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        FilenameSpaces => {
            annotate(notes,
                     stmt,
                     "Filenames included by $[ are not allowed to contain whitespace",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        FloatNotConstant(index) => {
            annotate(notes,
                     stmt,
                     "The first token of a $f statement must be a declared constant (typecode)",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        FloatNotVariable(index) => {
            annotate(notes,
                     stmt,
                     "The second token of a $f statement must be a declared variable (to \
                      associate the type)",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        FloatRedeclared(saddr) => {
            annotate(notes,
                     stmt,
                     "There is already an active $f for this variable",
                     stmt.span(),
                     Error,
                     Vec::new());
            let stmt2 = sset.statement(saddr);
            annotate(notes,
                     stmt2,
                     "Previous $f was here",
                     stmt2.span(),
                     Note,
                     Vec::new());
        }
        IoError(ref err) => {
            annotate(notes,
                     stmt,
                     "Source file could not be read (error: {error})",
                     stmt.span(),
                     Error,
                     vec![("error", err.clone())]);
        }
        MidStatementCommentMarker(marker) => {
            annotate(notes,
                     stmt,
                     "Marked comments are only effective between statements, not inside them",
                     marker,
                     Warning,
                     Vec::new());
        }
        MissingLabel => {
            annotate(notes,
                     stmt,
                     "This statement type requires a label",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        MissingProof(math_end) => {
            annotate(notes,
                     stmt,
                     "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                      if you do not have a proof yet",
                     math_end,
                     Error,
                     Vec::new());
        }
        NestedComment(tok, opener) => {
            annotate(notes,
                     stmt,
                     "Nested comments are not supported - comment will end at the first $)",
                     tok,
                     Warning,
                     Vec::new());
            annotate(notes,
                     stmt,
                     "Comment started here",
                     opener,
                     Note,
                     Vec::new());
        }
        NotActiveSymbol(index) => {
            annotate(notes,
                     stmt,
                     "Token used here must be active in the current scope",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        RepeatedLabel(lspan, fspan) => {
            annotate(notes,
                     stmt,
                     "A statement may have only one label",
                     lspan,
                     Error,
                     Vec::new());
            annotate(notes, stmt, "First label was here", fspan, Note, Vec::new());
        }
        SpuriousLabel(lspan) => {
            annotate(notes,
                     stmt,
                     "Labels are only permitted for statements of type $a, $e, $f, or $p",
                     lspan,
                     Error,
                     Vec::new());
        }
        SpuriousProof(math_end) => {
            annotate(notes,
                     stmt,
                     "Proofs are only allowed on $p assertions",
                     math_end,
                     Error,
                     Vec::new());
        }
        SymbolDuplicatesLabel(index, saddr) => {
            annotate(notes,
                     stmt,
                     "Metamath spec forbids symbols which are the same as labels in the same \
                      database",
                     stmt.math_span(index),
                     Warning,
                     Vec::new());
            let stmt2 = sset.statement(saddr);
            annotate(notes,
                     stmt2,
                     "Symbol was used as a label here",
                     stmt2.span(),
                     Note,
                     Vec::new());
        }
        SymbolRedeclared(index, taddr) => {
            annotate(notes,
                     stmt,
                     "This symbol is already active in this scope",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
            let stmt2 = sset.statement(taddr.statement);
            annotate(notes,
                     stmt2,
                     "Symbol was previously declared here",
                     stmt2.math_span(taddr.token_index),
                     Note,
                     Vec::new());
        }
        UnclosedBeforeEof => {
            annotate(notes,
                     stmt,
                     "${ group must be closed with a $} before end of file",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        UnclosedBeforeInclude(index) => {
            annotate(notes,
                     stmt,
                     "${ group must be closed with a $} before another file can be included",
                     stmt.span(),
                     Error,
                     Vec::new());
            let stmt2 = stmt.segment.statement(index);
            annotate(notes,
                     stmt2,
                     "Include statement is here",
                     stmt2.span(),
                     Note,
                     Vec::new());
        }
        UnclosedComment(comment) => {
            annotate(notes,
                     stmt,
                     "Comment requires closing $) before end of file",
                     comment,
                     Error,
                     Vec::new());
        }
        UnclosedInclude => {
            annotate(notes,
                     stmt,
                     "$[ requires a matching $]",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        UnclosedMath => {
            annotate(notes,
                     stmt,
                     "A math string must be closed with $= or $.",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        UnclosedProof => {
            annotate(notes,
                     stmt,
                     "A proof must be closed with $.",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        UnknownKeyword(kwspan) => {
            annotate(notes,
                     stmt,
                     "Statement-starting keyword must be one of $a $c $d $e $f $p $v",
                     kwspan,
                     Error,
                     Vec::new());
        }
        UnmatchedCloseGroup => {
            annotate(notes,
                     stmt,
                     "This $} does not match any open ${",
                     stmt.span(),
                     Error,
                     Vec::new());
        }
        VariableMissingFloat(index) => {
            annotate(notes,
                     stmt,
                     "Variable token used in statement must have an active $f",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
        }
        VariableRedeclaredAsConstant(index, taddr) => {
            annotate(notes,
                     stmt,
                     "Symbol cannot be used as a variable here and as a constant later",
                     stmt.math_span(index),
                     Error,
                     Vec::new());
            let stmt2 = sset.statement(taddr.statement);
            annotate(notes,
                     stmt2,
                     "Symbol will be used as a constant here",
                     stmt2.math_span(taddr.token_index),
                     Note,
                     Vec::new());
        }
    }
}
