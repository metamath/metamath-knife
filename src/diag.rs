//! Datatypes to represent diagnostics emitted by smetamath analysis passes.
//!
//! This includes an enum-based representation suited for programmatic
//! interpretation and testing, as well as a mostly-text representation which
//! can be used for various human-readable outputs.

use crate::parser::as_str;
use crate::parser::Comparer;
use crate::parser::Span;
use crate::parser::StatementAddress;
use crate::parser::StatementIndex;
use crate::parser::StatementRef;
use crate::parser::Token;
use crate::parser::TokenAddress;
use crate::parser::TokenIndex;
use crate::segment_set::SegmentSet;
use crate::segment_set::SourceInfo;
use std::fmt::Display;
use std::io;
use std::mem;
use std::sync::Arc;

/// List of passes that generate diagnostics, for use with the
/// `Database::diag_notations` filter.
#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub enum DiagnosticClass {
    /// Parse errors, which can be observed from a single statement in
    /// isolation.
    Parse,
    /// Scope errors are mostly inter-statement consistency checks which
    /// invalidate the logical interpretation of a statement.
    Scope,
    /// Verify errors do not invalidate the interpretation of statements, but
    /// affect only proofs.
    Verify,
    /// Grammar errors reflect whether the database is unambiguous
    Grammar,
    /// Statement Parsing result
    StmtParse,
}

/// List of all diagnostic codes.  For a description of each, see the source of
/// `to_annotations`.
///
/// Each diagnostic applies to precisely one statement.  Some diagnostics
/// reference statements other than the one they are attached to; the fanout is
/// handled by to_annotations.
#[derive(Debug,Clone,Eq,PartialEq)]
#[allow(missing_docs)]
pub enum Diagnostic {
    BadCharacter(usize, u8),
    BadCommentEnd(Span, Span),
    BadExplicitLabel(Token),
    BadFloating,
    BadLabel(Span),
    ChainBackref(Span),
    CommentMarkerNotStart(Span),
    ConstantNotTopLevel,
    DisjointSingle,
    DjNotVariable(TokenIndex),
    DjRepeatedVariable(TokenIndex, TokenIndex),
    DuplicateExplicitLabel(Token),
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
    GrammarAmbiguous(StatementAddress),
	GrammarProvableFloat,
    IoError(String),
    LocalLabelAmbiguous(Span),
    LocalLabelDuplicate(Span),
	MalformedAdditionalInfo(Span),
    MidStatementCommentMarker(Span),
    MissingLabel,
    MissingProof(Span),
    NestedComment(Span, Span),
    NotActiveSymbol(TokenIndex),
    NotAProvableStatement,
    ParsedStatementTooShort(Token),
    ParsedStatementNoTypeCode,
    ParsedStatementWrongTypeCode(Token),
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
    UnparseableStatement(TokenIndex),
    VariableMissingFloat(TokenIndex),
    VariableRedeclaredAsConstant(TokenIndex, TokenAddress),
}
use self::Diagnostic::*;

impl From<io::Error> for Diagnostic {
    fn from(err: io::Error) -> Diagnostic {
        IoError(format!("{}", err))
    }
}

/// An indication of the severity of a notation.
#[derive(Copy,Clone,Debug)]
pub enum Level {
    /// Notes indicate other statements relevant to an error which is primarily
    /// elsewhere.
    Note,
    /// Warnings indicate constructs which are defined by the spec but also
    /// forbidden by the spec, as well as issues with non-spec extensions.
    Warning,
    /// Errors are forbidden by the spec and invalidate the logical content of
    /// the database.
    Error,
}
use self::Level::*;

/// A notation is a human-readable description of a diagnostic, with a single
/// structure, named fields, and identifying a single source location.
pub struct Notation {
    /// Reference to source data, including the filename and text which could be
    /// used to calculate line numbers or print an invalid excerpt.
    pub source: Arc<SourceInfo>,
    /// A message for the diagnostic, which may contain `{placeholders}`.  The
    /// message will be in English but, being not dynamically generated, it is
    /// suitable for remapping with a resource file.
    pub message: &'static str,
    /// The location of the error (byte offset within the SourceInfo; _this is
    /// not the same as the byte offset in the file_).
    pub span: Span,
    /// Severity level of the message
    pub level: Level,
    /// Values to substitute for the `{placeholders}` in the message.  `String`
    /// could be replaced with a richer enum.
    pub args: Vec<(&'static str, String)>,
}

/// Converts a collection of raw diagnostics to a notation list before output.
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

fn annotate_diagnostic(notes: &mut Vec<Notation>,
                       sset: &SegmentSet,
                       stmt: StatementRef,
                       diag: &Diagnostic) {
    struct AnnInfo<'a> {
        notes: &'a mut Vec<Notation>,
        sset: &'a SegmentSet,
        stmt: StatementRef<'a>,
        level: Level,
        s: &'static str,
        args: Vec<(&'static str, String)>,
    }

    fn ann<'a>(info: &mut AnnInfo<'a>, mut span: Span) {
        if span.is_null() {
            span = info.stmt.span();
        }
        info.notes.push(Notation {
            source: info.sset.source_info(info.stmt.segment().id).clone(),
            message: info.s,
            span: span,
            level: info.level,
            args: mem::replace(&mut info.args, Vec::new()),
        })
    }

    fn d<V: Display>(v: V) -> String {
        format!("{}", v)
    }

    fn t(v: &Token) -> String {
        as_str(v).to_owned()
    }

    let mut info = AnnInfo {
        notes: notes,
        sset: sset,
        stmt: stmt,
        level: Error,
        s: "",
        args: Vec::new(),
    };

    match *diag {
        BadCharacter(span, byte) => {
            info.s = "Invalid character (byte value {byte}); Metamath source files are limited to \
                      US-ASCII with controls TAB, CR, LF, FF)";
            info.args.push(("byte", d(byte)));
            ann(&mut info, Span::new(span, span + 1));
        }
        BadCommentEnd(tok, opener) => {
            info.s = "$) sequence must be surrounded by whitespace to end a comment";
            info.level = Warning;
            ann(&mut info, tok);
            info.s = "Comment started here";
            info.level = Note;
            ann(&mut info, opener);
        }
        BadExplicitLabel(ref tok) => {
            info.s = "Explicit label {label} does not refer to a hypothesis of the parent step";
            info.args.push(("label", t(tok)));
            ann(&mut info, stmt.span());
        }
        BadFloating => {
            info.s = "A $f statement must have exactly two math tokens";
            ann(&mut info, stmt.span());
        }
        BadLabel(lbl) => {
            info.s = "Statement labels may contain only alphanumeric characters and - _ .";
            ann(&mut info, lbl);
        }
        ChainBackref(span) => {
            info.s = "Backreference steps are not permitted to have local labels";
            ann(&mut info, span);
        }
        CommentMarkerNotStart(marker) => {
            info.s = "This comment marker must be the first token in the comment to be effective";
            info.level = Warning;
            ann(&mut info, marker);
        }
        ConstantNotTopLevel => {
            info.s = "$c statements are not allowed in nested groups";
            ann(&mut info, stmt.span());
        }
        DisjointSingle => {
            info.s = "A $d statement which lists only one variable is meaningless";
            info.level = Warning;
            ann(&mut info, stmt.span());
        }
        DjNotVariable(index) => {
            info.s = "$d constraints are not applicable to constants";
            ann(&mut info, stmt.math_span(index));
        }
        DjRepeatedVariable(index1, index2) => {
            info.s = "A variable may not be used twice in the same $d constraint";
            ann(&mut info, stmt.math_span(index1));
            info.s = "Previous appearance was here";
            info.level = Note;
            ann(&mut info, stmt.math_span(index2));
        }
        DuplicateExplicitLabel(ref tok) => {
            info.s = "Explicit label {label} is used twice in the same step";
            info.args.push(("label", t(tok)));
            ann(&mut info, stmt.span());
        }
        DuplicateLabel(prevstmt) => {
            info.s = "Statement labels must be unique";
            ann(&mut info, stmt.span());
            info.stmt = sset.statement(prevstmt);
            info.s = "Label was previously used here";
            info.level = Note;
            ann(&mut info, Span::null());
        }
        EmptyFilename => {
            info.s = "Filename included by a $[ directive must not be empty";
            ann(&mut info, stmt.span());
        }
        EmptyMathString => {
            info.s = "A math string must have at least one token";
            ann(&mut info, stmt.span());
        }
        EssentialAtTopLevel => {
            info.s = "$e statements must be inside scope brackets, not at the top level";
            ann(&mut info, stmt.span());
        }
        ExprNotConstantPrefix(index) => {
            info.s = "The math string of an $a, $e, or $p assertion must start with a constant, \
                     not a variable";
            ann(&mut info, stmt.math_span(index));
        }
        FilenameDollar => {
            info.s = "Filenames included by $[ are not allowed to contain the $ character";
            ann(&mut info, stmt.span());
        }
        FilenameSpaces => {
            info.s = "Filenames included by $[ are not allowed to contain whitespace";
            ann(&mut info, stmt.span());
        }
        FloatNotConstant(index) => {
            info.s = "The first token of a $f statement must be a declared constant (typecode)";
            ann(&mut info, stmt.math_span(index));
        }
        FloatNotVariable(index) => {
            info.s = "The second token of a $f statement must be a declared variable (to \
                     associate the type)";
            ann(&mut info, stmt.math_span(index));
        }
        FloatRedeclared(saddr) => {
            info.s = "There is already an active $f for this variable";
            ann(&mut info, stmt.span());
            info.stmt = sset.statement(saddr);
            info.s = "Previous $f was here";
            info.level = Note;
            ann(&mut info, Span::null());
        }
        GrammarAmbiguous(prevstmt) => {
            info.s = "Grammar is ambiguous; ";
            ann(&mut info, stmt.span());
            info.stmt = sset.statement(prevstmt);
            info.s = "Collision with this statement:";
            info.level = Note;
            ann(&mut info, Span::null());
        }
		GrammarProvableFloat => {
            info.s = "Floating declaration of provable type";
            ann(&mut info, stmt.span());
		}
        IoError(ref err) => {
            info.s = "Source file could not be read (error: {error})";
            info.args.push(("error", err.clone()));
            ann(&mut info, Span::null());
        }
        LocalLabelAmbiguous(span) => {
            info.s = "Local label conflicts with the name of an existing statement";
            ann(&mut info, span);
        }
        LocalLabelDuplicate(span) => {
            info.s = "Local label duplicates another label in the same proof";
            ann(&mut info, span);
        }
        MalformedAdditionalInfo(span) => {
            info.s = "Malformed additional information";
            ann(&mut info, span);
        }
        MidStatementCommentMarker(marker) => {
            info.s = "Marked comments are only effective between statements, not inside them";
            info.level = Warning;
            ann(&mut info, marker);
        }
        MissingLabel => {
            info.s = "This statement type requires a label";
            ann(&mut info, stmt.span());
        }
        MissingProof(math_end) => {
            info.s = "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                     if you do not have a proof yet";
            ann(&mut info, math_end);
        }
        NestedComment(tok, opener) => {
            info.s = "Nested comments are not supported - comment will end at the first $)";
            info.level = Warning;
            ann(&mut info, tok);
            info.s = "Comment started here";
            info.level = Note;
            ann(&mut info, opener);
        }
        NotActiveSymbol(index) => {
            info.s = "Token used here must be active in the current scope";
            ann(&mut info, stmt.math_span(index));
        }
        NotAProvableStatement => {
            info.s = "Statement does not start with the provable constant type";
            ann(&mut info, stmt.span());
        }
        ParsedStatementNoTypeCode => {
            info.s = "Empty statement";
            ann(&mut info, stmt.span());
        }
        ParsedStatementTooShort(ref tok) => {
            info.s = "Statement is too short, expecting for example {expected}";
            info.args.push(("expected", t(tok)));
            ann(&mut info, stmt.span());
        }
        ParsedStatementWrongTypeCode(ref found) => {
            info.s = "Type code {found} is not among the expected type codes";
            info.args.push(("found", t(found)));
            ann(&mut info, stmt.span());
        }
        ProofDvViolation => {
            info.s = "Disjoint variable constraint violated";
            ann(&mut info, stmt.span());
        }
        ProofExcessEnd => {
            info.s = "Must be exactly one statement on stack at end of proof";
            ann(&mut info, stmt.span());
        }
        ProofIncomplete => {
            info.s = "Proof is incomplete";
            info.level = Warning;
            ann(&mut info, stmt.span());
        }
        ProofInvalidSave => {
            info.s = "Z must appear immediately after a complete step integer";
            ann(&mut info, stmt.span());
        }
        ProofMalformedVarint => {
            info.s = "Proof step number too long or missing terminator";
            ann(&mut info, stmt.span());
        }
        ProofNoSteps => {
            info.s = "Proof must have at least one step (use ? if deliberately incomplete)";
            ann(&mut info, stmt.span());
        }
        ProofUnderflow => {
            info.s = "Too few statements on stack to satisfy step's mandatory hypotheses";
            ann(&mut info, stmt.span());
        }
        ProofUnterminatedRoster => {
            info.s = "List of referenced assertions in a compressed proof must be terminated by )";
            ann(&mut info, stmt.span());
        }
        ProofWrongExprEnd => {
            info.s = "Final step statement does not match assertion";
            ann(&mut info, stmt.span());
        }
        ProofWrongTypeEnd => {
            info.s = "Final step typecode does not match assertion";
            ann(&mut info, stmt.span());
        }
        RepeatedLabel(lspan, fspan) => {
            info.s = "A statement may have only one label";
            ann(&mut info, lspan);
            info.s = "First label was here";
            info.level = Note;
            ann(&mut info, fspan);
        }
        SpuriousLabel(lspan) => {
            info.s = "Labels are only permitted for statements of type $a, $e, $f, or $p";
            ann(&mut info, lspan);
        }
        SpuriousProof(math_end) => {
            info.s = "Proofs are only allowed on $p assertions";
            ann(&mut info, math_end);
        }
        StepEssenWrong => {
            info.s = "Step used for $e hypothesis does not match statement";
            ann(&mut info, stmt.span());
        }
        StepEssenWrongType => {
            info.s = "Step used for $e hypothesis does not match typecode";
            ann(&mut info, stmt.span());
        }
        StepFloatWrongType => {
            info.s = "Step used for $f hypothesis does not match typecode";
            ann(&mut info, stmt.span());
        }
        StepMissing(ref tok) => {
            info.s = "Step {step} referenced by proof does not correspond to a $p statement (or \
                      is malformed)";
            info.args.push(("step", t(tok)));
            ann(&mut info, stmt.span());
        }
        StepOutOfRange => {
            info.s = "Step in compressed proof is out of range of defined steps";
            ann(&mut info, stmt.span());
        }
        StepUsedAfterScope(ref tok) => {
            info.s = "Step {step} referenced by proof is a hypothesis not active in this scope";
            info.args.push(("step", t(tok)));
            ann(&mut info, stmt.span());
        }
        StepUsedBeforeDefinition(ref tok) => {
            info.s = "Step {step} referenced by proof has not yet been proved";
            info.args.push(("step", t(tok)));
            ann(&mut info, stmt.span());
        }
        SymbolDuplicatesLabel(index, saddr) => {
            info.s = "Metamath spec forbids symbols which are the same as labels in the same \
                     database";
            info.level = Warning;
            ann(&mut info, stmt.math_span(index));
            info.stmt = sset.statement(saddr);
            info.s = "Symbol was used as a label here";
            info.level = Note;
            ann(&mut info, Span::null());
        }
        SymbolRedeclared(index, taddr) => {
            info.s = "This symbol is already active in this scope";
            ann(&mut info, stmt.math_span(index));
            info.stmt = sset.statement(taddr.statement);
            info.s = "Symbol was previously declared here";
            info.level = Note;
            let sp = info.stmt.math_span(taddr.token_index);
            ann(&mut info, sp);
        }
        UnclosedBeforeEof => {
            info.s = "${ group must be closed with a $} before end of file";
            ann(&mut info, stmt.span());
        }
        UnclosedBeforeInclude(index) => {
            info.s = "${ group must be closed with a $} before another file can be included";
            ann(&mut info, stmt.span());
            info.stmt = stmt.segment().statement(index);
            info.s = "Include statement is here";
            info.level = Note;
            ann(&mut info, Span::null());
        }
        UnclosedComment(comment) => {
            info.s = "Comment requires closing $) before end of file";
            ann(&mut info, comment);
        }
        UnclosedInclude => {
            info.s = "$[ requires a matching $]";
            ann(&mut info, stmt.span());
        }
        UnclosedMath => {
            info.s = "A math string must be closed with $= or $.";
            ann(&mut info, stmt.span());
        }
        UnclosedProof => {
            info.s = "A proof must be closed with $.";
            ann(&mut info, stmt.span());
        }
        UnknownKeyword(kwspan) => {
            info.s = "Statement-starting keyword must be one of $a $c $d $e $f $p $v";
            ann(&mut info, kwspan);
        }
        UnmatchedCloseGroup => {
            info.s = "This $} does not match any open ${";
            ann(&mut info, stmt.span());
        }
        UnparseableStatement(index) => {
            info.s = "Could not parse this statement";
            ann(&mut info, stmt.math_span(index));
        }
        VariableMissingFloat(index) => {
            info.s = "Variable token used in statement must have an active $f";
            ann(&mut info, stmt.math_span(index));
        }
        VariableRedeclaredAsConstant(index, taddr) => {
            info.s = "Symbol cannot be used as a variable here and as a constant later";
            ann(&mut info, stmt.math_span(index));
            info.stmt = sset.statement(taddr.statement);
            info.s = "Symbol will be used as a constant here";
            let sp = info.stmt.math_span(taddr.token_index);
            info.level = Note;
            ann(&mut info, sp);
        }
    }
}
