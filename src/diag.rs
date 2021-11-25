//! Datatypes to represent diagnostics emitted by smetamath analysis passes.
//!
//! This includes an enum-based representation suited for programmatic
//! interpretation and testing, as well as a mostly-text representation which
//! can be used for various human-readable outputs.

use annotate_snippets::display_list::FormatOptions;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation};
use crate::line_cache::LineCache;
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
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Display;
use std::io;
use strfmt::strfmt;

/// List of passes that generate diagnostics, for use with the
/// `Database::diag_notations` filter.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
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
/// handled by `to_annotations`.
#[derive(Debug, Clone, Eq, PartialEq)]
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
    FormulaVerificationFailed,
    GrammarAmbiguous(StatementAddress),
    GrammarCantBuild,
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

/// Converts a collection of raw diagnostics to a notation list before output.
#[must_use]
pub(crate) fn to_annotations<'a>(
    sset: &'a SegmentSet,
    lc: &mut LineCache,
    mut diags: Vec<(StatementAddress, Diagnostic)>,
) -> Vec<Snippet<'a>> {
    diags.sort_by(|x, y| sset.order.cmp(&x.0, &y.0));
    let mut out = Vec::new();
    for (saddr, diag) in diags {
        out.push(annotate_diagnostic(sset, sset.statement(saddr), lc, &diag));
    }
    out
}

/// Converts a raw diagnostics to a snippet
#[must_use]
pub fn make_snippet(
    slices: Vec<Slice<'_>>,
) -> Snippet<'_> {
    Snippet {
        title: Some(Annotation {
            label: None,
            id: None,
            annotation_type: slices[0].annotations[0].annotation_type,
        }),
        footer: vec![],
        slices,
        opt: FormatOptions {
            color: true,
            ..FormatOptions::default()
        },
    }
}

/// Creates a `Slice` containing a diagnostic annotation.
/// 
/// # Arguments
///
/// * `source` - Reference to source data, including the filename and text which could be
/// used to calculate line numbers or print an invalid excerpt.
/// * `message` - A message for the diagnostic, which may contain `{placeholders}`.  The
/// message will be in English but, being not dynamically generated, it is
/// suitable for remapping with a resource file.
/// * `span` - The location of the error (byte offset within the SourceInfo; _this is
/// not the same as the byte offset in the file_).
/// * `annotation_type` -  Severity level of the message
/// * `args` - Values to substitute for the `{placeholders}` in the message.  `String`
/// could be replaced with a richer enum.
/// * `lc` - A helper struct for keeping track of line numbers in the source file
fn make_slice<'a>(
    source: &'a SourceInfo,
    message: &'static str,
    span: Span,
    annotation_type: AnnotationType,
    args: Vec<(&'static str, String)>,
    lc: &mut LineCache,
) -> Slice<'a> {
    let mut vars = HashMap::new();
    for (name, value) in args { vars.insert(name.to_string(), value); }
    let label = strfmt(&message, &vars).unwrap().as_str();
    let offs = (span.start + source.span.start) as usize;
    let (_, col) = lc.from_offset(&source.text, offs);
    let line_end = LineCache::line_end(&source.text, offs);
    let end_offs = (span.end + source.span.start) as usize;
    let line_start = offs - (col - 1) as usize;
    Slice {
        source: as_str(&source.text[line_start..line_end]),
        line_start: 0,
        origin: Some(source.name.as_str()),
        annotations: vec![
            SourceAnnotation {
                label,
                annotation_type,
                range: (offs - line_start, end_offs - line_start),
            },
        ],
        fold: false,
    }
}

fn annotate_diagnostic<'a>(
    sset: &'a SegmentSet,
    stmt: StatementRef<'a>,
    lc: &mut LineCache,
    diag: &Diagnostic,
) -> Snippet<'a> {
    fn d<V: Display>(v: V) -> String {
        format!("{}", v)
    }

    fn t(v: &Token) -> String {
        as_str(v).to_owned()
    }

    #[derive(Clone)]
    struct AnnInfo<'a> {
        sset: &'a SegmentSet,
        stmt: StatementRef<'a>,
        annotation_type: AnnotationType,
        s: &'static str,
        args: Vec<(&'static str, String)>,
    }

    let mut slices = vec![];
    let mut info = AnnInfo {
        sset,
        stmt,
        annotation_type: AnnotationType::Error,
        s: "",
        args: Vec::new(),
    };

    let mut ann = |info: AnnInfo<'a>, mut span: Span| {
        if span.is_null() {
            span = info.stmt.span();
        }
        slices.push(make_slice(
            sset.source_info(info.stmt.segment().id).borrow(),
            info.s,
            span,
            info.annotation_type,
            info.args,
            lc,
        ));
    };

    match *diag {
        BadCharacter(span, byte) => {
            info.s = "Invalid character (byte value {byte}); Metamath source files are limited to \
                      US-ASCII with controls TAB, CR, LF, FF)";
            info.args.push(("byte", d(byte)));
            ann(info, Span::new(span, span + 1));
        }
        BadCommentEnd(tok, opener) => {
            let mut info2 = info.clone();
            info.s = "$) sequence must be surrounded by whitespace to end a comment";
            info.annotation_type = AnnotationType::Warning;
            ann(info, tok);
            info2.s = "Comment started here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, opener);
        }
        BadExplicitLabel(ref tok) => {
            info.s = "Explicit label {label} does not refer to a hypothesis of the parent step";
            info.args.push(("label", t(tok)));
            ann(info, stmt.span());
        }
        BadFloating => {
            info.s = "A $f statement must have exactly two math tokens";
            ann(info, stmt.span());
        }
        BadLabel(lbl) => {
            info.s = "Statement labels may contain only alphanumeric characters and - _ .";
            ann(info, lbl);
        }
        ChainBackref(span) => {
            info.s = "Backreference steps are not permitted to have local labels";
            ann(info, span);
        }
        CommentMarkerNotStart(marker) => {
            info.s = "This comment marker must be the first token in the comment to be effective";
            info.annotation_type = AnnotationType::Warning;
            ann(info, marker);
        }
        ConstantNotTopLevel => {
            info.s = "$c statements are not allowed in nested groups";
            ann(info, stmt.span());
        }
        DisjointSingle => {
            info.s = "A $d statement which lists only one variable is meaningless";
            info.annotation_type = AnnotationType::Warning;
            ann(info, stmt.span());
        }
        DjNotVariable(index) => {
            info.s = "$d constraints are not applicable to constants";
            ann(info, stmt.math_span(index));
        }
        DjRepeatedVariable(index1, index2) => {
            let mut info2 = info.clone();
            info.s = "A variable may not be used twice in the same $d constraint";
            ann(info, stmt.math_span(index1));
            info2.s = "Previous appearance was here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, stmt.math_span(index2));
        }
        DuplicateExplicitLabel(ref tok) => {
            info.s = "Explicit label {label} is used twice in the same step";
            info.args.push(("label", t(tok)));
            ann(info, stmt.span());
        }
        DuplicateLabel(prevstmt) => {
            let mut info2 = info.clone();
            info.s = "Statement labels must be unique";
            ann(info, stmt.span());
            info2.stmt = sset.statement(prevstmt);
            info2.s = "Label was previously used here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, Span::NULL);
        }
        EmptyFilename => {
            info.s = "Filename included by a $[ directive must not be empty";
            ann(info, stmt.span());
        }
        EmptyMathString => {
            info.s = "A math string must have at least one token";
            ann(info, stmt.span());
        }
        EssentialAtTopLevel => {
            info.s = "$e statements must be inside scope brackets, not at the top level";
            ann(info, stmt.span());
        }
        ExprNotConstantPrefix(index) => {
            info.s = "The math string of an $a, $e, or $p assertion must start with a constant, \
                     not a variable";
            ann(info, stmt.math_span(index));
        }
        FilenameDollar => {
            info.s = "Filenames included by $[ are not allowed to contain the $ character";
            ann(info, stmt.span());
        }
        FilenameSpaces => {
            info.s = "Filenames included by $[ are not allowed to contain whitespace";
            ann(info, stmt.span());
        }
        FloatNotConstant(index) => {
            info.s = "The first token of a $f statement must be a declared constant (typecode)";
            ann(info, stmt.math_span(index));
        }
        FloatNotVariable(index) => {
            info.s = "The second token of a $f statement must be a declared variable (to \
                     associate the type)";
            ann(info, stmt.math_span(index));
        }
        FloatRedeclared(saddr) => {
            let mut info2 = info.clone();
            info.s = "There is already an active $f for this variable";
            ann(info, stmt.span());
            info2.stmt = sset.statement(saddr);
            info2.s = "Previous $f was here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, Span::NULL);
        }
        FormulaVerificationFailed => {
            info.s = "Formula verification failed at this symbol";
            ann(info, stmt.span());
        }
        GrammarAmbiguous(prevstmt) => {
            let mut info2 = info.clone();
            info.s = "Grammar is ambiguous; ";
            ann(info, stmt.span());
            info2.stmt = sset.statement(prevstmt);
            info2.s = "Collision with this statement:";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, Span::NULL);
        }
        GrammarCantBuild => {
            info.s = "Can't build the grammar";
            ann(info, stmt.span());
        }
        GrammarProvableFloat => {
            info.s = "Floating declaration of provable type";
            ann(info, stmt.span());
        }
        IoError(ref err) => {
            info.s = "Source file could not be read (error: {error})";
            info.args.push(("error", err.clone()));
            ann(info, Span::NULL);
        }
        LocalLabelAmbiguous(span) => {
            info.s = "Local label conflicts with the name of an existing statement";
            ann(info, span);
        }
        LocalLabelDuplicate(span) => {
            info.s = "Local label duplicates another label in the same proof";
            ann(info, span);
        }
        MalformedAdditionalInfo(span) => {
            info.s = "Malformed additional information";
            ann(info, span);
        }
        MidStatementCommentMarker(marker) => {
            info.s = "Marked comments are only effective between statements, not inside them";
            info.annotation_type = AnnotationType::Warning;
            ann(info, marker);
        }
        MissingLabel => {
            info.s = "This statement type requires a label";
            ann(info, stmt.span());
        }
        MissingProof(math_end) => {
            info.s = "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                     if you do not have a proof yet";
            ann(info, math_end);
        }
        NestedComment(tok, opener) => {
            let mut info2 = info.clone();
            info.s = "Nested comments are not supported - comment will end at the first $)";
            info.annotation_type = AnnotationType::Warning;
            ann(info, tok);
            info2.s = "Comment started here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, opener);
        }
        NotActiveSymbol(index) => {
            info.s = "Token used here must be active in the current scope";
            ann(info, stmt.math_span(index));
        }
        NotAProvableStatement => {
            info.s = "Statement does not start with the provable constant type";
            ann(info, stmt.span());
        }
        ParsedStatementNoTypeCode => {
            info.s = "Empty statement";
            ann(info, stmt.span());
        }
        ParsedStatementTooShort(ref tok) => {
            info.s = "Statement is too short, expecting for example {expected}";
            info.args.push(("expected", t(tok)));
            ann(info, stmt.span());
        }
        ParsedStatementWrongTypeCode(ref found) => {
            info.s = "Type code {found} is not among the expected type codes";
            info.args.push(("found", t(found)));
            ann(info, stmt.span());
        }
        ProofDvViolation => {
            info.s = "Disjoint variable constraint violated";
            ann(info, stmt.span());
        }
        ProofExcessEnd => {
            info.s = "Must be exactly one statement on stack at end of proof";
            ann(info, stmt.span());
        }
        ProofIncomplete => {
            info.s = "Proof is incomplete";
            info.annotation_type = AnnotationType::Warning;
            ann(info, stmt.span());
        }
        ProofInvalidSave => {
            info.s = "Z must appear immediately after a complete step integer";
            ann(info, stmt.span());
        }
        ProofMalformedVarint => {
            info.s = "Proof step number too long or missing terminator";
            ann(info, stmt.span());
        }
        ProofNoSteps => {
            info.s = "Proof must have at least one step (use ? if deliberately incomplete)";
            ann(info, stmt.span());
        }
        ProofUnderflow => {
            info.s = "Too few statements on stack to satisfy step's mandatory hypotheses";
            ann(info, stmt.span());
        }
        ProofUnterminatedRoster => {
            info.s = "List of referenced assertions in a compressed proof must be terminated by )";
            ann(info, stmt.span());
        }
        ProofWrongExprEnd => {
            info.s = "Final step statement does not match assertion";
            ann(info, stmt.span());
        }
        ProofWrongTypeEnd => {
            info.s = "Final step typecode does not match assertion";
            ann(info, stmt.span());
        }
        RepeatedLabel(l_span, f_span) => {
            let mut info2 = info.clone();
            info.s = "A statement may have only one label";
            ann(info, l_span);
            info2.s = "First label was here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, f_span);
        }
        SpuriousLabel(lspan) => {
            info.s = "Labels are only permitted for statements of type $a, $e, $f, or $p";
            ann(info, lspan);
        }
        SpuriousProof(math_end) => {
            info.s = "Proofs are only allowed on $p assertions";
            ann(info, math_end);
        }
        StepEssenWrong => {
            info.s = "Step used for $e hypothesis does not match statement";
            ann(info, stmt.span());
        }
        StepEssenWrongType => {
            info.s = "Step used for $e hypothesis does not match typecode";
            ann(info, stmt.span());
        }
        StepFloatWrongType => {
            info.s = "Step used for $f hypothesis does not match typecode";
            ann(info, stmt.span());
        }
        StepMissing(ref tok) => {
            info.s = "Step {step} referenced by proof does not correspond to a $p statement (or \
                      is malformed)";
            info.args.push(("step", t(tok)));
            ann(info, stmt.span());
        }
        StepOutOfRange => {
            info.s = "Step in compressed proof is out of range of defined steps";
            ann(info, stmt.span());
        }
        StepUsedAfterScope(ref tok) => {
            info.s = "Step {step} referenced by proof is a hypothesis not active in this scope";
            info.args.push(("step", t(tok)));
            ann(info, stmt.span());
        }
        StepUsedBeforeDefinition(ref tok) => {
            info.s = "Step {step} referenced by proof has not yet been proved";
            info.args.push(("step", t(tok)));
            ann(info, stmt.span());
        }
        SymbolDuplicatesLabel(index, saddr) => {
            let mut info2 = info.clone();
            info.s = "Metamath spec forbids symbols which are the same as labels in the same \
                     database";
            info.annotation_type = AnnotationType::Warning;
            ann(info, stmt.math_span(index));
            info2.stmt = sset.statement(saddr);
            info2.s = "Symbol was used as a label here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, Span::NULL);
        }
        SymbolRedeclared(index, taddr) => {
            let mut info2 = info.clone();
            info.s = "This symbol is already active in this scope";
            ann(info, stmt.math_span(index));
            info2.stmt = sset.statement(taddr.statement);
            info2.s = "Symbol was previously declared here";
            info2.annotation_type = AnnotationType::Note;
            let sp = info2.stmt.math_span(taddr.token_index);
            ann(info2, sp);
        }
        UnclosedBeforeEof => {
            info.s = "${ group must be closed with a $} before end of file";
            ann(info, stmt.span());
        }
        UnclosedBeforeInclude(index) => {
            let mut info2 = info.clone();
            info.s = "${ group must be closed with a $} before another file can be included";
            ann(info, stmt.span());
            info2.stmt = stmt.segment().statement(index);
            info2.s = "Include statement is here";
            info2.annotation_type = AnnotationType::Note;
            ann(info2, Span::NULL);
        }
        UnclosedComment(comment) => {
            info.s = "Comment requires closing $) before end of file";
            ann(info, comment);
        }
        UnclosedInclude => {
            info.s = "$[ requires a matching $]";
            ann(info, stmt.span());
        }
        UnclosedMath => {
            info.s = "A math string must be closed with $= or $.";
            ann(info, stmt.span());
        }
        UnclosedProof => {
            info.s = "A proof must be closed with $.";
            ann(info, stmt.span());
        }
        UnknownKeyword(kwspan) => {
            info.s = "Statement-starting keyword must be one of $a $c $d $e $f $p $v";
            ann(info, kwspan);
        }
        UnmatchedCloseGroup => {
            info.s = "This $} does not match any open ${";
            ann(info, stmt.span());
        }
        UnparseableStatement(index) => {
            info.s = "Could not parse this statement";
            ann(info, stmt.math_span(index));
        }
        VariableMissingFloat(index) => {
            info.s = "Variable token used in statement must have an active $f";
            ann(info, stmt.math_span(index));
        }
        VariableRedeclaredAsConstant(index, taddr) => {
            let mut info2 = info.clone();
            info.s = "Symbol cannot be used as a variable here and as a constant later";
            ann(info, stmt.math_span(index));
            info2.stmt = sset.statement(taddr.statement);
            info2.s = "Symbol will be used as a constant here";
            let sp = info2.stmt.math_span(taddr.token_index);
            info2.annotation_type = AnnotationType::Note;
            ann(info2, sp);
        }
    };

    make_snippet(slices)
}
