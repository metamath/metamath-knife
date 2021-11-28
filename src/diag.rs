//! Datatypes to represent diagnostics emitted by smetamath analysis passes.
//!
//! This includes an enum-based representation suited for programmatic
//! interpretation and testing, as well as a mostly-text representation which
//! can be used for various human-readable outputs.

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
use annotate_snippets::display_list::FormatOptions;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation};
use std::borrow::Borrow;
use std::borrow::Cow;
use std::io;
use typed_arena::Arena;

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
pub(crate) fn to_annotations<T>(
    sset: &SegmentSet,
    lc: &mut LineCache,
    mut diags: Vec<(StatementAddress, Diagnostic)>,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T + Copy,
) -> Vec<T> {
    diags.sort_by(|x, y| sset.order.cmp(&x.0, &y.0));
    diags
        .iter()
        .map(move |(saddr, diag)| {
            let stmt = sset.statement(*saddr);
            diag.to_snippet(sset, stmt, lc, f)
        })
        .collect::<Vec<_>>()
}

/// Annotation info
///
/// * `label` - A global error message for the diagnostic
/// For each annotation:
/// * `label` - The diagnostic message
/// * `annotation_type` -  Severity level of the message
/// * `span` - The location of the error (byte offset within the segment; _this is
/// not the same as the byte offset in the file_).
type AnnInfo<'a> = (
    Cow<'a, str>,
    Vec<(AnnotationType, Cow<'a, str>, StatementRef<'a>, Span)>,
);

/// Creates a `Snippet` containing a diagnostic annotation.
///
/// # Arguments
///
/// * `sset` - Reference to the segment set.
/// * `infos` - Diagnostic information to display.
/// * `lc` - A helper struct for keeping track of line numbers in the source file
/// * `f` - A function for continuation passing style (CPS)
#[must_use]
fn make_snippet<T>(
    sset: &SegmentSet,
    infos: AnnInfo<'_>,
    lc: &mut LineCache,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T,
) -> T {
    let mut slices = vec![];
    let arena: Arena<String> = Arena::new();
    for info in infos.1 {
        let (annotation_type, label, stmt, span) = info;
        let source: &SourceInfo = sset.source_info(stmt.segment().id).borrow();
        let offs = (span.start + source.span.start) as usize;
        let (line_start, col) = lc.from_offset(&source.text, offs);
        let end_offs = (span.end + source.span.start) as usize;
        let source_start = offs + 1 - col as usize;
        let source_end = LineCache::line_end(&source.text, end_offs);
        slices.push(Slice {
            source: as_str(&source.text[source_start..source_end]),
            line_start: line_start as usize,
            origin: Some(source.name.as_str()),
            annotations: vec![SourceAnnotation {
                label: arena.alloc(label.to_string()),
                annotation_type,
                range: (offs - source_start, end_offs - source_start),
            }],
            fold: true,
        });
    }
    f(Snippet {
        title: Some(Annotation {
            label: Some(&infos.0),
            id: None,
            annotation_type: slices[0].annotations[0].annotation_type,
        }),
        footer: vec![],
        slices,
        opt: FormatOptions {
            color: true,
            ..FormatOptions::default()
        },
    })
}

impl Diagnostic {
    fn to_snippet<T>(
        &self,
        sset: &SegmentSet,
        stmt: StatementRef<'_>,
        lc: &mut LineCache,
        f: impl for<'a> FnOnce(Snippet<'a>) -> T,
    ) -> T {
        fn t(v: &Token) -> String {
            as_str(v).to_owned()
        }
        let infos = match self {
            BadCharacter(pos, byte) => ("Invalid character".into(), vec![(
                AnnotationType::Error,
                format!("Invalid character (byte value {byte}); Metamath source files are limited to \
                        US-ASCII with controls TAB, CR, LF, FF)", byte = byte).into(),
                stmt,
                Span::new(*pos, *pos + 1),
            )]),
            BadCommentEnd(tok, opener) => ("Bad comment end".into(), vec![(
                AnnotationType::Warning,
                "$) sequence must be surrounded by whitespace to end a comment".into(),
                stmt,
                *tok,
            ), (
                AnnotationType::Note,
                "Comment started here".into(),
                stmt,
                *opener,
            )]),
            BadExplicitLabel(ref tok) => ("Bad explicit label".into(), vec![(
                AnnotationType::Error,
                format!("Explicit label {label} does not refer to a hypothesis of the parent step", label = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            BadFloating => ("Bad floating".into(), vec![(
                AnnotationType::Error,
                "A $f statement must have exactly two math tokens".into(),
                stmt,
                stmt.span(),
            )]),
            BadLabel(lbl) => ("Bad label".into(), vec![(
                AnnotationType::Error,
                "Statement labels may contain only alphanumeric characters and - _ .".into(),
                stmt,
                *lbl,
            )]),
            ChainBackref(span) => ("Chain backref".into(), vec![(
                AnnotationType::Error,
                "Backreference steps are not permitted to have local labels".into(),
                stmt,
                *span,
            )]),
            CommentMarkerNotStart(marker) => ("Wrong comment marker".into(), vec![(
                AnnotationType::Warning,
                "This comment marker must be the first token in the comment to be effective".into(),
                stmt,
                *marker,
            )]),
            ConstantNotTopLevel => ("Constant is not at top level".into(), vec![(
                AnnotationType::Error,
                "$c statements are not allowed in nested groups".into(),
                stmt,
                stmt.span(),
            )]),
            DisjointSingle => ("Disjoint statement with single variable".into(), vec![(
                AnnotationType::Warning,
                "A $d statement which lists only one variable is meaningless".into(),
                stmt,
                stmt.span(),
            )]),
            DjNotVariable(index) => ("Disjoint constraints are not applicable to constants".into(), vec![(
                AnnotationType::Error,
                "$d constraints are not applicable to constants".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            DjRepeatedVariable(index1, index2) => ("Variable repeated in disjoint statement".into(), vec![(
                AnnotationType::Error,
                "A variable may not be used twice in the same $d constraint".into(),
                stmt,
                stmt.math_span(*index1),
            ), (
                AnnotationType::Note,
                "Previous appearance was here".into(),
                stmt,
                stmt.math_span(*index2),
            )]),
            DuplicateExplicitLabel(ref tok) => ("Duplicate explicit label".into(), vec![(
                AnnotationType::Error,
                format!("Explicit label {label} is used twice in the same step", label = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            DuplicateLabel(prevstmt) => ("Duplicate label".into(), vec![(
                AnnotationType::Error,
                "Statement labels must be unique".into(),
                stmt,
                stmt.span(),
            ), (
                AnnotationType::Note,
                "Label was previously used here".into(),
                sset.statement(*prevstmt),
                sset.statement(*prevstmt).span(),
            )]),
            EmptyFilename => ("Empty filename".into(), vec![(
                AnnotationType::Error,
                "Filename included by a $[ directive must not be empty".into(),
                stmt,
                stmt.span(),
            )]),
            EmptyMathString => ("Empty math string".into(), vec![(
                AnnotationType::Error,
                "A math string must have at least one token".into(),
                stmt,
                stmt.span(),
            )]),
            EssentialAtTopLevel => ("Essential at top level".into(), vec![(
                AnnotationType::Error,
                "$e statements must be inside scope brackets, not at the top level".into(),
                stmt,
                stmt.span(),
            )]),
            ExprNotConstantPrefix(index) => ("Expression does not have a constant prefix".into(), vec![(
                AnnotationType::Error,
                "The math string of an $a, $e, or $p assertion must start with a constant, \
                        not a variable".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            FilenameDollar => ("Dollar in filename".into(), vec![(
                AnnotationType::Error,
                "Filenames included by $[ are not allowed to contain the $ character".into(),
                stmt,
                stmt.span(),
            )]),
            FilenameSpaces => ("Spaces in filename".into(), vec![(
                AnnotationType::Error,
                "Filenames included by $[ are not allowed to contain whitespace".into(),
                stmt,
                stmt.span(),
            )]),
            FloatNotConstant(index) => ("Typecode was not declared".into(), vec![(
                AnnotationType::Error,
                "The first token of a $f statement must be a declared constant (typecode)".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            FloatNotVariable(index) => ("Variable not declared".into(), vec![(
                AnnotationType::Error,
                "The second token of a $f statement must be a declared variable (to \
                        associate the type)".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            FloatRedeclared(saddr) => ("Float redeclared".into(), vec![(
                AnnotationType::Error,
                "There is already an active $f for this variable".into(),
                stmt,
                stmt.span(),
            ), (
                AnnotationType::Note,
                "Previous $f was here".into(),
                sset.statement(*saddr),
                sset.statement(*saddr).span(),
            )]),
            FormulaVerificationFailed => ("Formula verification failed".into(), vec![(
                AnnotationType::Error,
                "Formula verification failed at this symbol".into(),
                stmt,
                stmt.span(),
            )]),
            GrammarAmbiguous(prevstmt) => ("Grammar ambiguous".into(), vec![(
                AnnotationType::Error,
                "Grammar is ambiguous; ".into(),
                stmt,
                stmt.span(),
            ), (
                AnnotationType::Note,
                "Collision with this statement:".into(),
                sset.statement(*prevstmt),
                sset.statement(*prevstmt).span(),
            )]),
            GrammarCantBuild => ("Can't build the grammar".into(), vec![(
                AnnotationType::Error,
                "Can't build the grammar".into(),
                stmt,
                stmt.span(),
            )]),
            GrammarProvableFloat => ("Floating declaration of provable type".into(), vec![(
                AnnotationType::Error,
                "Floating declaration of provable type".into(),
                stmt,
                stmt.span(),
            )]),
            IoError(ref err) => (format!("I/O error: {error}", error = err.clone()).into(), vec![(
                AnnotationType::Error,
                "Source file could not be read".into(),
                stmt,
                stmt.span(),
            )]),
            LocalLabelAmbiguous(span) => ("Local label is ambiguous".into(), vec![(
                AnnotationType::Error,
                "Local label conflicts with the name of an existing statement".into(),
                stmt,
                *span,
            )]),
            LocalLabelDuplicate(span) => ("Duplicate local Label".into(), vec![(
                AnnotationType::Error,
                "Local label duplicates another label in the same proof".into(),
                stmt,
                *span,
            )]),
            MalformedAdditionalInfo(span) => ("Malformed additional info".into(), vec![(
                AnnotationType::Error,
                "Malformed additional information".into(),
                stmt,
                *span,
            )]),
            MidStatementCommentMarker(marker) => ("Mid-statement comment".into(), vec![(
                AnnotationType::Warning,
                "Marked comments are only effective between statements, not inside them".into(),
                stmt,
                *marker,
            )]),
            MissingLabel => ("Missing label".into(), vec![(
                AnnotationType::Error,
                "This statement type requires a label".into(),
                stmt,
                stmt.span(),
            )]),
            MissingProof(math_end) => ("Missing proof".into(), vec![(
                AnnotationType::Error,
                "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                        if you do not have a proof yet".into(),
                stmt,
                *math_end,
            )]),
            NestedComment(tok, opener) => ("Nested comment".into(), vec![(
                AnnotationType::Warning,
                "Nested comments are not supported - comment will end at the first $)".into(),
                stmt,
                *tok,
            ), (
                AnnotationType::Note,
                "Comment started here".into(),
                stmt,
                *opener,
            )]),
            NotActiveSymbol(index) => ("Inactive symbol".into(), vec![(
                AnnotationType::Error,
                "Token used here must be active in the current scope".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            NotAProvableStatement => ("Not a provable statement".into(), vec![(
                AnnotationType::Error,
                "Statement does not start with the provable constant type".into(),
                stmt,
                stmt.span(),
            )]),
            ParsedStatementNoTypeCode => ("Empty statement".into(), vec![(
                AnnotationType::Error,
                "Empty statement".into(),
                stmt,
                stmt.span(),
            )]),
            ParsedStatementTooShort(ref tok) => ("Parsed statement too short".into(), vec![(
                AnnotationType::Error,
                format!("Statement is too short, expecting for example {expected}", expected = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            ParsedStatementWrongTypeCode(ref found) => ("Parsed statement has wrong typecode".into(), vec![(
                AnnotationType::Error,
                format!("Type code {found} is not among the expected type codes", found = t(found)).into(),
                stmt,
                stmt.span(),
            )]),
            ProofDvViolation => ("Distinct variable violation".into(), vec![(
                AnnotationType::Error,
                "Disjoint variable constraint violated".into(),
                stmt,
                stmt.span(),
            )]),
            ProofExcessEnd => ("Proof does not end with a single statement".into(), vec![(
                AnnotationType::Error,
                "Must be exactly one statement on stack at end of proof".into(),
                stmt,
                stmt.span(),
            )]),
            ProofIncomplete => ("Proof incomplete".into(), vec![(
                AnnotationType::Warning,
                "Proof is incomplete".into(),
                stmt,
                stmt.span(),
            )]),
            ProofInvalidSave => ("Invalid save".into(), vec![(
                AnnotationType::Error,
                "Z must appear immediately after a complete step integer".into(),
                stmt,
                stmt.span(),
            )]),
            ProofMalformedVarint => ("Proof too long".into(), vec![(
                AnnotationType::Error,
                "Proof step number too long or missing terminator".into(),
                stmt,
                stmt.span(),
            )]),
            ProofNoSteps => ("Empty proof".into(), vec![(
                AnnotationType::Error,
                "Proof must have at least one step (use ? if deliberately incomplete)".into(),
                stmt,
                stmt.span(),
            )]),
            ProofUnderflow => ("Proof underflow".into(), vec![(
                AnnotationType::Error,
                "Too few statements on stack to satisfy step's mandatory hypotheses".into(),
                stmt,
                stmt.span(),
            )]),
            ProofUnterminatedRoster => ("Unterminated roster".into(), vec![(
                AnnotationType::Error,
                "List of referenced assertions in a compressed proof must be terminated by )".into(),
                stmt,
                stmt.span(),
            )]),
            ProofWrongExprEnd => ("Proven statement does not match assertion".into(), vec![(
                AnnotationType::Error,
                "Final step statement does not match assertion".into(),
                stmt,
                stmt.span(),
            )]),
            ProofWrongTypeEnd => ("Proven statement has wrong typecode".into(), vec![(
                AnnotationType::Error,
                "Final step typecode does not match assertion".into(),
                stmt,
                stmt.span(),
            )]),
            RepeatedLabel(l_span, f_span) => ("Repeated label".into(), vec![(
                AnnotationType::Error,
                "A statement may have only one label".into(),
                stmt,
                *l_span,
            ), (
                AnnotationType::Note,
                "First label was here".into(),
                stmt,
                *f_span,
            )]),
            SpuriousLabel(lspan) => ("Spurious label".into(), vec![(
                AnnotationType::Error,
                "Labels are only permitted for statements of type $a, $e, $f, or $p".into(),
                stmt,
                *lspan,
            )]),
            SpuriousProof(math_end) => ("Spurious proof".into(), vec![(
                AnnotationType::Error,
                "Proofs are only allowed on $p assertions".into(),
                stmt,
                *math_end,
            )]),
            StepEssenWrong => ("Wrong essential statement".into(), vec![(
                AnnotationType::Error,
                "Step used for $e hypothesis does not match statement".into(),
                stmt,
                stmt.span(),
            )]),
            StepEssenWrongType => ("Wrong essential typecode".into(), vec![(
                AnnotationType::Error,
                "Step used for $e hypothesis does not match typecode".into(),
                stmt,
                stmt.span(),
            )]),
            StepFloatWrongType => ("Wrong floating typecode".into(), vec![(
                AnnotationType::Error,
                "Step used for $f hypothesis does not match typecode".into(),
                stmt,
                stmt.span(),
            )]),
            StepMissing(ref tok) => ("Missing step".into(), vec![(
                AnnotationType::Error,
                format!("Step {step} referenced by proof does not correspond to a $p statement (or \
                        is malformed)", step = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            StepOutOfRange => ("Step out of range".into(), vec![(
                AnnotationType::Error,
                "Step in compressed proof is out of range of defined steps".into(),
                stmt,
                stmt.span(),
            )]),
            StepUsedAfterScope(ref tok) => ("Step used after scope".into(), vec![(
                AnnotationType::Error,
                format!("Step {step} referenced by proof is a hypothesis not active in this scope", step = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            StepUsedBeforeDefinition(ref tok) => ("Step used before definition".into(), vec![(
                AnnotationType::Error,
                format!("Step {step} referenced by proof has not yet been proved", step = t(tok)).into(),
                stmt,
                stmt.span(),
            )]),
            SymbolDuplicatesLabel(index, saddr) => ("Symbol duplicates label".into(), vec![(
                AnnotationType::Warning,
                "Metamath spec forbids symbols which are the same as labels in the same \
                        database".into(),
                stmt,
                stmt.math_span(*index),
            ), (
                AnnotationType::Note,
                "Symbol was used as a label here".into(),
                sset.statement(*saddr),
                sset.statement(*saddr).span(),
            )]),
            SymbolRedeclared(index, taddr) => ("Symbol redeclared".into(), vec![(
                AnnotationType::Error,
                "This symbol is already active in this scope".into(),
                stmt,
                stmt.math_span(*index),
            ), (
                AnnotationType::Note,
                "Symbol was previously declared here".into(),
                stmt,
                sset.statement(taddr.statement).math_span(taddr.token_index),
            )]),
            UnclosedBeforeEof => ("Unclosed before eof".into(), vec![(
                AnnotationType::Error,
                "${ group must be closed with a $} before end of file".into(),
                stmt,
                stmt.span(),
            )]),
            UnclosedBeforeInclude(index) => ("Include not at top level".into(), vec![(
                AnnotationType::Error,
                "${ group must be closed with a $} before another file can be included".into(),
                stmt,
                stmt.span(),
            ), (
                AnnotationType::Note,
                "Include statement is here".into(),
                stmt.segment().statement(*index),
                stmt.segment().statement(*index).span(),
            )]),
            UnclosedComment(comment) => ("Unclosed comment".into(), vec![(
                AnnotationType::Error,
                "Comment requires closing $) before end of file".into(),
                stmt,
                *comment,
            )]),
            UnclosedInclude => ("Unclosed include".into(), vec![(
                AnnotationType::Error,
                "$[ requires a matching $]".into(),
                stmt,
                stmt.span(),
            )]),
            UnclosedMath => ("Unclosed math".into(), vec![(
                AnnotationType::Error,
                "A math string must be closed with $= or $.".into(),
                stmt,
                stmt.span(),
            )]),
            UnclosedProof => ("Unclosed proof".into(), vec![(
                AnnotationType::Error,
                "A proof must be closed with $.".into(),
                stmt,
                stmt.span(),
            )]),
            UnknownKeyword(kwspan) => ("Unknown keyword".into(), vec![(
                AnnotationType::Error,
                "Statement-starting keyword must be one of $a $c $d $e $f $p $v".into(),
                stmt,
                *kwspan,
            )]),
            UnmatchedCloseGroup => ("Unmatched close group".into(), vec![(
                AnnotationType::Error,
                "This $} does not match any open ${".into(),
                stmt,
                stmt.span(),
            )]),
            UnparseableStatement(index) => ("Unparseable statement".into(), vec![(
                AnnotationType::Error,
                "Could not parse this statement".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            VariableMissingFloat(index) => ("Variable missing float".into(), vec![(
                AnnotationType::Error,
                "Variable token used in statement must have an active $f".into(),
                stmt,
                stmt.math_span(*index),
            )]),
            VariableRedeclaredAsConstant(index, taddr) => ("Variable redeclared as a constant".into(), vec![(
                AnnotationType::Error,
                "Symbol cannot be used as a variable here and as a constant later".into(),
                stmt,
                stmt.math_span(*index),
            ), (
                AnnotationType::Note,
                "Symbol will be used as a constant here".into(),
                sset.statement(taddr.statement),
                sset.statement(taddr.statement).math_span(taddr.token_index),
            )]),
        };

        make_snippet(sset, infos, lc, f)
    }
}
