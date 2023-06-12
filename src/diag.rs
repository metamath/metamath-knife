//! Datatypes to represent diagnostics emitted by smetamath analysis passes.
//!
//! This includes an enum-based representation suited for programmatic
//! interpretation and testing, as well as a mostly-text representation which
//! can be used for various human-readable outputs.

use crate::as_str;
use crate::line_cache::LineCache;
use crate::parser::HeadingLevel;
use crate::segment::Comparer;
use crate::segment_set::SegmentSet;
use crate::segment_set::SourceInfo;
use crate::statement::GlobalSpan;
use crate::statement::StatementAddress;
use crate::statement::StatementIndex;
use crate::statement::Token;
use crate::statement::TokenAddress;
use crate::statement::TokenIndex;
use crate::statement::NO_STATEMENT;
use crate::Span;
use crate::StatementRef;
use crate::StatementType;
use annotate_snippets::display_list::FormatOptions;
use annotate_snippets::snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation};
use itertools::Itertools;
use std::borrow::Borrow;
use std::borrow::Cow;
use std::error::Error;
use std::fmt::Display;
use std::io;
use typed_arena::Arena;

/// The three kinds of markup supported by `$t` typesetting comments.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MarkupKind {
    /// The `htmldef` markup style, used in metamath for GIF-based rendering.
    Html,
    /// The `althtmldef` markup style, used in metamath for unicode-based rendering.
    AltHtml,
    /// The `latexdef` markup style, used in metamath for LaTeX markup rendering.
    Latex,
}

impl MarkupKind {
    const fn def_name(self) -> &'static str {
        match self {
            MarkupKind::Html => "htmldef",
            MarkupKind::AltHtml => "althtmldef",
            MarkupKind::Latex => "latexdef",
        }
    }
}

impl HeadingLevel {
    fn diagnostic_note(self) -> &'static [&'static str] {
        #[rustfmt::skip]
        macro_rules! diag { ($type:expr, $header:expr, $decoration:expr) => { &[
            concat!("A ", $type, " header comment has the form: \
                \n$(\
                \n", $decoration, "\
                \n  ", $header, "\
                \n", $decoration, "\
                \nMarkup text here\
                \n$)"),
            "section titles may not be longer than one line",
        ]}}
        match self {
            HeadingLevel::MajorPart => {
                diag!("major part", "MY HEADER", "###############################")
            }
            HeadingLevel::Section => {
                diag!("section", "My Header", "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#")
            }
            HeadingLevel::SubSection => {
                diag!("subsection", "My Header", "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=")
            }
            HeadingLevel::SubSubSection => diag!(
                "subsubsection",
                "My Header",
                "-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-"
            ),
            _ => unreachable!(),
        }
    }
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
    BadCommand(Span),
    BadCommentEnd(Span, Span),
    BadExplicitLabel(Token),
    BadFloating,
    BadLabel(Span),
    BibEscape(u32, Span),
    ChainBackref(Span),
    CommandExpectedAs(Span),
    CommandExpectedString(Span),
    CommandIncomplete(Span),
    CommentMarkerNotStart(Span),
    ConstantNotTopLevel,
    DefCkDuplicateDefinition(Token, StatementAddress),
    DefCkDuplicateEquality(Token, GlobalSpan, Span),
    DefCkMalformedDefinition(StatementAddress),
    DefCkMisplacedPrimitive(Span),
    DefCkMalformedEquality(StatementAddress, Span),
    DefCkMalformedJustification(GlobalSpan),
    DefCkMalformedSyntaxAxiom,
    DefCkMissingDefinition,
    DefCkSyntaxUsedBeforeDefinition(Token, StatementAddress),
    DefCkNotAnEquality(Token, Vec<Token>),
    DisjointSingle,
    DjNotVariable(TokenIndex),
    DjRepeatedVariable(TokenIndex, TokenIndex),
    DateOrderError(Span, Span),
    DateParseError(Span),
    DefaultAuthor(Span),
    DuplicateContributor(Span, Span),
    DuplicateExplicitLabel(Token),
    DuplicateLabel(StatementAddress),
    DuplicateMarkupDef(MarkupKind, GlobalSpan, Span),
    EmptyFilename,
    EmptyMathString,
    EmptyLabel(u32),
    EssentialAtTopLevel,
    ExprNotConstantPrefix(TokenIndex),
    FilenameDollar,
    FilenameSpaces,
    FloatNotConstant(TokenIndex),
    FloatNotVariable(TokenIndex),
    FloatRedeclared(StatementAddress),
    FormulaVerificationFailed,
    GrammarAmbiguous(StatementAddress),
    GrammarCantBuild(&'static str),
    GrammarProvableFloat,
    HeaderCommentParseError(HeadingLevel),
    InvalidAxiomRestatement(Span, Span),
    IoError(String),
    LabelContainsUnderscore(Span),
    LineLengthExceeded(Span),
    LocalLabelAmbiguous(Span),
    LocalLabelDuplicate(Span),
    MarkupNeedsWhitespace(u32),
    MathboxCrossReference(Box<(Span, Span, Span, Token, Token)>),
    MathboxHeaderFormat(Span),
    MalformedAdditionalInfo(Span),
    MidStatementCommentMarker(Span),
    MissingContributor,
    MissingLabel,
    MissingMarkupDef([bool; 3], Span),
    MissingProof(Span),
    MMReservedLabel(Span),
    NestedComment(Span, Span),
    NotActiveSymbol(TokenIndex),
    NotAProvableStatement,
    OldAltNotDiscouraged,
    ParenOrderError(Span, Span),
    ProofDvViolation,
    ProofExcessEnd,
    ProofIncomplete,
    ProofInvalidSave,
    ProofMalformedVarint,
    ProofModOnAxiom(Span),
    ProofNoSteps,
    ProofUnderflow,
    ProofUnterminatedRoster,
    ProofWrongExprEnd,
    ProofWrongTypeEnd,
    RepeatedLabel(Span, Span),
    ReservedAtToken(Span),
    ReservedQToken(Span),
    SpuriousLabel(Span),
    SpuriousProof(Span),
    StepEssenWrong,
    StepEssenWrongType,
    StepFloatWrongType,
    StepMissing(Token),
    StepOutOfRange,
    StepUsedAfterScope(Token),
    StepUsedBeforeDefinition(Token),
    StmtParseError(StmtParseError),
    SymbolDuplicatesLabel(TokenIndex, StatementAddress),
    SymbolRedeclared(TokenIndex, TokenAddress),
    TabUsed(Span),
    TrailingWhitespace(Span),
    UnclosedBeforeEof,
    UnclosedBeforeInclude(StatementIndex),
    UnclosedCommandComment(Span),
    UnclosedCommandString(Span),
    UnclosedComment(Span),
    UnclosedHtml(u32, u32),
    UnclosedInclude,
    UnclosedMath,
    UnclosedMathMarkup(u32, u32),
    UnclosedProof,
    UnconventionalAxiomLabel(Span),
    UndefinedBibTag(Span),
    UndefinedToken(Span, Token),
    UninterpretedEscape(u32),
    UninterpretedHtml(Span),
    UnknownLabel(Span),
    UnknownKeyword(Span),
    UnknownTypesettingCommand(Span),
    UnmatchedCloseGroup,
    VariableMissingFloat(TokenIndex),
    VariableRedeclaredAsConstant(TokenIndex, TokenAddress),
    WindowsReservedLabel(Span),
}
use self::Diagnostic::*;

impl From<io::Error> for Diagnostic {
    fn from(err: io::Error) -> Diagnostic {
        IoError(format!("{err}"))
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
            let stmt = sset.statement_or_dummy(*saddr);
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
/// * `label`, `infos` - Diagnostic information to display.
/// * `lc` - A helper struct for keeping track of line numbers in the source file
/// * `f` - A function for continuation passing style (CPS)
#[must_use]
fn make_snippet_from<'b, T>(
    label: &str,
    infos: impl Iterator<Item = (AnnotationType, Cow<'b, str>, Span, &'b SourceInfo)>,
    footer: &[&str],
    lc: &mut LineCache,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T,
) -> T {
    let mut slices = vec![];
    let arena: Arena<String> = Arena::new();
    for (annotation_type, label, span, source) in infos {
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
            label: Some(label),
            id: None,
            annotation_type: slices[0].annotations[0].annotation_type,
        }),
        footer: footer
            .iter()
            .map(|msg| Annotation {
                id: None,
                label: Some(msg),
                annotation_type: AnnotationType::Note,
            })
            .collect(),
        slices,
        opt: FormatOptions {
            color: true,
            ..FormatOptions::default()
        },
    })
}

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
    (label, infos): AnnInfo<'_>,
    footer: &[&str],
    lc: &mut LineCache,
    f: impl for<'a> FnOnce(Snippet<'a>) -> T,
) -> T {
    let iter = (infos.into_iter()).map(|(annotation_type, label, stmt, span)| {
        let source = sset.source_info(stmt.segment().id).borrow();
        (annotation_type, label, span, source)
    });
    make_snippet_from(&label, iter, footer, lc, f)
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
        let mut notes: &[&str] = &[];
        let infos = match self {
            BadCharacter(pos, byte) => ("Invalid character".into(), vec![(
                AnnotationType::Error,
                format!("Invalid character (byte value {byte}); Metamath source files are limited to \
                        US-ASCII with controls TAB, CR, LF, FF)").into(),
                stmt,
                Span::new(*pos, *pos + 1),
            )]),
            BadCommand(span) => ("Invalid command".into(), vec![(
                AnnotationType::Warning,
                "Commands must start with a keyword".into(),
                stmt,
                *span,
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
            &BibEscape(index, span) => {
                notes = &["Avoid uses of escape characters in bibliography tags \
                    since they break regex-based implementations"];
                ("Invalid escape character".into(), vec![(
                    AnnotationType::Warning,
                    "Use of ~ or ` in a bibliography tag".into(),
                    stmt,
                    Span::new2(index, index + 1),
                ), (
                    AnnotationType::Note,
                    "computed bibliography span".into(),
                    stmt,
                    span,
                )])
            }
            ChainBackref(span) => ("Chain backref".into(), vec![(
                AnnotationType::Error,
                "Backreference steps are not permitted to have local labels".into(),
                stmt,
                *span,
            )]),
            CommandExpectedAs(span) => ("Expected 'as'".into(), vec![(
                AnnotationType::Warning,
                "Expected the keyword 'as' here".into(),
                stmt,
                *span,
            )]),
            CommandExpectedString(span) => ("Expected string, got keyword argument".into(), vec![(
                AnnotationType::Warning,
                "Expected a string here".into(),
                stmt,
                *span,
            )]),
            CommandIncomplete(span) => ("Incomplete command".into(), vec![(
                AnnotationType::Warning,
                "This command ended early, it was expecting more arguments".into(),
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
            DefCkDuplicateDefinition(ref tok, prev_saddr) => (format!("Definition Check: Duplicate definition for '{label}'", label = t(tok)).into(), vec![(
                AnnotationType::Warning,
                format!("This axiom seems to introduce a definition for '{label}', however a definition already exists.", label = t(tok)).into(),
                stmt,
                stmt.label_span(),
            ), (
                AnnotationType::Note,
                "Definition was previously provided here.".into(),
                sset.statement(*prev_saddr),
                sset.statement(*prev_saddr).label_span(),
            )]),
            &DefCkDuplicateEquality(ref tok, fst, snd) => (format!("Definition Check: Duplicate equality for typecode '{code}'", code = t(tok)).into(), vec![(
                AnnotationType::Warning,
                format!("This is the second equality introduced for typecode '{label}'. Each typecode must have a unique equality.", label = t(tok)).into(),
                stmt,
                snd,
            ), (
                AnnotationType::Note,
                "Definition was previously provided here.".into(),
                sset.statement_or_dummy(StatementAddress::new(fst.0, NO_STATEMENT)),
                fst.1,
            )]),
            &DefCkMalformedDefinition(syntax) => ("Definition Check: Malformed definition".into(), vec![(
                AnnotationType::Error,
                "Malformed definition".into(),
                stmt,
                stmt.label_span(),
            ), (
                AnnotationType::Note,
                "Syntax axiom defined here".into(),
                sset.statement(syntax),
                sset.statement(syntax).label_span(),
            )]),
            &DefCkMisplacedPrimitive(span) => ("Definition Check: Misplaced 'primitive' command".into(), vec![(
                AnnotationType::Warning,
                "there is no pending definition for this".into(),
                stmt,
                span,
            )]),
            &DefCkMalformedEquality(prev_saddr, tok) => ("Definition Check: Malformed equality or equality theorem".into(), vec![(
                AnnotationType::Error,
                "Malformed equality".into(),
                stmt,
                tok,
            ), (
                AnnotationType::Note,
                "declaration here does not have the shape of an equality (theorem)".into(),
                sset.statement(prev_saddr),
                sset.statement(prev_saddr).label_span(),
            )]),
            &DefCkMalformedJustification(span) => ("Definition Check: Malformed justification theorem".into(), vec![(
                AnnotationType::Error,
                "Malformed justification".into(),
                stmt,
                stmt.label_span(),
            ), (
                AnnotationType::Note,
                "marked as justification here".into(),
                sset.statement_or_dummy(StatementAddress::new(span.0, NO_STATEMENT)),
                span.1,
            )]),
            &DefCkMalformedSyntaxAxiom => {
                notes = &["syntax axioms must have no hypotheses, no repeated variables and no $d"];
                ("Definition Check: Malformed syntax axiom".into(), vec![(
                    AnnotationType::Error,
                    "".into(),
                    stmt,
                    stmt.label_span(),
                )])
            },
            DefCkMissingDefinition => {
                notes = &["If this is intentional, consider adding a $( $j primitive ...; $) command"];
                ("Definition Check: Missing definition or 'primitive'".into(), vec![(
                    AnnotationType::Error,
                    "this syntax axiom has no corresponding definition".into(),
                    stmt,
                    stmt.label_span(),
                )])
            },
            DefCkSyntaxUsedBeforeDefinition(tok, saddr) => (format!("Definition Check: '{label}' used before definition, or missing definition.", label = t(tok)).into(), vec![(
                AnnotationType::Error,
                format!("this expression contains an occurrence of '{label}'", label = t(tok)).into(),
                stmt,
                stmt.span(),
            ), (
                AnnotationType::Note,
                "syntax declared here".into(),
                sset.statement(*saddr),
                sset.statement(*saddr).label_span(),
            )]),
            DefCkNotAnEquality(ref tok, equalities) => {
                notes = &["No provable axioms should appear between definitions and the corresponding syntax declaration."];
                ("Definition Check: Not an equality".into(), vec![(
                AnnotationType::Error,
                format!("This definition does not use an equality.  It is built using '{label}', but the only declared equalities are '{equalities}'", 
                    label = t(tok),
                    equalities = equalities.iter().map(t).join("', '"),
                ).into(),
                stmt,
                stmt.label_span(),
            )])},
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
            &DateOrderError(contrib, later) => {
                notes = &["It is easiest to read the contribution comments when they come in order"];
                (format!("at {}: Parentheticals should come in chronological order", as_str(stmt.label())).into(), vec![(
                    AnnotationType::Warning,
                    "this date...".into(),
                    stmt,
                    contrib,
                ), (
                    AnnotationType::Warning,
                    "comes after this one".into(),
                    stmt,
                    later,
                )])
            }
            &DateParseError(span) => ("Failed to parse date".into(), vec![(
                AnnotationType::Error,
                "Expected DD-MMM-YYYY format".into(),
                stmt,
                span,
            )]),
            &DefaultAuthor(span) => ("Use of default author".into(), vec![(
                AnnotationType::Warning,
                "There should be a person's name here".into(),
                stmt,
                span,
            )]),
            &DuplicateContributor(fst, snd) => {
                notes = &["The 'Contributed by' field indicates the first author of a theorem.\n\
                    Use 'Revised by' for subsequent contributions to the same theorem."];
                ("Statement has multiple contributors".into(), vec![(
                    AnnotationType::Note,
                    "First contributor here".into(),
                    stmt,
                    fst,
                ), (
                    AnnotationType::Warning,
                    "Second contributor here".into(),
                    stmt,
                    snd,
                )])
            },
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
            &DuplicateMarkupDef(kind, fst, snd) => (format!("Duplicate {}", kind.def_name()).into(), vec![(
                AnnotationType::Warning,
                "This token has already been defined".into(),
                stmt,
                snd,
            ), (
                AnnotationType::Note,
                "Token was previously defined here".into(),
                sset.statement_or_dummy(StatementAddress::new(fst.0, NO_STATEMENT)),
                fst.1,
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
            &EmptyLabel(index) => {
                notes = &["empty label references can happen because '~' \
                    was used at the end of a comment,",
                    "or before <HTML>, a math string, or a bibliography tag"];
                ("Empty label reference".into(), vec![(
                    AnnotationType::Error,
                    "This references nothing".into(),
                    stmt,
                    Span::new2(index, index + 1),
                )])
            },
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
            GrammarCantBuild(message) => ("Can't build the grammar".into(), vec![(
                AnnotationType::Error,
                (*message).into(),
                stmt,
                stmt.span(),
            )]),
            GrammarProvableFloat => ("Floating declaration of provable type".into(), vec![(
                AnnotationType::Error,
                "Floating declaration of provable type".into(),
                stmt,
                stmt.span(),
            )]),
            HeaderCommentParseError(lvl) => {
                notes = lvl.diagnostic_note();
                ("Invalid header comment".into(), vec![(
                    AnnotationType::Warning,
                    "Could not parse this as a header".into(),
                    stmt,
                    stmt.span(),
                )])
            },
            InvalidAxiomRestatement(ax_span, th_span) => ("Invalid axiom restatement".into(), vec![(
                AnnotationType::Warning,
                "This ax* theorem does not match the corresponding ax-*".into(),
                stmt,
                *th_span,
            ), (
                AnnotationType::Note,
                "Axiom ax-* here".into(),
                stmt,
                *ax_span,
            )]),
            IoError(ref err) => (format!("I/O error: {error}", error = err.clone()).into(), vec![(
                AnnotationType::Error,
                "Source file could not be read".into(),
                stmt,
                stmt.span(),
            )]),
            LabelContainsUnderscore(span) => {
                notes = &["Prefer '-' over '_' in labels"];
                ("Label contains underscore".into(), vec![(
                    AnnotationType::Warning,
                    "this statement has an underscore".into(),
                    stmt,
                    *span,
                )])
            },
            LineLengthExceeded(span) => ("Line is too long".into(), vec![(
                AnnotationType::Warning,
                "These characters go over the line limit".into(),
                stmt,
                *span,
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
            &MarkupNeedsWhitespace(index) => ("Markup character requires surrounding whitespace".into(), vec![(
                AnnotationType::Warning,
                "Put spaces around this character".into(),
                stmt,
                Span::new2(index, index + 1),
            )]),
            MathboxCrossReference(args) => {
                let (span, this, that, ref this_name, ref that_name) = **args;
                let ann1 =
                    if this_name.is_empty() { "theorem defined here".into() }
                    else { format!("this theorem is in {}'s mathbox", as_str(this_name)).into() };
                let ann2 =
                    if that_name.is_empty() { "defined in a different mathbox".into() }
                    else { format!("defined in {}'s mathbox", as_str(that_name)).into() };
                ("Mathbox uses a theorem from another mathbox".into(), vec![
                    (AnnotationType::Warning, ann1, stmt, this),
                    (AnnotationType::Note, "it refers to a theorem here...".into(), stmt, span),
                    (AnnotationType::Note, ann2, stmt, that)
                ])
            }
            MathboxHeaderFormat(span) => ("Malformed mathbox header".into(), vec![(
                AnnotationType::Warning,
                "Expected 'Mathbox for <name>'".into(),
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
            MissingContributor => ("No contribution comment".into(), vec![(
                AnnotationType::Warning,
                "No (Contributed by...) provided for this statement".into(),
                stmt,
                stmt.label_span(),
            )]),
            MissingLabel => ("Missing label".into(), vec![(
                AnnotationType::Error,
                "This statement type requires a label".into(),
                stmt,
                stmt.span(),
            )]),
            &MissingMarkupDef([html, alt_html, latex], span) => {
                let msg = html.then_some("htmldef").into_iter()
                    .chain(alt_html.then_some("althtmldef").into_iter())
                    .chain(latex.then_some("latexdef").into_iter());
                (format!("Missing {} for token", msg.format(", ")).into(), vec![(
                    AnnotationType::Warning,
                    "This token has not been declared in the $t comment".into(),
                    stmt,
                    span,
                )])
            },
            MissingProof(math_end) => ("Missing proof".into(), vec![(
                AnnotationType::Error,
                "Provable assertion requires a proof introduced with $= here; use $= ? $. \
                        if you do not have a proof yet".into(),
                stmt,
                *math_end,
            )]),
            MMReservedLabel(span) => ("Reserved label".into(), vec![(
                AnnotationType::Warning,
                "Labels beginning with 'mm' are reserved for Metamath file names".into(),
                stmt,
                *span,
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
            OldAltNotDiscouraged if stmt.statement_type() == StatementType::Axiom => {
                notes = &["Add (New usage is discouraged.) to the comment"];
                ("OLD/ALT axiom not discouraged".into(), vec![(
                    AnnotationType::Warning,
                    "OLD and ALT axioms should be discouraged".into(),
                    stmt,
                    stmt.label_span(),
                )])
            },
            OldAltNotDiscouraged => {
                notes = &["Add (Proof modification is discouraged.) \
                    and (New usage is discouraged.) to the comment"];
                ("OLD/ALT theorem not discouraged".into(), vec![(
                    AnnotationType::Warning,
                    "OLD and ALT theorems should be discouraged".into(),
                    stmt,
                    stmt.label_span(),
                )])
            },
            &ParenOrderError(contrib, later) => {
                notes = &["The contribution comment should come before any revisions"];
                ("(Revised by...) precedes (Contributed by...)".into(), vec![(
                    AnnotationType::Warning,
                    "contribution comment here".into(),
                    stmt,
                    contrib,
                ), (
                    AnnotationType::Warning,
                    "earlier revision comment".into(),
                    stmt,
                    later,
                )])
            }
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
            &ProofModOnAxiom(span) => {
                notes = &["it doesn't make sense to put this marker on an axiom,\n\
                    because axioms don't have proofs"];
                ("Axiom contains (Proof modification is discouraged.)".into(), vec![(
                    AnnotationType::Warning,
                    "This doesn't make sense".into(),
                    stmt,
                    span,
                )])
            },
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
            ReservedAtToken(span) => {
                notes = &["The '@' character is discouraged in tokens because it is\n\
                    traditionally used to replace '$' in commented out database source code."];
                ("Token contains '@'".into(), vec![(
                    AnnotationType::Warning,
                    "Used '@' character here".into(),
                    stmt,
                    *span,
                )])
            }
            ReservedQToken(span) => {
                notes = &["The '?' character is discouraged in tokens because it is\n\
                    sometimes used as a math token search wildcard."];
                ("Token contains '?'".into(), vec![(
                    AnnotationType::Warning,
                    "Used '?' character here".into(),
                    stmt,
                    *span,
                )])
            }
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
            StmtParseError(err) => err.build_info(stmt),
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
            TabUsed(span) => ("Tab character used".into(), vec![(
                AnnotationType::Warning,
                "Use spaces instead".into(),
                stmt,
                *span,
            )]),
            TrailingWhitespace(span) => ("Trailing whitespace".into(), vec![(
                AnnotationType::Warning,
                "whitespace here".into(),
                stmt,
                *span,
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
            UnclosedCommandComment(span) => ("Unclosed comment".into(), vec![(
                AnnotationType::Error,
                "$t/$j comment requires closing */ before end of statement".into(),
                stmt,
                *span,
            )]),
            UnclosedCommandString(span) => ("Unclosed string".into(), vec![(
                AnnotationType::Error,
                "A string must be closed with ' or \"".into(),
                stmt,
                *span,
            )]),
            UnclosedComment(comment) => ("Unclosed comment".into(), vec![(
                AnnotationType::Error,
                "Comment requires closing $) before end of file".into(),
                stmt,
                *comment,
            )]),
            &UnclosedHtml(start, end) => ("Unclosed <HTML>".into(), vec![(
                AnnotationType::Error,
                "HTML blocks must be closed".into(),
                stmt,
                Span::new2(end, end + 2), // the $)
            ), (
                AnnotationType::Note,
                "HTML block started here".into(),
                stmt,
                Span::new2(start, start + 6), // the <HTML>
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
            &UnclosedMathMarkup(start, end) => ("Unclosed math".into(), vec![(
                AnnotationType::Error,
                "A math string must be closed with `".into(),
                stmt,
                Span::new2(end, end + 2), // the $)
            ), (
                AnnotationType::Note,
                "Math string started here".into(),
                stmt,
                Span::new2(start, start + 1), // the `
            )]),
            UnclosedProof => ("Unclosed proof".into(), vec![(
                AnnotationType::Error,
                "A proof must be closed with $.".into(),
                stmt,
                stmt.span(),
            )]),
            UnconventionalAxiomLabel(span) => ("Unconventional axiom label".into(), vec![(
                AnnotationType::Warning,
                "Axioms should start with 'ax-' or 'df-'".into(),
                stmt,
                *span,
            )]),
            UndefinedBibTag(span) => ("Missing bibliography tag".into(), vec![(
                AnnotationType::Warning,
                "This tag was not found in the bibliography file".into(),
                stmt,
                *span,
            )]),
            UndefinedToken(span, tk) => (format!("Undeclared token '{}'", as_str(tk)).into(), vec![(
                AnnotationType::Warning,
                "This token was not declared in any $v or $c statement".into(),
                stmt,
                *span,
            )]),
            UnknownKeyword(kwspan) => ("Unknown keyword".into(), vec![(
                AnnotationType::Error,
                "Statement-starting keyword must be one of $a $c $d $e $f $p $v".into(),
                stmt,
                *kwspan,
            )]),
            UnknownTypesettingCommand(kwspan) => ("Unknown $t command".into(), vec![(
                AnnotationType::Error,
                "Typesetting command must be one of:\n\
                latexdef, htmldef, althtmldef, htmlvarcolor, htmltitle, htmlhome,\n\
                exthtmltitle, exthtmlhome, exthtmllabel, htmldir, althtmldir,\n\
                htmlbibliography, exthtmlbibliography, htmlcss, htmlfont, htmlexturl".into(),
                stmt,
                *kwspan,
            )]),
            &UninterpretedEscape(index) => {
                notes = &[
                    "This character has special meaning in this position, \
                    but it was not interpretable here.",
                    "Use ~~ or [[ or `` if you mean to include the character literally"
                ];
                ("Invalid escape character".into(), vec![(
                    AnnotationType::Warning,
                    "This escape character should be doubled".into(),
                    stmt,
                    Span::new2(index, index + 1),
                )])
            }
            UninterpretedHtml(tok) => ("incorrect use of <HTML>".into(), vec![(
                AnnotationType::Warning,
                "This <HTML> was not interpreted".into(),
                stmt,
                *tok,
            )]),
            UnknownLabel(span) => ("Unknown label".into(), vec![(
                AnnotationType::Warning,
                "This is not the label of any statement".into(),
                stmt,
                *span,
            )]),
            UnmatchedCloseGroup => ("Unmatched close group".into(), vec![(
                AnnotationType::Error,
                "This $} does not match any open ${".into(),
                stmt,
                stmt.span(),
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
            WindowsReservedLabel(span) => {
                notes = &["On windows, it is not legal to name a file any of:\n\
                    CON, PRN, AUX, CLOCK$, NUL, COM[1-9], LPT[1-9]."];
                ("Windows reserved label".into(), vec![(
                    AnnotationType::Warning,
                    "This label cannot be used as the name of a file on windows".into(),
                    stmt,
                    *span,
                )])
            },
        };

        make_snippet(sset, infos, notes, lc, f)
    }
}

/// An error during statement parsing.
#[derive(Debug, Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum StmtParseError {
    ParsedStatementTooShort(Span, Option<Token>),
    ParsedStatementNoTypeCode,
    ParsedStatementWrongTypeCode(Token),
    UnknownToken(Span),
    UnparseableStatement(Span),
}

impl StmtParseError {
    /// The diagnostic's label
    #[must_use]
    pub fn label<'a>(&self) -> Cow<'a, str> {
        match self {
            StmtParseError::ParsedStatementTooShort(_, _) => "Parsed statement too short",
            StmtParseError::ParsedStatementWrongTypeCode(_) => {
                "Parsed statement has wrong typecode"
            }
            StmtParseError::UnknownToken(_) => "Unknown token",
            StmtParseError::UnparseableStatement(_) => "Unparseable statement",
            StmtParseError::ParsedStatementNoTypeCode => "Empty statement",
        }
        .into()
    }

    /// The diagnostic's severity
    #[must_use]
    #[allow(clippy::unused_self)]
    pub const fn severity(&self) -> AnnotationType {
        AnnotationType::Error
    }

    fn build_info<'a>(&self, stmt: StatementRef<'a>) -> AnnInfo<'a> {
        fn t(v: &Token) -> String {
            as_str(v).to_owned()
        }
        let severity = self.severity();
        let info = match self {
            StmtParseError::ParsedStatementTooShort(span, ref opt_tok) => (
                severity,
                match opt_tok {
                    Some(tok) => format!(
                        "Statement is too short, expecting for example {expected}",
                        expected = t(tok)
                    )
                    .into(),
                    None => {
                        "Statement is too short, and does not correspond to any valid prefix".into()
                    }
                },
                stmt,
                *span,
            ),
            StmtParseError::ParsedStatementWrongTypeCode(ref found) => (
                severity,
                format!(
                    "Type code {found} is not among the expected type codes",
                    found = t(found)
                )
                .into(),
                stmt,
                stmt.span(),
            ),
            StmtParseError::UnknownToken(span) => (
                severity,
                "This token was not declared in any $v or $c statement".into(),
                stmt,
                *span,
            ),
            StmtParseError::UnparseableStatement(span) => (
                severity,
                "Could not parse this statement".into(),
                stmt,
                *span,
            ),
            StmtParseError::ParsedStatementNoTypeCode => (
                AnnotationType::Error,
                "Empty statement".into(),
                stmt,
                stmt.span(),
            ),
        };
        (self.label(), vec![info])
    }
}

impl From<StmtParseError> for Diagnostic {
    fn from(err: StmtParseError) -> Self {
        Diagnostic::StmtParseError(err)
    }
}

impl Display for StmtParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.label())
    }
}

impl Error for StmtParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

/// An error during bibliography parsing.
#[derive(Debug, Clone, Copy)]
#[allow(missing_docs)]
pub enum BibError {
    DuplicateBib(Span, Span),
}

impl BibError {
    #[allow(clippy::wrong_self_convention)]
    fn to_snippet<T>(
        &self,
        source: &SourceInfo,
        lc: &mut LineCache,
        f: impl for<'a> FnOnce(Snippet<'a>) -> T,
    ) -> T {
        let (label, infos): (Cow<'_, str>, Vec<_>) = match self {
            &BibError::DuplicateBib(span, other) => (
                "duplicate bibliography anchor".into(),
                vec![
                    (
                        AnnotationType::Warning,
                        "this anchor has already appeared".into(),
                        span,
                    ),
                    (AnnotationType::Note, "previous occurrence".into(), other),
                ],
            ),
        };
        let iter = (infos.into_iter())
            .map(|(annotation_type, label, span)| (annotation_type, label, span, source));
        make_snippet_from(&label, iter, &[], lc, f)
    }

    /// Convert a list of diagnostics collected by `diag_notations` to a list of snippets.
    pub fn render_list<T>(
        diags: &[(&SourceInfo, BibError)],
        f: impl for<'a> FnOnce(Snippet<'a>) -> T + Copy,
    ) -> Vec<T> {
        let mut lc = LineCache::default();
        diags
            .iter()
            .map(move |&(source, ref diag)| diag.to_snippet(source, &mut lc, f))
            .collect::<Vec<_>>()
    }
}
