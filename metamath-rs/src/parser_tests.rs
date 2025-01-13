use crate::database::Database;
use crate::diag::Diagnostic;
use crate::parser::commands;
use crate::segment::{Comparer, SegmentOrder};
use crate::statement::{Span, StatementAddress, TokenRef, NO_STATEMENT};
use crate::{as_str, StatementType};
use std::cmp::Ordering;

#[test]
#[allow(clippy::many_single_char_names)]
fn test_segment_order() {
    let mut so = SegmentOrder::default();
    let f = SegmentOrder::START;
    let e = so.new_before(f);
    let b = so.new_before(e);
    let d = so.new_before(e);
    let a = so.new_before(b);
    let c = so.new_before(d);
    so.free_id(e);
    assert_eq!(so.cmp(&a, &b), Ordering::Less);
    assert_eq!(so.cmp(&b, &c), Ordering::Less);
    assert_eq!(so.cmp(&d, &c), Ordering::Greater);
    assert_eq!(so.cmp(&d, &d), Ordering::Equal);
    assert_eq!(so.cmp(&d, &f), Ordering::Less);

    let c1 = StatementAddress::new(d, 1);
    let c2 = StatementAddress::new(d, 2);
    let f1 = StatementAddress::new(f, 1);
    assert_eq!(so.cmp(&c1, &c2), Ordering::Less);
    assert_eq!(so.cmp(&c2, &f1), Ordering::Less);
    assert_eq!(so.cmp(&f1, &c1), Ordering::Greater);
}

fn mkdb(text: &[u8]) -> Database {
    let mut db = Database::default();
    db.parse(
        "test.mm".to_owned(),
        vec![("test.mm".to_owned(), text.to_owned())],
    );
    db
}

#[test]
fn test_segref() {
    let db = mkdb(b"${ $}");
    let seg = db.parse_result().segments(..).next().unwrap();
    assert_eq!(seg.bytes(), 5);
    let mut stmt_iter = seg.into_iter();
    assert_eq!(
        stmt_iter.next().unwrap().statement_type(),
        StatementType::OpenGroup
    );
    assert_eq!(
        stmt_iter.next().unwrap().statement_type(),
        StatementType::CloseGroup
    );
    assert_eq!(
        stmt_iter.next().unwrap().statement_type(),
        StatementType::Eof
    );
    assert!(stmt_iter.next().is_none());
}

#[test]
fn test_stref_v() {
    let db = mkdb(b"$v X $. ${ $v Y Z $. $}");
    let seg = db.parse_result().segments(..).next().unwrap();
    let vx = seg.statement(0);
    let vyz = seg.statement(2);
    assert_eq!(vx.statement_type(), StatementType::Variable);
    assert_eq!(vyz.statement_type(), StatementType::Variable);
    assert_eq!(vyz.index(), 2);
    assert_eq!(vx.scope_range().end, NO_STATEMENT);
    assert_eq!(vyz.scope_range().end, 3);
    assert!(!vx.in_group());
    assert!(vyz.in_group());
    assert_eq!(vyz.label(), b"");
    assert_eq!(vyz.math_len(), 2);
    assert_eq!(vyz.proof_len(), 0);
    assert_eq!(vx.math_span(0), Span::new(3, 4));
    assert_eq!(vyz.span_full(), Span::new(10, 20));
    assert_eq!(vyz.span(), Span::new(11, 20));
    let tli: Vec<_> = vyz.math_iter().map(TokenRef::index).collect();
    assert_eq!(tli, vec![0i32, 1i32]);
    let zz: Vec<Vec<u8>> = vyz.math_iter().map(|z| (*z).to_owned()).collect();
    assert_eq!(zz, vec![b"Y", b"Z"]);
}

#[test]
fn test_inclusion() {
    use Diagnostic::*;
    macro_rules! test {
        (   $start:literal: { $($name:literal = $text:literal),* $(,)? };
            parse [$($e:expr),* $(,)?];
            errors [$($parse:expr),* $(,)?];
        ) => {{
            use StatementType::*;
            let mut db = Database::default();
            db.parse($start.to_owned(), vec![$(($name.to_owned(), $text.to_vec()),)*]);
            assert_eq!(
                db.parse_result()
                    .segments(..)
                    .map(|seg| {
                        seg.into_iter()
                            .map(|stmt| stmt.statement_type())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
                [$($e.to_vec(),)*].to_vec()
            );
            let diags = db.parse_result().parse_diagnostics();
            assert_eq!(diags.into_iter().map(|e| e.1).collect::<Vec<_>>(), vec![$($parse,)*]);
        }}
    }
    test!(
        "A": { "A" = b"$[ B $] $c a $.", "B" = b"$[ B $] ${ $}" };
        parse [[FileInclude], [FileInclude], [OpenGroup, CloseGroup, Eof], [Constant, Eof]];
        errors [];
    );
    test!(
        "A": { "A" = b"${ $[ B $] $}", "B" = b"$c b $." };
        parse [[OpenGroup, FileInclude], [Constant, Eof], [CloseGroup, Eof]];
        errors [UnclosedBeforeInclude(1), UnmatchedCloseGroup];
    );
    test!(
        "A": { "A" = b"${ $c b $. $}" };
        parse [[OpenGroup, Constant, CloseGroup, Eof]];
        errors [ConstantNotTopLevel];
    );
}

macro_rules! parse_test {
    ($name:ident, $text:expr, $diags:expr) => {
        #[test]
        fn $name() {
            let db = mkdb($text);
            let seg = db.parse_result().segments(..).next().unwrap();
            assert_eq!(seg.diagnostics, &$diags);
        }
    };
}

parse_test!(test_valid_whitespace, b" \t\r\n\x0C", []);
parse_test!(
    test_invalid_c0,
    b"$c\0X $.",
    [(0, Diagnostic::BadCharacter(2, 0))]
);
parse_test!(
    test_invalid_del,
    b"$c X Y\x7F $.",
    [(0, Diagnostic::BadCharacter(6, 0x7F))]
);

parse_test!(
    test_j_valid,
    b"$( $j usage 'exel' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13' 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pow'; $)",
    []
);

parse_test!(
    test_j_missing_closing_quote,
    b"$( $j usage 'exel $)",
    [(
        0,
        Diagnostic::UnclosedCommandString(Span { start: 13, end: 20 })
    )]
);

parse_test!(
    test_j_unclosed_comment,
    b"$( $j usage /* $)",
    [(
        0,
        Diagnostic::UnclosedCommandComment(Span { start: 12, end: 17 })
    )]
);

parse_test!(
    test_j_missing_whitespace,
    b"$( $j usage 'exel' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13''ax-ext' 'ax-sep' 'ax-nul' 'ax-pow'; $)",
    []
);

macro_rules! parse_command_test {
    ($name:ident, $text:expr, $commands:expr) => {
        #[test]
        fn $name() {
            let commands = commands($text, b'j', 0);
            let parsed = commands.and_then(|iter| {
                Ok(iter
                    .map(|command| {
                        command.and_then(|(span, tokens)| {
                            Ok((
                                span,
                                tokens
                                    .into_iter()
                                    .map(|token| as_str(&token.value($text)).to_owned())
                                    .collect::<Vec<_>>(),
                            ))
                        })
                    })
                    .collect::<Vec<_>>())
            });
            let expected = Ok($commands
                .into_iter()
                .map(|item| {
                    item.and_then(|(start, end, tokens)| {
                        Ok((
                            Span::new(start, end),
                            tokens
                                .into_iter()
                                .map(|token| token.to_string())
                                .collect::<Vec<_>>(),
                        ))
                    })
                })
                .collect::<Vec<_>>());
            assert_eq!(parsed, expected);
        }
    };
}

parse_command_test!(
    test_command_valid,
    b"$( $j usage 'exel' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13' 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pow'; $)",
    [Ok((
        6,
        129,
        [
            "usage", "exel", "avoids", "ax-5", "ax-7", "ax-8", "ax-9", "ax-10", "ax-11", "ax-12",
            "ax-13", "ax-ext", "ax-sep", "ax-nul", "ax-pow"
        ]
    ))]
);

parse_command_test!(
    test_command_comment,
    b"$( $j usage /* comment, may contain ; * / and ' - ignored */ 'exel' avoids 'ax-5'; $)",
    [Ok((6, 82, ["usage", "exel", "avoids", "ax-5"]))]
);

parse_command_test!(
    test_command_stop_at_end_tag,
    b"$( $j usage 'exel' avoids 'ax-5'; $) Nothing is parsed here",
    [Ok((6, 33, ["usage", "exel", "avoids", "ax-5"]))]
);

type NoCommandType = [Result<(usize, usize, [&'static str; 0]), Diagnostic>; 0];
const NO_COMMANDS: NoCommandType = [];
parse_command_test!(test_command_empty_list, b"$( $j $)", NO_COMMANDS);

parse_command_test!(
    test_command_more_commands,
    b"$( $j
            syntax 'wff';
            syntax '|-' as 'wff';
            unambiguous 'klr 5';
        $)",
    [
        Ok((18, 31, vec!["syntax", "wff"])),
        Ok((44, 65, vec!["syntax", "|-", "as", "wff"])),
        Ok((78, 98, vec!["unambiguous", "klr 5"]))
    ]
);

parse_command_test!(
    test_command_missing_semicolon,
    b"$( $j usage 'exel' avoids 'ax-5' $)",
    [Err::<(usize, usize, Vec<&str>), Diagnostic>(
        Diagnostic::UnclosedCommand(Span::new(6, 35))
    )]
);

parse_command_test!(
    test_command_double_quote_escape,
    b"$( $j abc \"de\"\"f\" 'ghi'; $)",
    [Ok((6, 24, ["abc", "de\"f", "ghi"]))]
);

parse_command_test!(
    test_command_unclosed_comment,
    b"$( $j usage /* unclosed comment",
    [Err::<(usize, usize, Vec<&str>), Diagnostic>(
        Diagnostic::UnclosedCommandComment(Span::new(12, 31))
    )]
);

parse_command_test!(
    test_command_missing_whitespace,
    b"$( $j usage 'exel' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-11'
       'ax-12' 'ax-13''ax-ext' 'ax-sep' 'ax-nul' 'ax-pow'; $)",
    [Ok((
        6,
        128,
        [
            "usage",
            "exel",
            "avoids",
            "ax-5",
            "ax-7",
            "ax-8",
            "ax-9",
            "ax-10",
            "ax-11",
            "ax-12",
            "ax-13'ax-ext",
            "ax-sep",
            "ax-nul",
            "ax-pow"
        ]
    ))]
);

parse_command_test!(
    test_command_missing_closing_quote,
    b"$( $j usage 'exel' avoids 'ax-5' 'ax-7' 'ax-8' 'ax-9' 'ax-10 'ax-11'
       'ax-12' 'ax-13' 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pow'; $)",
    [
        Err::<(usize, usize, Vec<&str>), Diagnostic>(Diagnostic::MissingSpaceAfterCommandToken(
            Span::new(55, 62)
        )),
        Ok((
            62,
            128,
            vec!["ax-11'", "ax-12", "ax-13", "ax-ext", "ax-sep", "ax-nul", "ax-pow"]
        ))
    ]
);
