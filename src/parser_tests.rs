use crate::database::Database;
use crate::diag::Diagnostic;
use crate::parser::Comparer;
use crate::parser::SegmentOrder;
use crate::parser::Span;
use crate::parser::StatementAddress;
use crate::parser::StatementType;
use crate::parser::TokenRef;
use crate::parser::NO_STATEMENT;
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
    let zz: Vec<Vec<u8>> = vyz.math_iter().map(|z| (&*z).to_owned()).collect();
    assert_eq!(zz, vec![b"Y", b"Z"]);
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
