use std::sync::Arc;

use crate::as_str;
use crate::database::Database;
use crate::database::DbOptions;
use crate::diag::Diagnostic;
use crate::grammar::FormulaToken;
use crate::nameck::Nameset;
use crate::statement::SegmentId;
use crate::statement::StatementAddress;
use crate::Span;

macro_rules! sa {
    ($id: expr, $index:expr) => {
        StatementAddress {
            segment_id: SegmentId($id),
            index: $index,
        }
    };
}

const GRAMMAR_DB: &[u8] = b"
    $c |- wff class ( ) + = $.
    $( $j syntax 'class'; syntax 'wff'; syntax '|-' as 'wff'; $)
    $v A B $.
    cA $f class A $.
    cB $f class B $.
    weq $a wff A = B $.
    cadd $a class ( A + B ) $.
    ax-com $a |- ( A + B ) = ( B + A ) $.
";

pub(super) fn mkdb(text: &[u8]) -> Database {
    let options = DbOptions {
        incremental: true,
        ..DbOptions::default()
    };
    let mut db = Database::new(options);
    db.parse(
        "test.mm".to_owned(),
        vec![("test.mm".to_owned(), text.to_owned())],
    );
    db
}

#[test]
fn test_lookup() {
    let mut db = mkdb(GRAMMAR_DB);
    let names = db.name_pass();
    assert_eq!(
        as_str(names.atom_name(names.lookup_symbol(b"A").unwrap().atom)),
        "A"
    );
    assert_eq!(
        as_str(names.atom_name(names.lookup_symbol(b"B").unwrap().atom)),
        "B"
    );
    assert_eq!(
        as_str(names.atom_name(names.lookup_label(b"weq").unwrap().atom)),
        "weq"
    );
    assert_eq!(
        as_str(names.atom_name(names.lookup_label(b"cadd").unwrap().atom)),
        "cadd"
    );
}

#[test]
fn test_db_stmt_parse() {
    let mut db = mkdb(GRAMMAR_DB);
    let sset = db.parse_result().clone();
    let grammar = db.grammar_pass().clone();
    let stmt_parse = db.stmt_parse_pass().clone();
    assert!(sset.parse_diagnostics().is_empty());
    assert!(grammar.diagnostics().is_empty());
    assert!(stmt_parse.diagnostics().is_empty());
}

#[test]
fn test_db_formula() {
    let mut db = mkdb(GRAMMAR_DB);
    let stmt_parse = db.stmt_parse_pass().clone();
    {
        let sref = db.statement(b"ax-com").unwrap();
        let formula = stmt_parse.get_formula(&sref).unwrap();
        assert_eq!(
            formula.as_ref(&db).as_sexpr(),
            "(weq (cadd cA cB) (cadd cB cA))"
        );
    }
}

fn make_tok(t: &[u8], names: &Arc<Nameset>) -> FormulaToken {
    FormulaToken {
        symbol: names.lookup_symbol(t).unwrap().atom,
        span: Span::default(),
    }
}

#[test]
fn test_parse_formula() {
    let mut db = mkdb(GRAMMAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = names.lookup_symbol(b"wff").unwrap().atom;
    let class = names.lookup_symbol(b"class").unwrap().atom;
    let a = make_tok(b"A", &names);
    let b = make_tok(b"B", &names);
    let eq = make_tok(b"=", &names);
    let plus = make_tok(b"+", &names);
    let open_parens = make_tok(b"(", &names);
    let close_parens = make_tok(b")", &names);
    let fmla_vec = vec![a, eq, open_parens, b, plus, a, close_parens];
    let formula = grammar
        .parse_formula(
            &mut fmla_vec.clone().into_iter(),
            &[wff, class],
            false,
            &names,
        )
        .unwrap();
    // Accessing formula using paths to labels
    assert_eq!(
        as_str(names.atom_name(formula.get_by_path(&[]).unwrap())),
        "weq"
    );
    assert_eq!(
        as_str(names.atom_name(formula.get_by_path(&[0]).unwrap())),
        "cA"
    );
    assert_eq!(
        as_str(names.atom_name(formula.get_by_path(&[1]).unwrap())),
        "cadd"
    );
    assert_eq!(
        as_str(names.atom_name(formula.get_by_path(&[1, 0]).unwrap())),
        "cB"
    );
    assert_eq!(
        as_str(names.atom_name(formula.get_by_path(&[1, 1]).unwrap())),
        "cA"
    );
    // Accessing formula as S-Expression
    assert_eq!(formula.as_ref(&db).as_sexpr(), "(weq cA (cadd cB cA))");
    // Accessing formula as flattened string of tokens
    assert!(formula
        .as_ref(&db)
        .iter()
        .eq(fmla_vec.into_iter().map(|t| t.symbol)));
}

#[test]
fn test_parse_string() {
    let mut db = mkdb(GRAMMAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let formula = grammar.parse_string("|- A = ( B + A )", &names).unwrap();
    assert_eq!(formula.as_ref(&db).as_sexpr(), "(weq cA (cadd cB cA))");
    let formula = grammar
        .parse_string("|- A\n   = ( B + A )\n\n", &names)
        .unwrap();
    assert_eq!(formula.as_ref(&db).as_sexpr(), "(weq cA (cadd cB cA))");
}

// This grammar exposes issue #32 in the statement parser
const GRAMMAR_DB_32: &[u8] = b"
    $c |- wff class setvar ( ) = e. |-> $.
    $( $j syntax 'class'; syntax 'setvar'; syntax 'wff'; syntax '|-' as 'wff'; type_conversions; $)
    $v A B C x $.
    cA $f class A $.
    cB $f class B $.
    cC $f class C $.
    vx $f setvar x $.
    cv $a class x $.
    weq $a wff A = B $.
    cov $a class ( A B C ) $.
    cmpt $a class ( x e. A |-> B ) $.
    check $a |- ( x A B ) = C $.
";

#[test]
fn test_db_32_formula() {
    let mut db = mkdb(GRAMMAR_DB_32);
    let stmt_parse = db.stmt_parse_pass().clone();
    {
        let sref = db.statement(b"check").unwrap();
        let formula = stmt_parse.get_formula(&sref).unwrap();
        assert_eq!(
            formula.as_ref(&db).as_sexpr(),
            "(weq (cov (cv vx) cA cB) cC)"
        );
    }
}

#[test]
fn test_setvar_as_class() {
    let mut db = mkdb(GRAMMAR_DB_32);
    let grammar = db.grammar_pass().clone();
    let names = db.name_pass().clone();
    let class_symbol = names.lookup_symbol(b"class").unwrap().atom;
    let x_symbol = FormulaToken {
        symbol: names.lookup_symbol(b"x").unwrap().atom,
        span: Span::default(),
    };
    {
        let formula = grammar
            .parse_formula(
                &mut vec![x_symbol].into_iter(),
                &[class_symbol],
                false,
                &names,
            )
            .unwrap();
        assert_eq!(formula.as_ref(&db).as_sexpr(), "(cv vx)");
    }
}

// This grammar exposes issue #43 in the statement parser
const GRAMMAR_DB_43: &[u8] = b"
    $c |- wff class setvar ( ) { } = e. | |-> /\\ $.
    $( $j syntax 'class'; syntax 'setvar'; syntax 'wff'; syntax '|-' as 'wff';
          type_conversions; garden_path ( x e. A   =>   ( ph ; $)
    $v ph ps A B x $.
    wph $f wff ph $.
    wps $f wff ps $.
    cA $f class A $.
    cB $f class B $.
    vx $f setvar x $.
    cv $a class x $.
    weq $a wff A = B $.
    wcel $a wff A e. B $.
    wa $a wff ( ph /\\ ps ) $.
    cab $a class { x | ph } $.
    cmpt $a class ( x e. A |-> B ) $.
    check $a |- { x | ( x e. A /\\ ph ) } = B $.
";

#[test]
fn test_db_43_formula() {
    let mut db = mkdb(GRAMMAR_DB_43);
    let stmt_parse = db.stmt_parse_pass().clone();
    {
        let sref = db.statement(b"check").unwrap();
        let formula = stmt_parse.get_formula(&sref).unwrap().as_ref(&db);
        assert_eq!(
            formula.as_sexpr(),
            "(weq (cab vx (wa (wcel (cv vx) cA) wph)) cB)"
        );
    }
}

// A minimal set.mm-like database with "Garden Paths"
const GARDEN_PATH_DB: &[u8] = b"
    $c |- wff class setvar { } <. >. , | e. = $.
    $( $j syntax 'class'; syntax 'wff'; syntax '|-' as 'wff';
        type_conversions; garden_path { <.   =>   { A ;
    $)
    $v ph A B C D x y $.
    wph $f wff ph $.
    cA $f class A $.
    cB $f class B $.
    cC $f class C $.
    cD $f class D $.
    vx $f setvar x $.
    vy $f setvar y $.
    cv $a class x $.
    weq $a wff A = B $.
    csn $a class { A } $.
    cop $a class <. A , B >. $.
    copab $a class { <. x , y >. e. A | ph } $.
    formula1 $a |- A = { <. B , C >. } $.
    formula2 $a |- A = { <. x , y >. } $.
    formula3 $a |- A = { <. x , y >. e. B | C = D } $.
";

#[test]
fn test_garden_path_1() {
    let mut db = mkdb(GARDEN_PATH_DB);
    let sset = db.parse_result().clone();
    let stmt_parse = db.stmt_parse_pass().clone();
    assert!(sset.parse_diagnostics().is_empty());
    let sref = db.statement(b"formula1").unwrap();
    let formula = stmt_parse.get_formula(&sref).unwrap();
    assert_eq!(formula.as_ref(&db).as_sexpr(), "(weq cA (csn (cop cB cC)))");
}

#[test]
fn test_garden_path_2() {
    let mut db = mkdb(GARDEN_PATH_DB);
    let stmt_parse = db.stmt_parse_pass().clone();
    let sref = db.statement(b"formula2").unwrap();
    let formula = stmt_parse.get_formula(&sref).unwrap();
    assert_eq!(
        formula.as_ref(&db).as_sexpr(),
        "(weq cA (csn (cop (cv vx) (cv vy))))"
    );
}

#[test]
fn test_garden_path_3() {
    let mut db = mkdb(GARDEN_PATH_DB);
    let stmt_parse = db.stmt_parse_pass().clone();
    let sref = db.statement(b"formula3").unwrap();
    let formula = stmt_parse.get_formula(&sref).unwrap();
    assert_eq!(
        formula.as_ref(&db).as_sexpr(),
        "(weq cA (copab vx vy cB (weq cC cD)))"
    );
}

macro_rules! grammar_test {
    ($name:ident, $text:expr, $id: expr, $index:expr, $diag:expr) => {
        #[test]
        fn $name() {
            let mut db = mkdb($text);
            let sset = db.parse_result().clone();
            let grammar = db.grammar_pass();
            assert!(sset.parse_diagnostics().is_empty());
            assert_eq!(grammar.diagnostics(), &[(sa!($id, $index), $diag)]);
        }
    };
}

grammar_test!(
    test_missing_float,
    b"$c setvar $. $v x $. vx $a setvar x $.",
    2,
    2,
    Diagnostic::VariableMissingFloat(1)
);
grammar_test!(
    test_ambiguous,
    b"$c A B $. a1 $a A B $. a2 $a A B $.",
    2,
    2,
    Diagnostic::GrammarAmbiguous(sa!(2, 1))
);
grammar_test!(
    test_float_not_var,
    b"$c setvar $. vx $f setvar x $.",
    2,
    1,
    Diagnostic::FloatNotVariable(1)
);
grammar_test!(
    test_unknown_token_1,
    b"$c |- $. err $a |- unknown $.",
    2,
    1,
    Diagnostic::UndefinedToken(crate::Span::new(19, 26), Box::new(*b"unknown"))
);
grammar_test!(
    test_unknown_token_2,
    b"$c |- ( $. err $a |- ( unknown $.",
    2,
    1,
    Diagnostic::UndefinedToken(crate::Span::new(23, 30), Box::new(*b"unknown"))
);
