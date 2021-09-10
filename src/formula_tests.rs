use crate::grammar_tests::mkdb;
use crate::parser::as_str;

const FORMULA_DB : &[u8] = b"
    $c |- wff class ( ) + = 1 2 $.
    $( $j syntax 'class'; syntax 'wff'; syntax '|-' as 'wff'; $)
    $v A B $.
    cA $f class A $.
    cB $f class B $.
    c1 $a class 1 $.
    c2 $a class 2 $.
    weq $a wff A = B $.
    cadd $a class ( A + B ) $.
    ax-com $a |- ( A + B ) = ( B + A ) $.
    1p2com $a |- ( 1 + 2 ) = ( 2 + 1 ) $.
    ${
        addeq1.1 $e |- A = B $.
        addeq1 $a |- ( A + 1 ) = ( B + 1 ) $.
    $}
    formula $a |- ( ( 1 + 2 ) + 1 ) = ( ( 2 + 1 ) + 1 ) $.
";

#[test]
/// Unification of ` ( 1 + 2 ) = ( 2 + 1 ) ` with ` ( A + B ) = ( B + A ) `
/// Shall result in ` A := 1 ` and  ` B := 2 `
fn test_unify() {
    let mut db = mkdb(FORMULA_DB);
    let stmt_parse = db.stmt_parse_result().clone();
    let names = db.name_result().clone();
    let goal = stmt_parse.get_formula(&db.statement("1p2com").unwrap()).unwrap();
    let axiom = stmt_parse.get_formula(&db.statement("ax-com").unwrap()).unwrap();
    let subst = goal.unify(axiom).unwrap();
    let a = names.lookup_label(b"cA").unwrap().atom;
    let b = names.lookup_label(b"cB").unwrap().atom;
    assert!(as_str(names.atom_name(subst[&a].get_by_path(&[]).unwrap())) == "c1");
    assert!(as_str(names.atom_name(subst[&b].get_by_path(&[]).unwrap())) == "c2");
}

#[test]
/// Unification of ` ( 1 + 2 ) = ( 2 + 1 ) ` with ` ( A + 1 ) = ( B + 1 ) ` shall fail.
fn test_unify_fail() {
    let mut db = mkdb(FORMULA_DB);
    let stmt_parse = db.stmt_parse_result().clone();
    let goal = stmt_parse.get_formula(&db.statement("1p2com").unwrap()).unwrap();
    let axiom = stmt_parse.get_formula(&db.statement("addeq1").unwrap()).unwrap();
    assert!(goal.unify(axiom).is_none());
}

#[test]
/// Substitution of ` ( A + 1 ) = ( B + 1 ) ` with ` A := ( 1 + 2 ) ` and ` B := ( 2 + 1 ) `
/// Shall result in ` ( ( 1 + 2 ) + 1 ) = ( ( 2 + 1 ) + 1 ) `
fn test_substitute() {
    let mut db = mkdb(FORMULA_DB);
    let stmt_parse = db.stmt_parse_result().clone();
    let names = db.name_result().clone();
    let goal = stmt_parse.get_formula(&db.statement("1p2com").unwrap()).unwrap();
    let axiom = stmt_parse.get_formula(&db.statement("addeq1.1").unwrap()).unwrap();
    let subst = goal.unify(axiom).unwrap();
    let a = names.lookup_label(b"cA").unwrap().atom;
    let b = names.lookup_label(b"cB").unwrap().atom;
    assert!(as_str(names.atom_name(subst[&a].get_by_path(&[]).unwrap())) == "cadd");
    assert!(as_str(names.atom_name(subst[&a].get_by_path(&[1]).unwrap())) == "c1");
    assert!(as_str(names.atom_name(subst[&a].get_by_path(&[2]).unwrap())) == "c2");
    assert!(as_str(names.atom_name(subst[&b].get_by_path(&[]).unwrap())) == "cadd");
    assert!(as_str(names.atom_name(subst[&b].get_by_path(&[1]).unwrap())) == "c2");
    assert!(as_str(names.atom_name(subst[&b].get_by_path(&[2]).unwrap())) == "c1");
    let stmt = stmt_parse.get_formula(&db.statement("addeq1").unwrap()).unwrap();
    let formula = stmt_parse.get_formula(&db.statement("formula").unwrap()).unwrap();
    let result = stmt.substitute(&subst);
    assert!(result == *formula);
}
