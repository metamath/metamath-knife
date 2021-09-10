use crate::database::Database;
use crate::database::DbOptions;
use crate::parser::as_str;

const GRAMMAR_DB : &[u8] = b"
    $c |- wff class ( ) + = $.
    $( $j syntax 'class'; syntax 'wff'; syntax '|-' as 'wff'; $)
    $v A B $.
    cA $f class A $.
    cB $f class B $.
    weq $a wff A = B $.
    cadd $a class ( A + B ) $.
    ax-com $a |- ( A + B ) = ( B + A ) $.
";

pub fn mkdb(text: &[u8]) -> Database {
    let mut options = DbOptions::default();
    options.incremental = true;
    let mut db = Database::new(options);
    db.parse("test.mm".to_owned(),
             vec![("test.mm".to_owned(), text.to_owned())]);
    db
}

#[test]
fn test_lookup() {
    let mut db = mkdb(GRAMMAR_DB);
    let names = db.name_result();
    assert!(as_str(names.atom_name(names.lookup_symbol(b"A").unwrap().atom)) == "A");
    assert!(as_str(names.atom_name(names.lookup_symbol(b"B").unwrap().atom)) == "B");
    assert!(as_str(names.atom_name(names.lookup_label(b"weq").unwrap().atom)) == "weq");
    assert!(as_str(names.atom_name(names.lookup_label(b"cadd").unwrap().atom)) == "cadd");
}

#[test]
fn test_db_stmt_parse() {
    let mut db = mkdb(GRAMMAR_DB);
    let sset = db.parse_result().clone();
    let grammar = db.grammar_result().clone();
    let stmt_parse = db.stmt_parse_result().clone();
    assert!(sset.parse_diagnostics().len() == 0);
    assert!(grammar.diagnostics().len() == 0);
    assert!(stmt_parse.diagnostics().len() == 0);
}

#[test]
fn test_db_formula() {
    let mut db = mkdb(GRAMMAR_DB);
    let stmt_parse = db.stmt_parse_result().clone();
    let names = db.name_result().clone();
    {
        let sref = db.statement("ax-com").unwrap();
        let formula = stmt_parse.get_formula(&sref).unwrap();
        assert!(as_str(names.atom_name(formula.get_by_path(&[]).unwrap())) == "weq");
        assert!(as_str(names.atom_name(formula.get_by_path(&[1]).unwrap())) == "cadd");
        assert!(as_str(names.atom_name(formula.get_by_path(&[1,1]).unwrap())) == "cA");
        assert!(as_str(names.atom_name(formula.get_by_path(&[1,2]).unwrap())) == "cB");
        assert!(as_str(names.atom_name(formula.get_by_path(&[2]).unwrap())) == "cadd");
        assert!(as_str(names.atom_name(formula.get_by_path(&[2,1]).unwrap())) == "cB");
        assert!(as_str(names.atom_name(formula.get_by_path(&[2,2]).unwrap())) == "cA");
    }
}
