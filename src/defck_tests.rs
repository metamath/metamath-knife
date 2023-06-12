use crate::grammar_tests::mkdb;
use crate::diag::Diagnostic::*;
use assert_matches::assert_matches;

const DEFCK_DB: &[u8] = b"
$c |- wff fruit + eq1 eq2 $.
$( $j syntax 'fruit'; syntax 'wff'; syntax '|-' as 'wff'; $)
$v apple orange banana $.
fa $f fruit apple $.
fb $f fruit banana $.
fo $f fruit orange $.
malformed $a wff apple + banana + orange $.
$( $j primitive 'malformed'; equality 'malformed' from 'eqfid' 'eqfcomi' 'eqftri'; $)

weq1 $a wff apple eq1 banana $.
$( $j primitive 'weq1'; equality 'weq1' from 'ax-eq1id' 'ax-eq1comi' 'ax-eq1tri'; $)

weq2 $a wff apple eq2 banana $.
$( $j primitive 'weq2'; equality 'weq2' from 'eq2id' 'eq2comi' 'eq2tri'; $)

ax-eq1id $a |- apple eq1 apple $.
${
    ax-eq1comi.1 $e |- apple eq1 banana $.
    ax-eq1comi $a |- banana eq1 apple $.
$}
${
    ax-eq1tri.1 $e |- apple eq1 banana $.
    ax-eq1tri.2 $e |- banana eq1 orange $.
    ax-eq1tri $a |- apple eq1 orange $.
$}
";

#[test]
fn test_defck() {
    let mut db = mkdb(DEFCK_DB);
    assert_eq!(db.parse_result().parse_diagnostics(),vec![]);
    let names = db.name_pass().clone();
    let defck = db.definitions_pass();
    let diags = defck.diagnostics();

    assert_eq!(diags.len(), 2);

    // Malformed Equality 'apple + banana + orange'
    assert_matches!(diags[0], (_, DefCkMalformedEquality(..)));
    let DefCkMalformedEquality(malformed, _) = diags[0].1.clone() else { panic!() };
    assert_eq!(malformed, names.lookup_label(b"malformed").unwrap().address);

    // Duplicated Equality for 'fruit'
    assert_matches!(diags[1], (_, DefCkDuplicateEquality(..)));
    let DefCkDuplicateEquality(dup_typecode, ..) = diags[1].1.clone() else { panic!() };
    assert_eq!(&*dup_typecode, b"fruit");
}