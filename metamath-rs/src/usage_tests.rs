use crate::diag::Diagnostic::{UnknownLabel, UsageViolation};
use crate::grammar_tests::mkdb;
use assert_matches::assert_matches;

const USAGE_DB: &[u8] = b"
$c wff |- > $.  $v a $.
wa $f |- a $.
ax-1 $a |- > a $.
thm1 $p |- > a $= wa ax-1 $.
$( $j usage 'thm1' avoids 'ax-1'; $)
thm2 $p |- > a $= ( ax-1 ) AB $.
$( $j usage 'thm2' avoids 'ax-1' 'ax-unknown'; $)
";

#[test]
fn test_usage() {
    let mut db = mkdb(USAGE_DB);
    assert_eq!(db.parse_result().parse_diagnostics(), vec![]);
    let usage = db.verify_usage_pass();
    let diags = usage.diagnostics();

    assert_eq!(diags.len(), 3);
    assert_matches!(diags[0], (_, UsageViolation(..)));
    assert_matches!(diags[1], (_, UsageViolation(..)));
    assert_matches!(diags[2], (_, UnknownLabel(..)));
}
