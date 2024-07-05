use crate::{diag::Diagnostic, grammar_tests::mkdb};
use assert_matches::assert_matches;

#[test]
fn issue_163() {
    let mut db = mkdb(
        b"$c term |- R $.
        $v x y $.
        x-term $f term x $.
        y-term $f term y $.
        
        R-any $a |- x R y $.
        R-id $p |- x R x $= x-term x-term R-any $.
        
        $( The offending $d may come after multiple declarations $)
        $v z $.
        z-term $f term z $.
        padding-lemma $a |- x R x $.
        
        $d x y $.",
    );

    assert!(db.parse_result().parse_diagnostics().is_empty());
    assert!(db.verify_pass().diagnostics().is_empty());

    db = mkdb(
        b"$c term |- R $.
        $v x y $.
        x-term $f term x $.
        y-term $f term y $.
        
        $d x y $.

        R-any $a |- x R y $.
        R-id $p |- x R x $= x-term x-term R-any $.",
    );

    assert!(db.parse_result().parse_diagnostics().is_empty());
    assert_matches!(
        *db.verify_pass().diagnostics(),
        [(_, Diagnostic::ProofDvViolation)]
    );
}
