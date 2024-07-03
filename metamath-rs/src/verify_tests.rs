use crate::grammar_tests::mkdb;

#[test]
fn issue_163() {
    const DB: &[u8] = b"
        $c term |- R $.
        $v x y $.
        x-term $f term x $.
        y-term $f term y $.
        
        R-any $a |- x R y $.
        R-id $p |- x R x $= x-term x-term R-any $.
        
        $( The offending $d may come after multiple declarations $)
        $v z $.
        z-term $f term z $.
        padding-lemma $a |- x R x $.
        
        $d x y $.
    ";
    let mut db = mkdb(DB);

    assert!(db.parse_result().parse_diagnostics().is_empty());
    assert!(db.verify_pass().diagnostics().is_empty());
}
