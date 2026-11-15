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
            &mut fmla_vec.iter().map(|t| Ok(*t)),
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
    // Accessing formula labels
    let map_label = |(label, is_var)| (as_str(names.atom_name(label)), is_var);
    let mut labels = formula.labels_iter();
    assert_eq!(labels.next().map(map_label), Some(("weq", false)));
    assert_eq!(labels.next().map(map_label), Some(("cA", true)));
    assert_eq!(labels.next().map(map_label), Some(("cadd", false)));
    assert_eq!(labels.next().map(map_label), Some(("cB", true)));
    assert_eq!(labels.next().map(map_label), Some(("cA", true)));
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
                &mut std::iter::once(Ok(x_symbol)),
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

const ISSUE_135: &[u8] = b"
    $c = class wff setvar -> ( ) |- + [ ] $.
    $( $j syntax 'setvar' 'class' 'wff'; syntax '|-' as 'wff'; $)
    $( $j type_conversions; garden_path ( x => ( ph ; $)
    $v x A B ph ps $.
    vx $f setvar x $.
    wph $f wff ph $.
    wps $f wff ps $.
    cA $f class A $.
    cB $f class B $.
    cv $a class x $.
    wn $a wff [ A ] $.
    wceq $a wff A = B $.
    wi $a wff ( ph -> ps ) $.
    cdif $a class ( A + B ) $.
    ax1 $a |- [ x ] $.
    ax2 $a |- ( x = x -> ph ) $.
";

#[test]
fn test_issue_135() {
    let mut db = mkdb(ISSUE_135);
    let stmt_parse = db.stmt_parse_pass().clone();
    let sref = db.statement(b"ax1").unwrap();
    let formula = stmt_parse.get_formula(&sref).unwrap();
    assert_eq!(formula.as_ref(&db).as_sexpr(), "(wn (cv vx))");
    let sref = db.statement(b"ax2").unwrap();
    let formula = stmt_parse.get_formula(&sref).unwrap();
    assert_eq!(
        formula.as_ref(&db).as_sexpr(),
        "(wi (wceq (cv vx) (cv vx)) wph)"
    );
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

// ---- Work-variable hook in `parse_formula_with` (0601a) ----

use crate::diag::StmtParseError;
use crate::formula::{Label, TypeCode};
use crate::grammar::{FormulaNodeBuilder, ParseToken, TokenKind};

const WORK_VAR_DB: &[u8] = b"
    $c |- wff class setvar ( ) -> = $.
    $( $j syntax 'class'; syntax 'setvar'; syntax 'wff'; syntax '|-' as 'wff'; type_conversions; $)
    $v ph ps x A B $.
    wph $f wff ph $.
    wps $f wff ps $.
    vx $f setvar x $.
    cA $f class A $.
    cB $f class B $.
    cv $a class x $.
    wi $a wff ( ph -> ps ) $.
    weq $a wff A = B $.
";

#[derive(Clone, Copy, Debug)]
enum TestToken {
    Sym(FormulaToken),
    Work(u32, TypeCode),
}

impl ParseToken for TestToken {
    type WorkVar = u32;
    fn span(&self) -> Span {
        match self {
            TestToken::Sym(t) => t.span,
            TestToken::Work(..) => Span::NULL,
        }
    }
    fn kind(&self) -> TokenKind<u32> {
        match *self {
            TestToken::Sym(t) => TokenKind::Symbol(t.symbol),
            TestToken::Work(id, tc) => TokenKind::WorkVar(id, tc),
        }
    }
}

/// Renders s-expressions in `as_sexpr`'s format (work variables as `&W<id>`) and logs calls.
struct SexprBuilder<'a> {
    names: &'a Nameset,
    log: Vec<String>,
}

impl<'a> SexprBuilder<'a> {
    fn new(names: &'a Nameset) -> Self {
        SexprBuilder { names, log: vec![] }
    }
    fn name(&self, atom: Label) -> String {
        as_str(self.names.atom_name(atom)).to_owned()
    }
}

impl FormulaNodeBuilder for SexprBuilder<'_> {
    type Node = String;
    type WorkVar = u32;
    fn variable(&mut self, label: Label) -> String {
        let n = self.name(label);
        self.log.push(format!("variable({n})"));
        n
    }
    fn work_var(&mut self, id: u32, typecode: TypeCode) -> String {
        let tc = self.name(typecode);
        self.log.push(format!("work_var({id}, {tc})"));
        let prefix = match tc.as_str() {
            "class" => "&C",
            "setvar" => "&S",
            _ => "&W",
        };
        format!("{prefix}{id}")
    }
    fn node(&mut self, label: Label, children: Vec<String>) -> String {
        let n = self.name(label);
        self.log
            .push(format!("node({n}, {} children)", children.len()));
        if children.is_empty() {
            n
        } else {
            format!("({n} {})", children.join(" "))
        }
    }
}

fn tc(names: &Nameset, t: &[u8]) -> TypeCode {
    names.lookup_symbol(t).unwrap().atom
}

/// Tokenizes a space-separated string; `&W<n>`, `&C<n>`, `&S<n>` are wff, class, setvar work variables.
fn work_toks(s: &str, names: &Nameset) -> Vec<TestToken> {
    s.split_whitespace()
        .map(|t| {
            let kind = match t.get(..2) {
                Some("&W") => Some(b"wff".as_slice()),
                Some("&C") => Some(b"class".as_slice()),
                Some("&S") => Some(b"setvar".as_slice()),
                _ => None,
            };
            match kind {
                Some(k) => TestToken::Work(t[2..].parse().unwrap(), tc(names, k)),
                None => TestToken::Sym(FormulaToken {
                    symbol: names.lookup_symbol(t.as_bytes()).unwrap().atom,
                    span: Span::default(),
                }),
            }
        })
        .collect()
}

fn parse_with(
    grammar: &crate::grammar::Grammar,
    names: &Nameset,
    s: &str,
    expected: &[TypeCode],
    convert_to_provable: bool,
) -> (Result<(String, TypeCode), StmtParseError>, Vec<String>) {
    let toks = work_toks(s, names);
    let mut builder = SexprBuilder::new(names);
    let res = grammar.parse_formula_with(
        &mut toks.into_iter().map(Ok),
        expected,
        convert_to_provable,
        names,
        &mut builder,
    );
    (res, builder.log)
}

#[test]
fn work_var_basic() {
    let mut db = mkdb(WORK_VAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = tc(&names, b"wff");
    let (res, log) = parse_with(&grammar, &names, "( &W1 -> ph )", &[wff], false);
    assert_eq!(res.unwrap(), ("(wi &W1 wph)".to_owned(), wff));
    assert_eq!(
        log,
        vec!["work_var(1, wff)", "variable(wph)", "node(wi, 2 children)"]
    );
    assert!(names.lookup_symbol(b"&W1").is_none());
}

#[test]
fn work_var_matches_declared_variable() {
    let mut db = mkdb(WORK_VAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = tc(&names, b"wff");
    for s in [
        "( &W1 -> ph )",
        "( ph -> &W1 )",
        "( ( &W1 -> &W2 ) -> ph )",
        "&W1",
    ] {
        let (work, _) = parse_with(&grammar, &names, s, &[wff], false);
        let (work_sexpr, work_tc) = work.unwrap();
        // Replace each wff work variable with `ps`, then render `wps` back as its `&W<id>`.
        let mut ids = vec![];
        let declared: Vec<&str> = s
            .split_whitespace()
            .map(|t| {
                if let Some(id) = t.strip_prefix("&W") {
                    ids.push(id.to_owned());
                    "ps"
                } else {
                    t
                }
            })
            .collect();
        let (decl, _) = parse_with(&grammar, &names, &declared.join(" "), &[wff], false);
        let (decl_sexpr, decl_tc) = decl.unwrap();
        let mut ids = ids.into_iter();
        let rendered = decl_sexpr
            .split("wps")
            .map(str::to_owned)
            .reduce(|acc, part| format!("{acc}&W{}{part}", ids.next().unwrap()))
            .unwrap();
        assert_eq!(work_sexpr, rendered, "for {s}");
        assert_eq!(work_tc, decl_tc, "for {s}");
    }
}

#[test]
fn work_var_wrong_typecode() {
    let mut db = mkdb(WORK_VAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = tc(&names, b"wff");
    for (work, declared) in [("( &C1 -> ph )", "( A -> ph )"), ("&C1", "A")] {
        let (res, _) = parse_with(&grammar, &names, work, &[wff], false);
        let mut toks = work_toks(declared, &names).into_iter().map(|t| match t {
            TestToken::Sym(t) => Ok(t),
            TestToken::Work(..) => unreachable!(),
        });
        let expected = grammar.parse_formula(&mut toks, &[wff], false, &names);
        let (Err(got), Err(want)) = (res, expected) else {
            panic!("expected both to fail for {work}");
        };
        assert_eq!(
            std::mem::discriminant(&got),
            std::mem::discriminant(&want),
            "for {work}: {got:?} vs {want:?}"
        );
    }
}

#[test]
fn work_var_type_conversion() {
    let mut db = mkdb(WORK_VAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = tc(&names, b"wff");
    let class = tc(&names, b"class");
    let (res, log) = parse_with(&grammar, &names, "&S1", &[class], false);
    assert_eq!(res.unwrap(), ("(cv &S1)".to_owned(), class));
    assert!(log.contains(&"node(cv, 1 children)".to_owned()), "{log:?}");
    let (res, _) = parse_with(&grammar, &names, "&S1 = A", &[wff], false);
    assert_eq!(res.unwrap(), ("(weq (cv &S1) cA)".to_owned(), wff));
}

#[test]
fn work_var_convert_to_provable() {
    let mut db = mkdb(WORK_VAR_DB);
    let names = db.name_pass().clone();
    let grammar = db.grammar_pass().clone();
    let wff = tc(&names, b"wff");
    let provable = tc(&names, b"|-");
    let (res, _) = parse_with(&grammar, &names, "( &W1 -> ph )", &[wff], true);
    assert_eq!(res.unwrap(), ("(wi &W1 wph)".to_owned(), provable));
}

#[test]
fn node_builder_garden_path_parity() {
    for (text, labels) in [
        (
            GARDEN_PATH_DB,
            &[b"formula1".as_slice(), b"formula2", b"formula3"][..],
        ),
        (GRAMMAR_DB_43, &[b"check".as_slice()][..]),
    ] {
        let mut db = mkdb(text);
        let names = db.name_pass().clone();
        let grammar = db.grammar_pass().clone();
        let stmt_parse = db.stmt_parse_pass().clone();
        let wff = tc(&names, b"wff");
        for &label in labels {
            let sref = db.statement(label).unwrap();
            let expected = stmt_parse
                .get_formula(&sref)
                .unwrap()
                .as_ref(&db)
                .as_sexpr();
            let mut reader = crate::nameck::NameReader::new(&names);
            let mut builder = SexprBuilder::new(&names);
            let (got, typecode) = grammar
                .parse_formula_with(
                    &mut sref.token_iter(&mut reader).map(|t| t.map(TestToken::Sym)),
                    &[wff],
                    true,
                    &names,
                    &mut builder,
                )
                .unwrap();
            assert_eq!(got, expected, "for {}", as_str(label));
            assert_eq!(typecode, tc(&names, b"|-"));
        }
    }
}
