use metamath_rs::{as_str, Database, StatementRef, StatementType};

pub fn list_statements(
    db: &Database,
    label_test: impl Fn(&[u8]) -> bool,
    out: &mut impl std::io::Write,
) -> Result<(), std::io::Error> {
    let separator = "-".repeat(79);
    let scope = db.scope_result();
    let name = db.name_result();
    for stmt in db.statements() {
        if let StatementType::Axiom | StatementType::Provable = stmt.statement_type() {
            let label = stmt.label();
            if label_test(label) {
                if let Some(frame) = scope.get(label) {
                    for (ix1, ix2) in &*frame.mandatory_dv {
                        writeln!(
                            out,
                            "$d {} {} $.",
                            as_str(name.atom_name(frame.var_list[*ix1])),
                            as_str(name.atom_name(frame.var_list[*ix2]))
                        )?;
                    }
                    for hyp in frame.hypotheses.iter().skip(frame.mandatory_count) {
                        write_statement(db.statement_by_address(hyp.address()), out)?;
                    }
                    write_statement(stmt, out)?;
                    writeln!(out, "{}", separator)?;
                }
            }
        }
    }
    Ok(())
}

pub fn write_statement(
    stmt: StatementRef,
    out: &mut impl std::io::Write,
) -> Result<(), std::io::Error> {
    write!(
        out,
        "{} ${}",
        as_str(stmt.label()),
        match stmt.statement_type() {
            StatementType::Axiom => "a",
            StatementType::Essential => "e",
            StatementType::Provable => "p",
            _ => "x",
        }
    )?;
    for token in stmt.math_iter() {
        write!(out, " {}", as_str(&token))?;
    }
    writeln!(out)?;
    Ok(())
}
