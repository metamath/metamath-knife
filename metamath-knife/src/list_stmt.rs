use metamath_rs::{as_str, Database, StatementType};

pub fn list_statements(
    db: &Database,
    label_test: impl Fn(&[u8]) -> bool,
    out: &mut impl std::io::Write,
) -> Result<(), std::io::Error> {
    for stmt in db.statements() {
        if let StatementType::Axiom | StatementType::Essential | StatementType::Provable =
            stmt.statement_type()
        {
            let label = stmt.label();
            if label_test(label) {
                write!(out, "{}:", as_str(label))?;
                for token in stmt.math_iter() {
                    write!(out, " {}", as_str(&token))?;
                }
                writeln!(out)?;
            }
        }
    }
    Ok(())
}
