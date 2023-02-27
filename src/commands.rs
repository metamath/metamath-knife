//! A parser for the different `$j` commands of the database
//! Currently supports:
//! - `syntax`
use crate::{formula::TypeCode, nameck::Nameset, segment_set::SegmentSet, statement::CommandToken};

/// Parser commands for the database
#[derive(Debug)]
pub struct Commands {
    /// The provable type, typically `|-`
    pub provable_type: TypeCode,
    /// The logical type, typically `wff`
    pub logic_type: TypeCode,
    /// A list of all typecodes, e.g. `wff`, `class`, `setvar`
    pub typecodes: Vec<TypeCode>,
}

impl Commands {
    /// Parses the commands
    pub(crate) fn new(sset: &SegmentSet, nset: &Nameset) -> Self {
        let mut provable_type = TypeCode::default();
        let mut logic_type = TypeCode::default();
        let mut typecodes = vec![];
        for sref in sset.segments(..) {
            let buf = &**sref.buffer;
            for (_, (_, command)) in &sref.j_commands {
                use CommandToken::*;
                match &**command {
                    [Keyword(cmd), sort, Keyword(as_), logic]
                        if cmd.as_ref(buf) == b"syntax" && as_.as_ref(buf) == b"as" =>
                    {
                        provable_type = nset.lookup_symbol(sort.value(buf)).unwrap().atom;
                        logic_type = nset.lookup_symbol(logic.value(buf)).unwrap().atom;
                        typecodes.push(logic_type);
                    }
                    [Keyword(cmd), sort] if cmd.as_ref(buf) == b"syntax" => {
                        typecodes.push(nset.lookup_symbol(sort.value(buf)).unwrap().atom)
                    }
                    _ => {}
                }
            }
        }
        Commands {
            provable_type,
            logic_type,
            typecodes,
        }
    }
}
