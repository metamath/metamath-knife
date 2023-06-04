//! Generation of a `GraphML` file containing all theorem dependencies.

use crate::StatementType;
use crate::{as_str, database::time, Database};
use xml::writer::{EmitterConfig, XmlEvent};

use crate::diag::Diagnostic;

impl From<xml::writer::Error> for Diagnostic {
    fn from(err: xml::writer::Error) -> Diagnostic {
        Diagnostic::IoError(format!("{err}"))
    }
}

impl Database {
    /// Writes down all dependencies in a `GraphML` file format to the given writer.
    pub fn export_graphml_deps(&self, out: &mut impl std::io::Write) -> Result<(), Diagnostic> {
        time(&self.options.clone(), "export_graphml_deps", || {
            let mut writer = EmitterConfig::new().perform_indent(true).create_writer(out);
            writer.write(
                XmlEvent::start_element("graphml")
                    .attr("xmlns", "http://graphml.graphdrawing.org/xmlns")
                    .attr("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance")
                    .attr(
                        "xsi:schemaLocation",
                        "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd",
                    ),
            )?;
            writer.write(XmlEvent::start_element("grpah").attr("id", "dependencies"))?;
            for sref in self.statements().filter(|stmt| stmt.is_assertion()) {
                let label = sref.label();
                writer.write(XmlEvent::start_element("node").attr("id", as_str(label)))?;
                writer.write(XmlEvent::end_element())?; // node
                if sref.statement_type() == StatementType::Provable {
                    let mut i = 1;
                    loop {
                        let tk = sref.proof_slice_at(i);
                        i += 1;
                        if tk == b")" {
                            break;
                        }
                        writer.write(
                            XmlEvent::start_element("edge")
                                .attr("source", as_str(label))
                                .attr("target", as_str(tk)),
                        )?;
                        writer.write(XmlEvent::end_element())?;
                    }
                }
            }
            writer.write(XmlEvent::end_element())?; // graph
            writer.write(XmlEvent::end_element())?; // graphml
            Ok(())
        })
    }
}
