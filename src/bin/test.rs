extern crate smetamath;
use smetamath::segment_set::SegmentSet;
use smetamath::nameck::Nameset;
use smetamath::scopeck;
use smetamath::diag::{self, Notation};
use smetamath::verify;
use std::env;
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut set = SegmentSet::new();
    if args.len() > 2 {
        let mut data = Vec::new();
        let mut i = 1;
        while i + 1 < args.len() {
            data.push((PathBuf::from(&args[i]), args[i + 1].clone().into_bytes()));
            i += 2;
        }
        set.read(data[0].0.clone(), data);
    } else {
        set.read(PathBuf::from(&args[1]).to_path_buf(), Vec::new());
    }

    let mut ns = Nameset::new();
    ns.update(&set);
    let sr = scopeck::scope_check(&set, &ns);
    let vr = verify::verify(&set, &sr);

    let mut diags = Vec::new();
    diags.extend(set.parse_diagnostics());
    diags.extend(sr.diagnostics());
    diags.extend(vr.diagnostics());

    for notation in diag::to_annotations(&set, diags) {
        print_annotation(notation);
    }
    // println!("{:#?}", set);
}

fn print_annotation(ann: Notation) {
    let mut args = String::new();
    for (id, val) in ann.args {
        args.push_str(&format!(" {}={}", id, val));
    }
    println!("{}:{}-{}:{:?}:{}{}",
             ann.source.filepath,
             ann.span.start,
             ann.span.end,
             ann.level,
             ann.message,
             args);
}
