extern crate fnv;

mod diag;
mod nameck;
mod parser;
mod scopeck;
mod segment_set;
mod util;
mod verify;

use diag::Notation;
use nameck::Nameset;
use segment_set::SegmentSet;
use std::env;
use std::mem;
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut set = SegmentSet::new();
    let now = Instant::now();
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

    println!("parse {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let mut ns = Nameset::new();
    ns.update(&set);

    println!("nameck {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let sr = scopeck::scope_check(&set, &ns);

    println!("scopeck {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let vr = verify::verify(&set, &sr);

    println!("verify {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let mut diags = Vec::new();
    diags.extend(set.parse_diagnostics());
    diags.extend(sr.diagnostics());
    diags.extend(vr.diagnostics());

    for notation in diag::to_annotations(&set, diags) {
        print_annotation(notation);
    }
    // println!("{:#?}", set);

    println!("diag {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    mem::drop(vr);
    mem::drop(sr);
    mem::drop(ns);
    mem::drop(set);

    println!("free {}ms", (now.elapsed() * 1000).as_secs());
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
