#[macro_use]
extern crate clap;
extern crate fnv;

mod bit_set;
mod diag;
mod nameck;
mod parser;
mod scopeck;
mod segment_set;
mod util;
mod verify;

use clap::Arg;
use clap::App;
use diag::Notation;
use nameck::Nameset;
use segment_set::SegmentSet;
use std::mem;
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let matches = App::new("smetamath-rs")
        .version(crate_version!())
        .about("About text")
        .arg(Arg::with_name("DATABASE").help("Database file to load").required_unless("TEXT"))
        .arg(Arg::with_name("TEXT")
            .long("text")
            .help("Provide raw database content on the command line")
            .value_names(&["NAME", "TEXT"])
            .multiple(true))
        .get_matches();

    let mut set = SegmentSet::new();
    let now = Instant::now();
    let mut data = Vec::new();
    if let Some(tvals) = matches.values_of_lossy("TEXT") {
        for kv in tvals.chunks(2) {
            data.push((PathBuf::from(&kv[0]), kv[1].clone().into_bytes()));
        }
    }
    let start = matches.value_of("DATABASE")
        .map(|st| PathBuf::from(st))
        .unwrap_or_else(|| data[0].0.clone());
    set.read(start, data);

    println!("parse {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let mut ns = Nameset::new();
    ns.update(&set);

    println!("nameck {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let sr = scopeck::scope_check(&set, &ns);

    println!("scopeck {}ms", (now.elapsed() * 1000).as_secs());
    let now = Instant::now();

    let vr = verify::verify(&set, &ns, &sr);

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
