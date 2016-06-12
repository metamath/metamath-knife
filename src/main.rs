#[macro_use]
extern crate clap;
extern crate fnv;

mod bit_set;
mod database;
mod diag;
mod nameck;
mod parser;
mod scopeck;
mod segment_set;
mod util;
mod verify;

use clap::Arg;
use clap::App;
use database::DbOptions;
use database::Executor;
use diag::Notation;
use nameck::Nameset;
use segment_set::SegmentSet;
use std::mem;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::Arc;
use std::time::Instant;

fn positive_integer(val: String) -> Result<(), String> {
    u32::from_str(&val).map(|_| ()).map_err(|e| format!("{}", e))
}

fn time<R, F: FnOnce() -> R>(opts: &DbOptions, name: &str, f: F) -> R {
    let now = Instant::now();
    let ret = f();
    if opts.timing {
        println!("{} {}ms", name, (now.elapsed() * 1000).as_secs());
    }
    ret
}

fn main() {
    let matches = App::new("smetamath-rs")
        .version(crate_version!())
        .about("About text")
        .arg(Arg::with_name("DATABASE").help("Database file to load").required_unless("TEXT"))
        .arg(Arg::with_name("split")
            .help("Process files > 1 MiB in multiple segments")
            .long("split"))
        .arg(Arg::with_name("timing").help("Print milliseconds after each stage").long("timing"))
        .arg(Arg::with_name("verify").help("Check proof validity").long("verify").short("v"))
        .arg(Arg::with_name("jobs")
            .help("Number of threads to use for verification")
            .long("jobs")
            .short("j")
            .takes_value(true)
            .validator(positive_integer))
        .arg(Arg::with_name("TEXT")
            .long("text")
            .help("Provide raw database content on the command line")
            .value_names(&["NAME", "TEXT"])
            .multiple(true))
        .get_matches();

    let mut options = DbOptions::default();
    options.autosplit = matches.is_present("split");
    options.timing = matches.is_present("timing");
    options.verify = matches.is_present("verify");
    options.jobs = usize::from_str(matches.value_of("jobs").unwrap_or("1"))
        .expect("validator should check this");

    let exec = Executor::new(options.jobs);

    let set = time(&options, "parse", || {
        let mut set = SegmentSet::new(&exec);
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
        Arc::new(set)
    });

    let ns = time(&options, "nameck", || {
        let mut ns = Nameset::new();
        ns.update(&set);
        Arc::new(ns)
    });

    let sr = time(&options,
                  "scopeck",
                  || Arc::new(scopeck::scope_check(&set, &ns)));
    let vr = time(&options, "verify", || verify::verify(&set, &ns, &sr));

    time(&options, "diag", || {
        let mut diags = Vec::new();
        diags.extend(set.parse_diagnostics());
        diags.extend(sr.diagnostics());
        diags.extend(vr.diagnostics());

        for notation in diag::to_annotations(&set, diags) {
            print_annotation(notation);
        }
    });

    time(&options, "free", move || {
        mem::drop(vr);
        mem::drop(sr);
        mem::drop(ns);
        mem::drop(set);
    });
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
