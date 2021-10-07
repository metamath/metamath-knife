//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.
#![warn(missing_docs)]
#[macro_use]
extern crate clap;
extern crate filetime;
extern crate fnv;
extern crate regex;

pub mod bit_set;
pub mod database;
pub mod diag;
pub mod export;
pub mod formula;
pub mod grammar;
pub mod line_cache;
pub mod nameck;
pub mod outline;
pub mod parser;
pub mod proof;
pub mod scopeck;
pub mod segment_set;
mod tree;
pub mod util;
pub mod verify;

#[cfg(test)]
mod formula_tests;
#[cfg(test)]
mod grammar_tests;
#[cfg(test)]
mod parser_tests;
#[cfg(test)]
mod util_tests;

use clap::App;
use clap::Arg;
use database::Database;
use database::DbOptions;
use diag::DiagnosticClass;
use diag::Notation;
use line_cache::LineCache;
use simple_logger::SimpleLogger;
use std::io;
use std::mem;
use std::str::FromStr;

fn positive_integer(val: String) -> Result<(), String> {
    u32::from_str(&val)
        .map(|_| ())
        .map_err(|e| format!("{}", e))
}

fn main() {
    let matches = App::new("smetamath-knife")
        .version(crate_version!())
        .about("A Metamath database verifier and processing tool")
        .arg(
            Arg::with_name("DATABASE")
                .help("Database file to load")
                .required_unless("TEXT"),
        )
        .arg(
            Arg::with_name("split")
                .help("Process files > 1 MiB in multiple segments")
                .long("split"),
        )
        .arg(
            Arg::with_name("timing")
                .help("Print milliseconds after each stage")
                .long("timing"),
        )
        .arg(
            Arg::with_name("verify")
                .help("Check proof validity")
                .long("verify")
                .short("v"),
        )
        .arg(
            Arg::with_name("outline")
                .help("Show database outline")
                .long("outline")
                .short("O"),
        )
        .arg(
            Arg::with_name("grammar")
                .help("Check grammar")
                .long("grammar")
                .short("g"),
        )
        .arg(
            Arg::with_name("parse-stmt")
                .help("Parse statements according to the databases grammar")
                .long("parse-stmt")
                .short("p"),
        )
        .arg(
            Arg::with_name("verify-parse-stmt")
                .help("Check that printing parsed statements gives back the original formulas")
                .long("verify-parse-stmt"),
        )
        .arg(
            Arg::with_name("print-grammar")
                .help("Print the database's grammar")
                .long("print-grammar")
                .short("G"),
        )
        .arg(
            Arg::with_name("print-formula")
                .help("Parse all statements according to the database's grammar")
                .long("print-formula")
                .short("F"),
        )
        .arg(
            Arg::with_name("export-grammar-dot")
                .help("Export the database's grammar in Graphviz DOT format for visualization")
                .long("export-grammar-dot")
                .short("E"),
        )
        .arg(
            Arg::with_name("debug")
                .help(
                    "Activate debug logs, including for the grammar building and statement parsing",
                )
                .long("debug"),
        )
        .arg(
            Arg::with_name("trace-recalc")
                .help("Print segments as they are recalculated")
                .long("trace-recalc"),
        )
        .arg(
            Arg::with_name("free")
                .help("Explicitly deallocate working memory before exit")
                .long("free"),
        )
        .arg(
            Arg::with_name("repeat")
                .help("Demonstrate incremental verifier")
                .long("repeat"),
        )
        .arg(
            Arg::with_name("jobs")
                .help("Number of threads to use for verification")
                .long("jobs")
                .short("j")
                .takes_value(true)
                .validator(positive_integer),
        )
        .arg(
            Arg::with_name("export")
                .help("Output a proof file")
                .long("export")
                .short("e")
                .multiple(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("TEXT")
                .long("text")
                .help("Provide raw database content on the command line")
                .value_names(&["NAME", "TEXT"])
                .multiple(true),
        )
        .get_matches();

    let options = DbOptions {
        autosplit: matches.is_present("split"),
        timing: matches.is_present("timing"),
        trace_recalc: matches.is_present("trace-recalc"),
        incremental: matches.is_present("repeat")
            || matches.is_present("grammar")
            || matches.is_present("parse-stmt")
            || matches.is_present("verify-parse-stmt")
            || matches.is_present("export-grammar-dot")
            || matches.is_present("print-grammar")
            || matches.is_present("print-formula"),
        jobs: usize::from_str(matches.value_of("jobs").unwrap_or("1"))
            .expect("validator should check this"),
    };

    if matches.is_present("debug") {
        SimpleLogger::new().init().unwrap();
    }

    let mut db = Database::new(options);

    let mut data = Vec::new();
    if let Some(tvals) = matches.values_of_lossy("TEXT") {
        for kv in tvals.chunks(2) {
            data.push((kv[0].clone(), kv[1].clone().into_bytes()));
        }
    }
    let start = matches
        .value_of("DATABASE")
        .map(|x| x.to_owned())
        .unwrap_or_else(|| data[0].0.clone());

    loop {
        db.parse(start.clone(), data.clone());

        let mut types = vec![DiagnosticClass::Parse, DiagnosticClass::Scope];

        if matches.is_present("verify") {
            types.push(DiagnosticClass::Verify);
        }

        if matches.is_present("grammar") {
            types.push(DiagnosticClass::Grammar);
        }

        if matches.is_present("parse-stmt") {
            types.push(DiagnosticClass::StmtParse);
        }

        if matches.is_present("verify-parse-stmt") {
            db.verify_parse_stmt();
        }

        let mut lc = LineCache::default();
        let mut count = 0;
        for notation in db.diag_notations(types) {
            print_annotation(&mut lc, notation);
            count += 1;
        }
        println!("{} diagnostics issued.", count);

        if matches.is_present("print-grammar") {
            db.print_grammar();
        }

        if matches.is_present("export-grammar-dot") {
            #[cfg(feature = "dot")]
            db.export_grammar_dot();

            #[cfg(not(feature = "dot"))]
            println!("The program was not compiled with the `dot` feature. This is required to export in the DOT format.");
        }

        if matches.is_present("print-formula") {
            db.print_formula();
        }

        if matches.is_present("outline") {
            db.print_outline();
        }

        if let Some(exps) = matches.values_of_lossy("export") {
            for file in exps {
                db.export(&file);
            }
        }

        if matches.is_present("repeat") {
            let mut input = String::new();
            if io::stdin().read_line(&mut input).unwrap() == 0 {
                break;
            }
        } else {
            if !matches.is_present("free") {
                mem::forget(db);
            }

            // Exit with code 1 if any warning or error were encountered
            let code = if count > 0 { 1 } else { 0 };
            std::process::exit(code);
        }
    }
}

fn print_annotation(lc: &mut LineCache, ann: Notation) {
    let mut args = String::new();
    for (id, val) in ann.args {
        args.push_str(&format!(" {}={}", id, val));
    }
    let offs = (ann.span.start + ann.source.span.start) as usize;
    let (row, col) = lc.from_offset(&ann.source.text, offs);
    println!(
        "{}:{}:{}:{:?}:{}{}",
        ann.source.name, row, col, ann.level, ann.message, args
    );

    let line_end = LineCache::line_end(&ann.source.text, offs);
    let eoffs = (ann.span.end + ann.source.span.start) as usize;
    let line_start = offs - (col - 1) as usize;
    if eoffs <= line_end {
        println!(
            "|{}»{}«{}",
            String::from_utf8_lossy(&ann.source.text[line_start..offs]),
            String::from_utf8_lossy(&ann.source.text[offs..eoffs]),
            String::from_utf8_lossy(&ann.source.text[eoffs..line_end])
        );
    } else {
        println!(
            "|{}»{}",
            String::from_utf8_lossy(&ann.source.text[line_start..offs]),
            String::from_utf8_lossy(&ann.source.text[offs..line_end])
        );
    }
}
