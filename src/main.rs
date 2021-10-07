//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

use clap::{clap_app, crate_version};
use metamath_knife::database::{Database, DbOptions};
use metamath_knife::diag::{DiagnosticClass, Notation};
use metamath_knife::line_cache::LineCache;
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
    let app = clap_app!(("smetamath-knife") =>
        (version: crate_version!())
        (about: "A Metamath database verifier and processing tool")
        (@arg DATABASE: required_unless("TEXT") "Database file to load")
        (@arg TEXT: --text value_names(&["NAME", "TEXT"]) ...
            "Provide raw database content on the command line")
        (@arg split: --split "Process files > 1 MiB in multiple segments")
        (@arg timing: --timing "Print milliseconds after each stage")
        (@arg verify: -v --verify "Check proof validity")
        (@arg outline: -O --outline "Show database outline")
        (@arg grammar: -g --grammar "Check grammar")
        (@arg parse_stmt: -p --("parse-stmt")
            "Parse all statements according to the database's grammar")
        (@arg verify_parse_stmt: --("verify-parse-stmt")
            "Check that printing parsed statements gives back the original formulas")
        (@arg print_grammar: -G --("print-grammar") "Print the database's grammar")
        (@arg print_formula: -F --("print-formula") "Dump the formulas of this database")
        (@arg debug: --debug
            "Activate debug logs, including for the grammar building and statement parsing")
        (@arg trace_recalc: --("trace-recalc") "Print segments as they are recalculated")
        (@arg free: --free "Explicitly deallocate working memory before exit")
        (@arg repeat: --repeat "Demonstrate incremental verifier")
        (@arg jobs: -j --jobs +takes_value validator(positive_integer)
            "Number of threads to use for verification")
        (@arg export: -e --export [LABEL] ... "Output a proof file")
    );

    #[cfg(feature = "dot")]
    let app = clap_app!(@app (app)
        (@arg export_grammar_dot: -E --("export-grammar-dot")
            "Export the database's grammar in Graphviz DOT format for visualization")
    );

    let matches = app.get_matches();

    let options = DbOptions {
        autosplit: matches.is_present("split"),
        timing: matches.is_present("timing"),
        trace_recalc: matches.is_present("trace_recalc"),
        incremental: matches.is_present("repeat")
            || matches.is_present("grammar")
            || matches.is_present("parse_stmt")
            || matches.is_present("verify_parse_stmt")
            || matches.is_present("export_grammar_dot")
            || matches.is_present("print_grammar")
            || matches.is_present("print_formula"),
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

        if matches.is_present("parse_stmt") {
            types.push(DiagnosticClass::StmtParse);
        }

        if matches.is_present("verify_parse_stmt") {
            db.verify_parse_stmt();
        }

        let mut lc = LineCache::default();
        let mut count = 0;
        for notation in db.diag_notations(types) {
            print_annotation(&mut lc, notation);
            count += 1;
        }
        println!("{} diagnostics issued.", count);

        if matches.is_present("print_grammar") {
            db.print_grammar();
        }

        #[cfg(feature = "dot")]
        if matches.is_present("export_grammar_dot") {
            db.export_grammar_dot();
        }

        if matches.is_present("print_formula") {
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
