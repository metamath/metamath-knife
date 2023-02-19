//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

use annotate_snippets::display_list::DisplayList;
use clap::{clap_app, crate_version};
use metamath_knife::database::{Database, DbOptions};
use metamath_knife::diag::{BibError, DiagnosticClass};
use metamath_knife::statement::StatementAddress;
use metamath_knife::verify_markup::{Bibliography, Bibliography2};
use metamath_knife::SourceInfo;
use simple_logger::SimpleLogger;
use std::fs::File;
use std::io::{self, BufWriter};
use std::mem;
use std::str::FromStr;
use std::sync::Arc;

fn positive_integer(val: String) -> Result<(), String> {
    u32::from_str(&val).map(|_| ()).map_err(|e| format!("{e}"))
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
        (@arg verify_markup: -m --("verify-markup") "Check comment markup")
        (@arg discouraged: -D --discouraged [FILE] "Regenerate `discouraged` file")
        (@arg outline: -O --outline "Show database outline")
        (@arg print_typesetting: --("dump-typesetting") "Show typesetting information")
        (@arg parse_typesetting: -t --("parse-typesetting") "Parse typesetting information")
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
        (@arg biblio: --biblio [FILE] ... "Supply a bibliography file for verify-markup\n\
            Can be used one or two times; the second is for exthtml processing")
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

        let mut types = vec![DiagnosticClass::Parse];

        if !matches.is_present("discouraged") {
            types.push(DiagnosticClass::Scope);
        }

        if matches.is_present("verify") {
            types.push(DiagnosticClass::Verify);
        }

        if matches.is_present("grammar") {
            types.push(DiagnosticClass::Grammar);
        }

        if matches.is_present("parse_stmt") {
            types.push(DiagnosticClass::StmtParse);
        }

        if matches.is_present("parse_typesetting") {
            types.push(DiagnosticClass::Typesetting);
        }

        if matches.is_present("verify_parse_stmt") {
            db.stmt_parse_pass();
            db.verify_parse_stmt();
        }

        let mut diags = db.diag_notations(&types);

        if matches.is_present("discouraged") {
            File::create(matches.value_of("discouraged").unwrap())
                .and_then(|file| db.write_discouraged(&mut BufWriter::new(file)))
                .unwrap_or_else(|err| diags.push((StatementAddress::default(), err.into())));
        }

        let mut count = db
            .render_diags(diags, |snippet| {
                println!("{}", DisplayList::from(snippet));
            })
            .len();

        if matches.is_present("verify_markup") {
            db.scope_pass();
            db.typesetting_pass();

            let sources = matches.values_of("biblio").map_or_else(Vec::new, |vals| {
                assert!(vals.len() <= 2, "expected at most 2 bibliography files");
                vals.map(|val| {
                    let file = std::fs::read(val).unwrap();
                    SourceInfo::new(val.to_owned(), Arc::new(file))
                })
                .collect()
            });
            let mut bib_diags = vec![];
            let mut bibs = sources
                .iter()
                .map(|source| Bibliography::parse(source, &mut bib_diags));
            let bib = bibs.next().map(|base| Bibliography2 {
                base,
                ext: bibs.next(),
            });

            count += BibError::render_list(&bib_diags, |snippet| {
                println!("{}", DisplayList::from(snippet));
            })
            .len();

            let diags = db.verify_markup(bib.as_ref());
            count += db
                .render_diags(diags, |snippet| {
                    println!("{}", DisplayList::from(snippet));
                })
                .len();
        }

        println!("{count} diagnostics issued.");

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
            db.outline_pass();
            db.print_outline();
        }

        if matches.is_present("print_typesetting") {
            db.typesetting_pass();
            db.print_typesetting();
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
