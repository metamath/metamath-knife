//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

use annotate_snippets::display_list::DisplayList;
use clap::{clap_app, crate_version};
use metamath_knife::database::{Database, DbOptions};
use metamath_knife::diag::BibError;
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
            "Provides raw database content on the command line")
        (@arg split: --split "Processes files > 1 MiB in multiple segments")
        (@arg timing: --time "Prints milliseconds after each stage")
        (@arg verify: -v --verify "Checks proof validity")
        (@arg verify_markup: -m --("verify-markup") "Checks comment markup")
        (@arg discouraged: -D --discouraged [FILE] "Regenerates `discouraged` file")
        (@arg axiom_use: -X --("axiom-use") [FILE] "Generate `axiom-use` file")
        (@arg verify_usage: -u --("verify-usage") "Checks axiom usage")
        (@arg outline: -O --outline "Shows database outline")
        (@arg dump_typesetting: -T --("dump-typesetting") "Dumps typesetting information")
        (@arg parse_typesetting: -t --("parse-typesetting") "Parses typesetting information")
        (@arg grammar: -g --grammar "Checks grammar")
        (@arg parse_stmt: -p --("parse-stmt")
            "Parses all statements according to the database's grammar")
        (@arg verify_parse_stmt: --("verify-parse-stmt")
            "Checks that printing parsed statements gives back the original formulas")
        (@arg dump_grammar: -G --("dump-grammar") "Dumps the database's grammar")
        (@arg dump_formula: -F --("dump-formula") "Dumps the formulas of this database")
        (@arg debug: --debug
            "Activates debug logs, including for the grammar building and statement parsing")
        (@arg trace_recalc: --("trace-recalc") "Prints segments as they are recalculated")
        (@arg free: --free "Explicitly deallocates working memory before exit")
        (@arg repeat: --repeat "Demonstrates incremental verifier")
        (@arg jobs: -j --jobs +takes_value validator(positive_integer)
            "Number of threads to use for verification")
        (@arg export: -e --export [LABEL] ... "Outputs a proof file")
        (@arg biblio: --biblio [FILE] ... "Supplies a bibliography file for verify-markup\n\
            Can be used one or two times; the second is for exthtml processing")
    );

    #[cfg(feature = "dot")]
    let app = clap_app!(@app (app)
        (@arg export_grammar_dot: -E --("export-grammar-dot")
            "Export the database's grammar in Graphviz DOT format for visualization")
    );

    #[cfg(feature = "xml")]
    let app = clap_app!(@app (app)
        (@arg export_graphml_deps: --("export-graphml-deps") [FILE]
        "Exports all theorem dependencies in the GraphML file format")
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
            || matches.is_present("dump_grammar")
            || matches.is_present("dump_formula"),
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

        if matches.is_present("verify") {
            db.verify_pass();
        }

        if matches.is_present("grammar") {
            db.grammar_pass();
        }

        if matches.is_present("parse_stmt") {
            db.stmt_parse_pass();
        }

        if matches.is_present("parse_typesetting") {
            db.typesetting_pass();
        }

        if matches.is_present("verify_parse_stmt") {
            db.stmt_parse_pass();
            db.verify_parse_stmt();
        }

        if matches.is_present("verify_usage") {
            db.verify_usage_pass();
        }

        let mut diags = db.diag_notations();

        if matches.is_present("discouraged") {
            File::create(matches.value_of("discouraged").unwrap())
                .and_then(|file| db.write_discouraged(&mut BufWriter::new(file)))
                .unwrap_or_else(|err| diags.push((StatementAddress::default(), err.into())));
        }

        #[cfg(feature = "xml")]
        if matches.is_present("export_graphml_deps") {
            File::create(matches.value_of("export_graphml_deps").unwrap())
                .map_err(|err| err.into())
                .and_then(|file| db.export_graphml_deps(&mut BufWriter::new(file)))
                .unwrap_or_else(|diag| diags.push((StatementAddress::default(), diag)));
        }

        if matches.is_present("axiom_use") {
            File::create(matches.value_of("axiom_use").unwrap())
                .and_then(|file| db.write_axiom_use(&mut BufWriter::new(file)))
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

        if matches.is_present("dump_grammar") {
            db.grammar_pass();
            db.dump_grammar();
        }

        #[cfg(feature = "dot")]
        if matches.is_present("export_grammar_dot") {
            db.export_grammar_dot();
        }

        if matches.is_present("dump_formula") {
            db.stmt_parse_pass();
            db.dump_formula();
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
            db.scope_pass();
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
