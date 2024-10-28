//! A library for manipulating [Metamath](http://us.metamath.org/#faq)
//! databases.  The entry point for all API operations is in the `database`
//! module, as is a discussion of the data representation.

mod list_stmt;

use annotate_snippets::Renderer;
use clap::error::ErrorKind;
use clap::{CommandFactory, Parser};
use list_stmt::list_statements;
use metamath_rs::database::{Database, DbOptions};
use metamath_rs::parser::is_valid_label;
use metamath_rs::statement::StatementAddress;
use simple_logger::SimpleLogger;
use std::fs::File;
use std::io::{self, stdout, BufWriter};
use std::mem;

/// A Metamath database verifier and processing tool
#[derive(Debug, clap::Parser)]
#[command(version, about, verbatim_doc_comment)]
struct Cli {
    /// Database file to load
    #[arg(id("DATABASE"), required_unless_present("text"))]
    db: Option<String>,
    /// Provides raw database content on the command line
    #[arg(long, value_names(&["NAME", "TEXT"]))]
    text: Vec<String>,
    /// Processes files > 1 MiB in multiple segments
    #[arg(long)]
    split: bool,
    /// Prints milliseconds after each stage
    #[arg(long = "time")]
    timing: bool,
    /// Checks proof validity
    #[arg(short, long)]
    verify: bool,
    /// Regenerates `discouraged` file
    #[arg(short = 'D', long, value_name("FILE"))]
    discouraged: Option<String>,
    /// Generate `axiom-use` file
    #[arg(short = 'X', long, value_name("FILE"))]
    axiom_use: Option<String>,
    /// Outputs statements directly or indirectly using the given list of statements
    #[arg(long, value_names(&["FILE", "LABELS"]))]
    stmt_use: Vec<String>,
    /// Checks axiom usage
    #[arg(short = 'u', long)]
    verify_usage: bool,
    /// Shows database outline
    #[arg(short = 'O', long)]
    outline: bool,
    /// Dumps typesetting information
    #[arg(short = 'T', long)]
    dump_typesetting: bool,
    /// Parses typesetting information
    #[arg(short = 't', long)]
    parse_typesetting: bool,
    /// Checks grammar
    #[arg(short, long)]
    grammar: bool,
    /// Parses all statements according to the database's grammar
    #[arg(short, long)]
    parse_stmt: bool,
    /// Checks that printing parsed statements gives back the original formulas
    #[arg(long)]
    verify_parse_stmt: bool,
    /// Dumps the database's grammar
    #[arg(short = 'G', long)]
    dump_grammar: bool,
    /// Dumps the formulas of this database
    #[arg(short = 'F', long)]
    dump_formula: bool,
    /// List all statements of this database
    #[arg(short = 'S', long)]
    list_statements: bool,
    /// Activates debug logs, including for the grammar building and statement parsing
    #[arg(long)]
    debug: bool,
    /// Prints segments as they are recalculated
    #[arg(long)]
    trace_recalc: bool,
    /// Explicitly deallocates working memory before exit
    #[arg(long)]
    free: bool,
    /// Demonstrates incremental verifier
    #[arg(long)]
    repeat: bool,
    /// Number of threads to use for verification
    #[arg(short, long, value_parser = clap::value_parser!(u32).range(1..))]
    jobs: Option<u32>,
    /// Outputs a proof file
    #[arg(short, long, value_name("LABEL"))]
    export: Vec<String>,
    /// Supplies a bibliography file for verify-markup
    /// Can be used one or two times; the second is for exthtml processing
    #[arg(long, value_name("FILE"))]
    biblio: Vec<String>,
    #[cfg(feature = "dot")]
    /// Export the database's grammar in Graphviz DOT format for visualization
    #[arg(short = 'E', long)]
    export_grammar_dot: bool,
    #[cfg(feature = "xml")]
    /// Exports all theorem dependencies in the GraphML file format
    #[arg(long, value_name("FILE"))]
    export_graphml_deps: Option<String>,
    #[cfg(feature = "verify_markup")]
    /// Checks comment markup and parses typesetting information
    #[arg(short = 'm', long)]
    verify_markup: bool,
}

fn main() {
    let cli = Cli::parse();
    let mut cmd = Cli::command();

    let incremental = cli.repeat
        || cli.grammar
        || cli.parse_stmt
        || cli.verify_parse_stmt
        || cli.dump_grammar
        || cli.dump_formula;
    #[cfg(feature = "dot")]
    let incremental = incremental || cli.export_grammar_dot;
    let options = DbOptions {
        autosplit: cli.split,
        timing: cli.timing,
        trace_recalc: cli.trace_recalc,
        incremental,
        jobs: cli.jobs.unwrap_or(1) as usize,
    };

    if cli.debug {
        SimpleLogger::new().init().unwrap();
    }

    let mut db = Database::new(options);

    let mut data = Vec::new();
    for kv in cli.text.chunks(2) {
        data.push((kv[0].clone(), kv[1].clone().into_bytes()));
    }
    let start = cli.db.unwrap_or_else(|| data[0].0.clone());

    loop {
        db.parse(start.clone(), data.clone());

        if cli.verify {
            db.verify_pass();
        }

        if cli.grammar {
            db.grammar_pass();
        }

        if cli.parse_stmt {
            db.stmt_parse_pass();
        }

        if cli.parse_typesetting {
            db.typesetting_pass();
        }

        if cli.verify_usage {
            db.verify_usage_pass();
        }

        let mut diags = db.diag_notations();

        if let Some(discouraged) = &cli.discouraged {
            File::create(discouraged)
                .and_then(|file| db.write_discouraged(&mut BufWriter::new(file)))
                .unwrap_or_else(|err| diags.push((StatementAddress::default(), err.into())));
        }

        #[cfg(feature = "xml")]
        if let Some(file) = &cli.export_graphml_deps {
            File::create(file)
                .map_err(|err| err.into())
                .and_then(|file| db.export_graphml_deps(&mut BufWriter::new(file)))
                .unwrap_or_else(|diag| diags.push((StatementAddress::default(), diag)));
        }

        if let Some(file) = &cli.axiom_use {
            File::create(file)
                .and_then(|file| {
                    db.write_stmt_use(|label| label.starts_with(b"ax-"), &mut BufWriter::new(file))
                })
                .unwrap_or_else(|err| diags.push((StatementAddress::default(), err.into())));
        }

        if !cli.stmt_use.is_empty() {
            let output_file_path = &cli.stmt_use[0];
            let stmt_list: Vec<_> = cli.stmt_use[1].split(',').map(str::as_bytes).collect();
            if !stmt_list.iter().copied().all(is_valid_label) {
                cmd.error(
                    ErrorKind::InvalidValue,
                    "Expected list of labels as second argument to --stmt-use",
                )
                .exit();
            }
            File::create(output_file_path)
                .and_then(|file| {
                    db.write_stmt_use(
                        |label| stmt_list.contains(&label),
                        &mut BufWriter::new(file),
                    )
                })
                .unwrap_or_else(|err| diags.push((StatementAddress::default(), err.into())));
        }

        if cli.list_statements {
            db.scope_pass();
            _ = list_statements(&db, |_label| true, &mut stdout());
        }

        let r = Renderer::styled();
        #[allow(unused_mut)]
        let mut count = db
            .render_diags(diags, |msg| println!("{}", r.render(msg)))
            .len();

        if cli.verify_parse_stmt {
            db.stmt_parse_pass();
            let diags = db.verify_parse_stmt();
            count += db
                .render_diags(diags, |msg| println!("{}", r.render(msg)))
                .len();
        }

        #[cfg(feature = "verify_markup")]
        if cli.verify_markup {
            use metamath_rs::diag::BibError;
            use metamath_rs::verify_markup::{Bibliography, Bibliography2};

            db.scope_pass();
            db.typesetting_pass();

            if cli.biblio.len() > 2 {
                cmd.error(
                    ErrorKind::TooManyValues,
                    "expected at most 2 bibliography files",
                )
                .exit()
            }
            let sources: Vec<_> = cli
                .biblio
                .iter()
                .map(|val| {
                    let file = std::fs::read(val).unwrap();
                    metamath_rs::SourceInfo::new(val.to_owned(), std::sync::Arc::new(file))
                })
                .collect();
            let mut bib_diags = vec![];
            let mut bibs = sources
                .iter()
                .map(|source| Bibliography::parse(source, &mut bib_diags));
            let bib = bibs.next().map(|base| Bibliography2 {
                base,
                ext: bibs.next(),
            });

            count += BibError::render_list(&bib_diags, |msg| println!("{}", r.render(msg))).len();

            let diags = db.verify_markup(bib.as_ref());
            count += db
                .render_diags(diags, |msg| println!("{}", r.render(msg)))
                .len();
        }

        println!("{count} diagnostics issued.");

        if cli.dump_grammar {
            db.grammar_pass();
            db.dump_grammar();
        }

        #[cfg(feature = "dot")]
        if cli.export_grammar_dot {
            db.grammar_pass();
            db.export_grammar_dot();
        }

        if cli.dump_formula {
            db.stmt_parse_pass();
            db.dump_formula();
        }

        if cli.outline {
            db.outline_pass();
            db.print_outline();
        }

        if cli.dump_typesetting {
            db.typesetting_pass();
            db.print_typesetting();
        }

        if !cli.export.is_empty() {
            db.scope_pass();
            for file in &cli.export {
                db.export(file);
            }
        }

        if cli.repeat {
            let mut input = String::new();
            if io::stdin().read_line(&mut input).unwrap() == 0 {
                break;
            }
        } else {
            if !cli.free {
                mem::forget(db);
            }

            // Exit with code 1 if any warning or error were encountered
            let code = if count > 0 { 1 } else { 0 };
            std::process::exit(code);
        }
    }
}
