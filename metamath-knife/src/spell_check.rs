//! Spell checking in theorem comments and section headers.
//!
//! This goes through each statement and parses the comments, ignoring HTML and italics, and stopping at the parentheticals.
//! The `zspell` rust library is used for spellchecking.
//! The `add_word` `$j` command allows to append custom words to the dictionary.
//! The dictionary included has been taken from https://github.com/wooorm/dictionaries/tree/main/dictionaries/en.
use metamath_rs::{
    as_str,
    comment_parser::CommentItem::EndItalic,
    comment_parser::CommentItem::StartItalic,
    comment_parser::CommentItem::Text,
    diag::Diagnostic,
    statement::{CommandToken::Keyword, FilePos, StatementAddress},
    Database, Span, StatementRef, StatementType,
};
use regex::Regex;
use std::sync::OnceLock;
use zspell::Dictionary;

fn ignore_words() -> &'static Regex {
    static IGNORE_WORDS: OnceLock<Regex> = OnceLock::new();
    IGNORE_WORDS.get_or_init(|| Regex::new(r"^(\d+|[A-Z]\w+|-)$").unwrap())
}

pub fn spell_check(db: &Database) -> Vec<(StatementAddress, Diagnostic)> {
    let aff_content = include_str!("dictionary/index.aff");
    let dic_content = include_str!("dictionary/index.dic");
    let dic = dic_content.to_string() + &personal_dict(db);

    let dict: Dictionary = zspell::builder()
        .config_str(aff_content)
        .dict_str(&dic)
        .build()
        .expect("failed to build spell check dictionary!");

    let mut diags = vec![];
    for stmt in db.statements() {
        if let StatementType::HeadingComment(_) = stmt.statement_type() {
            check_statement(&stmt, None, &dict, &mut diags);
        } else if stmt.is_assertion() {
            if let Some(comment) = stmt.associated_comment() {
                let parentheticals_start = comment.parentheticals().full_span().map(|s| s.start);
                check_statement(&comment, parentheticals_start, &dict, &mut diags);
            }
        }
    }
    diags
}

fn personal_dict(db: &Database) -> String {
    db.process_j_commands(|command: &Vec<metamath_rs::statement::CommandToken>, buf| {
        if let [Keyword(cmd), words @ ..] = &**command {
            if cmd.as_ref(buf) == b"add_word" {
                Some(
                    words
                        .iter()
                        .map(|word| as_str(&word.value(buf)).to_string())
                        .collect::<Vec<_>>()
                        .join("\n"),
                )
            } else {
                None
            }
        } else {
            None
        }
    })
    .join("\n")
}

fn check_statement(
    stmt: &StatementRef,
    stop_at: Option<FilePos>,
    dict: &Dictionary,
    diags: &mut Vec<(StatementAddress, Diagnostic)>,
) {
    let stop_at = stop_at.unwrap_or(stmt.span_full().end);
    let mut italics = false;
    for item in stmt.comment_parser() {
        match item {
            Text(span) => {
                if span.end > stop_at {
                    break;
                }
                if italics {
                    continue;
                }
                let text = as_str(stmt.span_text(&span));
                for (pos, word) in dict.check_indices(text) {
                    if ignore_words().is_match(word) {
                        continue;
                    }
                    let start = span.start + pos as FilePos;
                    let end = start + word.len() as FilePos;
                    diags.push((
                        stmt.address(),
                        Diagnostic::SpellingMistake(Span::new2(start, end)),
                    ))
                }
            }
            StartItalic(_) => {
                italics = true;
            }
            EndItalic(_) => {
                italics = false;
            }
            _ => {}
        }
    }
}
