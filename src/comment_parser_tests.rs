use crate::{
    comment_parser::{
        CommentItem::{self, *},
        CommentParser,
    },
    Span,
};

#[track_caller]
fn check(buf: &[u8], expected: &[CommentItem]) {
    assert_eq!(
        CommentParser::new(buf, Span::new(0, buf.len())).collect::<Vec<_>>(),
        expected
    )
}

#[test]
fn test_basic() {
    check(b"Hello world", &[Text(Span::new(0, 11))]);
}

#[test]
fn test_subscript() {
    check(
        b"Hello_world test",
        &[
            Text(Span::new(0, 5)),
            StartSubscript(5),
            Text(Span::new(6, 11)),
            EndSubscript(11),
            Text(Span::new(11, 16)),
        ],
    );
}

/// Metamath does not support nested subscripts, because `_` counts as a closing delimiter.
/// This turns into `x₀_y`.
#[test]
fn test_two_subscript() {
    check(
        b"x_0_y",
        &[
            Text(Span::new(0, 1)),
            StartSubscript(1),
            Text(Span::new(2, 3)),
            EndSubscript(3),
            Text(Span::new(3, 5)),
        ],
    );
}

/// You can have two subscripts in one word: `x₀_y₁`
#[test]
fn test_three_subscript() {
    check(
        b"x_0_y_1",
        &[
            Text(Span::new(0, 1)),
            StartSubscript(1),
            Text(Span::new(2, 3)),
            EndSubscript(3),
            Text(Span::new(3, 5)),
            StartSubscript(5),
            Text(Span::new(6, 7)),
            EndSubscript(7),
        ],
    );
}

#[test]
fn test_italic() {
    check(
        b"a _b_ c",
        &[
            Text(Span::new(0, 2)),
            StartItalic(2),
            Text(Span::new(3, 4)),
            EndItalic(4),
            Text(Span::new(5, 7)),
        ],
    );

    check(
        b"a _b c_ d",
        &[
            Text(Span::new(0, 2)),
            StartItalic(2),
            Text(Span::new(3, 6)),
            EndItalic(6),
            Text(Span::new(7, 9)),
        ],
    );
}

#[test]
fn test_bib() {
    check(
        b"Hello [world] test",
        &[
            Text(Span::new(0, 6)),
            BibTag(Span::new(7, 12)),
            Text(Span::new(13, 18)),
        ],
    );
    check(
        b"_italic [bib] test_",
        &[
            StartItalic(0),
            Text(Span::new(1, 8)),
            BibTag(Span::new(9, 12)),
            Text(Span::new(13, 18)),
            EndItalic(18),
        ],
    );
    check(b"[failed bib] test", &[Text(Span::new(0, 17))]);
    check(b"[[escaped] bib", &[Text(Span::new(0, 14))]);
}

#[test]
fn test_math() {
    check(
        b"` [x] + y_1 ` z_1",
        &[
            StartMathMode(0),
            MathToken(Span::new(2, 5)),
            MathToken(Span::new(6, 7)),
            MathToken(Span::new(8, 11)),
            EndMathMode(12),
            Text(Span::new(13, 15)),
            StartSubscript(15),
            Text(Span::new(16, 17)),
            EndSubscript(17),
        ],
    );
    check(
        b"`no spaces`",
        &[
            StartMathMode(0),
            MathToken(Span::new(1, 3)),
            MathToken(Span::new(4, 10)),
            EndMathMode(10),
        ],
    );
}

#[test]
fn test_label() {
    check(
        b"See ~ my_thm",
        &[Text(Span::new(0, 4)), Label(4, Span::new(6, 12))],
    );
    check(
        b"Visit ~http://example.com",
        &[Text(Span::new(0, 6)), Url(6, Span::new(7, 25))],
    );
}

#[test]
fn test_html() {
    check(
        b"Inside <HTML> tags, ~ labels work but sub_scripts don't </HTML>.",
        &[
            Text(Span::new(0, 7)),
            StartHtml(7),
            Text(Span::new(13, 20)),
            Label(20, Span::new(22, 28)),
            Text(Span::new(28, 56)),
            EndHtml(56),
            Text(Span::new(63, 64)),
        ],
    );
    check(
        b"It is an error to not close <HTML> tags",
        &[
            Text(Span::new(0, 28)),
            StartHtml(28),
            Text(Span::new(34, 39)),
        ],
    );
}
#[test]
fn test_para() {
    check(
        b"Line 1\n\nLine 2\n\nLine 3",
        &[
            Text(Span::new(0, 7)),
            LineBreak(7),
            Text(Span::new(7, 15)),
            LineBreak(15),
            Text(Span::new(15, 22)),
        ],
    );
    check(
        b"Extra\n\n\nWide",
        &[
            Text(Span::new(0, 6)),
            LineBreak(6),
            Text(Span::new(6, 7)),
            LineBreak(7),
            Text(Span::new(7, 12)),
        ],
    );
}
