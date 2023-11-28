//! The typesetting data.
//!
//! This is the result of parsing a `$t` metamath comment, which contains information
//! used by the metamath website generator. Although `metamath-rs` tries to be
//! generic and so it does not itself contain a website generator, this pass can be
//! used to collect information for generating HTML in the style of
//! [`metamath.exe`](https://github.com/metamath/metamath-exe).

use crate::{
    as_str,
    diag::Diagnostic,
    statement::{GlobalSpan, StatementAddress, Token, TokenPtr},
    util::HashMap,
    Span,
};

/// The parsed `$t` comment data.
#[derive(Debug, Default, Clone)]
pub struct TypesettingData {
    /// Any errors detected while parsing this segment.
    pub diagnostics: Vec<(StatementAddress, Diagnostic)>,

    /// LaTeX definitions are used to replace a token with a piece of latex syntax.
    /// Each entry has the form `(token, replacement)`.
    /// ```text
    /// latexdef "ph" as "\varphi";
    /// ```
    pub latex_defs: HashMap<Token, (Span, GlobalSpan, Token)>,

    /// HTML definitions are used to replace a token with a piece of HTML syntax.
    /// This version will generally be used for the GIF rendering version of the web pages.
    /// Each entry has the form `(token, replacement)`.
    /// ```text
    /// htmldef "ph" as "<IMG SRC='_varphi.gif' WIDTH=11 HEIGHT=19 ALT=' ph' TITLE='ph'>";
    /// ```
    pub html_defs: HashMap<Token, (Span, GlobalSpan, Token)>,

    /// HTML definitions are used to replace a token with a piece of HTML syntax.
    /// This version will generally be used for the unicode rendering version of the web pages.
    /// Each entry has the form `(token, replacement)`.
    /// ```text
    /// althtmldef "ph" as "<SPAN CLASS=wff STYLE='color:blue'>&#x1D711;</SPAN>";
    /// ```
    pub alt_html_defs: HashMap<Token, (Span, GlobalSpan, Token)>,

    /// A piece of HTML to give the variable color key. All `htmlvarcolor` directives are given
    /// separately here, but they are logically concatenated with spaces for rendering.
    /// ```text
    /// htmlvarcolor '<SPAN CLASS=wff STYLE="color:blue;font-style:normal">wff</SPAN> '
    ///   + '<SPAN CLASS=setvar STYLE="color:red;font-style:normal">setvar</SPAN> '
    ///   + '<SPAN CLASS=class STYLE="color:#C3C;font-style:normal">class</SPAN>';
    /// ```
    pub html_var_color: Vec<(GlobalSpan, Token)>,

    /// The title of the generated HTML page.
    /// ```text
    /// htmltitle "Metamath Proof Explorer";
    /// ```
    pub html_title: Option<(GlobalSpan, Token)>,

    /// The link to the home page in the generated HTML page.
    /// ```text
    /// htmlhome '<A HREF="mmset.html"><FONT SIZE=-2 FACE=sans-serif>' +
    ///     '<IMG SRC="mm.gif" BORDER=0 ALT='  +
    ///     '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    ///     'Home</FONT></A>';
    /// ```
    pub html_home: Option<(GlobalSpan, Token)>,

    /// The relative path from the unicode version to the GIF version. Used for cross references.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// htmldir "../mpegif/";
    /// ```
    pub html_dir: Option<(GlobalSpan, Token)>,

    /// The relative path from the GIF version to the unicode version. Used for cross references.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// althtmldir "../mpeuni/";
    /// ```
    pub alt_html_dir: Option<(GlobalSpan, Token)>,

    /// Optional file where bibliographic references are kept.
    /// ```text
    /// htmlbibliography "mmset.html";
    /// ```
    pub html_bibliography: Option<(GlobalSpan, Token)>,

    /// Custom CSS to be placed in the header of generated files.
    /// Note that any `\n` escapes are not yet replaced by newlines in this `html_css` variable;
    /// library consumers are responsible for performing this replacement.
    /// ```text
    /// htmlcss '<STYLE TYPE="text/css">\n' +
    ///   '</STYLE>\n' +
    ///   '<LINK href="mmset.css" title="mmset"\n' +
    ///   '    rel="stylesheet" type="text/css">\n';
    /// ```
    pub html_css: Option<(GlobalSpan, Token)>,

    /// Tag(s) for the main SPAN surrounding all Unicode math.
    /// ```text
    /// htmlfont 'CLASS=math';
    /// ```
    pub html_font: Option<(GlobalSpan, Token)>,

    /// A label, such that everything after this label uses the `ext_*` variables instead of the
    /// regular ones.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// exthtmllabel "chil";
    /// ```
    pub ext_html_label: Option<(GlobalSpan, Token)>,

    /// The title of the generated HTML page, for the Hilbert Space extension.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// exthtmltitle "Hilbert Space Explorer";
    /// ```
    pub ext_html_title: Option<(GlobalSpan, Token)>,

    /// The link to the home page in the generated HTML page, for the Hilbert Space extension.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// exthtmlhome '<A HREF="mmhil.html"><FONT SIZE=-2 FACE=sans-serif>' +
    ///    '<IMG SRC="atomic.gif" BORDER=0 ALT='  +
    ///    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE STYLE="margin-bottom:0px">' +
    ///    'Home</FONT></A>';
    /// ```
    pub ext_html_home: Option<(GlobalSpan, Token)>,

    /// Optional file where bibliographic references are kept, for the Hilbert Space extension.
    /// (This is a set.mm specific hack.)
    /// ```text
    /// exthtmlbibliography "mmhil.html";
    /// ```
    pub ext_html_bibliography: Option<(GlobalSpan, Token)>,

    /// Optional link(s) to other versions of the theorem page.  A "*" is replaced
    /// with the label of the current theorem.  If you need a literal "*" as part
    /// of the URL, use the alternate URL encoding "%2A". (Note that `*` characters are not
    /// interpreted in this string; library consumers are responsible for implementing this spec.)
    /// ```text
    /// htmlexturl '<A HREF="http://metamath.tirix.org/*.html">'
    ///     + 'Structured version</A>&nbsp;&nbsp; '
    ///     + '<A HREF="https://expln.github.io/metamath/asrt/*.html">'
    ///     + 'Visualization version</A>&nbsp;&nbsp; ';
    /// ```
    pub html_ext_url: Option<(GlobalSpan, Token)>,
}

impl TypesettingData {
    /// Get the unicode rendering for a given symbol
    #[must_use]
    pub fn get_alt_html_def(&self, symbol: TokenPtr<'_>) -> Option<&Token> {
        self.alt_html_defs.get(symbol).map(|(_, _, tk)| tk)
    }

    /// Dump the content of this outline to the standard output
    pub(crate) fn dump(&self) {
        for (_, v) in &self.html_var_color {
            println!("html_var_color += {:?};", as_str(v));
        }
        println!(
            "html_title = {:?};",
            self.html_title.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_home = {:?};",
            self.html_home.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_dir = {:?};",
            self.html_dir.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "alt_html_dir = {:?};",
            self.alt_html_dir.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_bibliography = {:?};",
            self.html_bibliography.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_css = {:?};",
            self.html_css.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_font = {:?};",
            self.html_font.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "ext_html_label = {:?};",
            self.ext_html_label.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "ext_html_title = {:?};",
            self.ext_html_title.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "ext_html_home = {:?};",
            self.ext_html_home.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "ext_html_bibliography = {:?};",
            self.ext_html_bibliography.as_ref().map(|tk| as_str(&tk.1))
        );
        println!(
            "html_ext_url = {:?};",
            self.html_ext_url.as_ref().map(|tk| as_str(&tk.1))
        );
        for (tk, (_, _, v)) in &self.latex_defs {
            println!("latex_defs[{:?}] = {:?};", as_str(tk), as_str(v));
        }
        for (tk, (_, _, v)) in &self.html_defs {
            println!("html_defs[{:?}] = {:?};", as_str(tk), as_str(v));
        }
        for (tk, (_, _, v)) in &self.alt_html_defs {
            println!("alt_html_defs[{:?}] = {:?};", as_str(tk), as_str(v));
        }
    }
}
