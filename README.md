# Metamath-knife - a Metamath database processing tool

## A what?

Metamath is a language for expressing formal proofs in mathematics. Metamath makes few assumptions on the underlying logic and is simple enough to support a wide variety of tools.
See http://us.metamath.org/#faq.

Metamath-knife can rapidly verify these proofs, providing much stronger confidence that the proof is correct. And we do mean *rapid*: over 28,000 proofs can be proved in less than a second.

Metamath-knife is a friendly fork of 
[smetamath-rs (aka SMM3) by Stephan O'Rear (sorear)](https://github.com/sorear/smetamath-rs). Here are some key differentiators:

* It supports *all* Metamath proof formats. In particular, Metamath-knife
  adds support for *all* Metamath proof formats
  (<a href="https://groups.google.com/g/metamath/c/xCUNA2ttHew/m/RXSNzdovBAAJ">uncompressed, compressed, package, or explicit</a>.
* We take extra steps to prevent errors, e.g., we have a CI pipeline
  (implemented using GitHub actions).
* We remove deprecated constructs, e.g., the deprecated try!(...)
  has been replaced with the easier-to-read "?" construct.
* We actively work to eliminate compiler warnings. This tends to
  counter errors, make the code more readable, and improve performance
  (e.g., by eliminating unnecessary clone() calls).

## Building

Install Rust, "Rust 2021" (version 1.56.0) or later, preferably using (rustup)[https://rustup.rs], then check out this repository and run:

    cargo build --release

Alternatively using `cargo install`:

    cargo install --git https://github.com/david-a-wheeler/metamath-knife
    # $HOME/.cargo/bin/metamath-knife has been installed, use it as the binary in the following instructions

## Running

    # The largest known Metamath database, and best test case
    git clone https://github.com/metamath/set.mm

    # One-shot verification using 4 threads
    target/release/metamath-knife --time --jobs 4 --split --verify set.mm/set.mm

    # Incremental verification
    (while sleep 5; do echo; done) | target/release/metamath-knife --time --jobs 4 --split --repeat --trace-recalc --verify set.mm/set.mm
    # then make small changes to the beginning, end, or middle of the DB and observe how behavior changes

Here is the command line help, which gives an idea of the options available:
```
A Metamath database verifier and processing tool

USAGE:
    metamath-knife [FLAGS] [OPTIONS] <DATABASE>

FLAGS:
        --debug                Activates debug logs, including for the grammar building and statement parsing
    -F, --dump-formula         Dumps the formulas of this database
    -G, --dump-grammar         Dumps the database's grammar
    -T, --dump-typesetting     Dumps typesetting information
        --free                 Explicitly deallocates working memory before exit
    -g, --grammar              Checks grammar
    -h, --help                 Prints help information
    -O, --outline              Shows database outline
    -p, --parse-stmt           Parses all statements according to the database's grammar
    -t, --parse-typesetting    Parses typesetting information
        --repeat               Demonstrates incremental verifier
        --split                Processes files > 1 MiB in multiple segments
        --time                 Prints milliseconds after each stage
        --trace-recalc         Prints segments as they are recalculated
    -V, --version              Prints version information
    -v, --verify               Checks proof validity
    -m, --verify-markup        Checks comment markup
        --verify-parse-stmt    Checks that printing parsed statements gives back the original formulas

OPTIONS:
        --text <NAME> <TEXT>    Provides raw database content on the command line
        --biblio <FILE>...      Supplies a bibliography file for verify-markup
                                Can be used one or two times; the second is for exthtml processing
    -D, --discouraged <FILE>    Regenerates `discouraged` file
    -e, --export <LABEL>...     Outputs a proof file
    -j, --jobs <jobs>           Number of threads to use for verification

ARGS:
    <DATABASE>    Database file to load
```

## License

This is licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

The SPDX license expression for its license is "(MIT OR Apache-2.0)".

Note that this is exactly the same license as smetamath-rs (SMM3),
That is intentional, because we want smetamath-rs (SMM3) to be able to
re-incorporate whatever we do if they like.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
