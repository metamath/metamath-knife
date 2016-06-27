# SMM 3 - a Metamath database processor

## A what?

Metamath is a language for expressing formal proofs, which makes few assumptions on the underlying logic and is simple enough to support a wide variety of tools.
See http://us.metamath.org/#faq.

## Building

Install Rust ([rustup.sh]), version 1.9.0 or later, then check out this repository and run:

    cargo build --release

Alternatively using `cargo install`:

    cargo install --git https://github.com/sorear/smetamath-rs
    # $HOME/.cargo/bin/smetamath has been installed, use it as the binary in the following instructions

## Running

    # The largest known Metamath database, and best test case
    git clone https://github.com/metamath/set.mm

    # One-shot verification using 4 threads
    target/release/smetamath --timing --jobs 4 --split --verify set.mm/set.mm

    # Incremental verification
    (while sleep 5; do echo; done) | target/release/smetamath --timing --jobs 4 --split --repeat --trace-recalc --verify set.mm/set.mm
    # then make small changes to the beginning, end, or middle of the DB and observe how behavior changes

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.