# SMM 3 - a Metamath database processor

## A what?

Metamath is a language for expressing formal proofs, which makes few assumptions on the underlying logic and is simple enough to support a wide variety of tools.
See http://us.metamath.org/#faq.

## Building

Install Rust ([rustup.sh]), then:

    cargo build --release

Rust 1.11.0 or newer is recommended as SMM3 benefits measurably from the "non-filling drop" change added to Rust on 2016-06-05.
At the time of writing, that requires a nightly build and the `-Z orbit` compiler flag, which is included in the `.cargo/config` file in this repository.
If you are trying to use an older or newer stable build and `-Z orbit` is giving an error, delete `.cargo/config` and try again.

## Running

    # The largest known Metamath database, and best test case
    git clone https://github.com/metamath/set.mm

    # One-shot verification using 4 threads
    target/release/smetamath --timing --jobs 4 --split --verify set.mm/set.mm

    # Incremental verification
    (while sleep 5; do echo; done) | target/release/smetamath --timing --jobs 4 --split --repeat --trace-recalc --verify set.mm/set.mm
    # then make small changes to the beginning, end, or middle of the DB and observe how behavior changes

# TODO

 * Biggest remaining oneshot optimization is to replace `HashMap<Token, ...>` with something more cache-friendly
 * For incremental verifiers, we can do finer-grained dependency tracking
 * There's no grammatical parser or outline inference just yet
 * Might want to get into some proof model stufff?