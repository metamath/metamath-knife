# Metamath-rs - a library for processing Metamath databases

## A what?

Metamath is a language for expressing formal proofs in mathematics. Metamath makes few assumptions on the underlying logic and is simple enough to support a wide variety of tools.
See http://us.metamath.org/#faq.

Metamath-rs can rapidly verify these proofs, providing much stronger confidence that the proof is correct. And we do mean *rapid*: over 28,000 proofs can be proved in less than a second.

Metamath-rs is the library component of the [metamath-knife](https://github.com/metamath/metamath-knife) project, which also contains a standalone command-line application.

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
