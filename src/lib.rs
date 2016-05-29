// TODO these should not be `pub`
pub mod parser;
pub mod nameck;
pub mod scopeck;
pub mod segment_set;
pub mod diag;
mod util;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
