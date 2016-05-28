extern crate smetamath;
use smetamath::parser;
use std::env;
use std::sync::Arc;

fn main() {
    let y = parser::parse_segments(&Arc::new(env::args().nth(1).unwrap().into_bytes()));
    println!("Hello world {:#?}", y);
}