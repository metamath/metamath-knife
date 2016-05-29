extern crate smetamath;
use smetamath::segment_set::SegmentSet;
use smetamath::nameck::Nameset;
use std::env;
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut set = SegmentSet::new();
    if args.len() > 2 {
        let mut data = Vec::new();
        let mut i = 1;
        while i + 1 < args.len() {
            data.push((PathBuf::from(&args[i]), args[i + 1].clone().into_bytes()));
            i += 2;
        }
        set.read(data[0].0.clone(), data);
    } else {
        set.read(PathBuf::from(&args[1]).to_path_buf(), Vec::new());
    }

    let mut ns = Nameset::new();
    ns.update(&set);
    // println!("{:#?}", set);
}