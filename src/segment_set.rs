use diag::Diagnostic;
use parser;
use parser::Comparer;
use parser::Segment;
use parser::SegmentId;
use parser::SegmentOrder;
use parser::SegmentRef;
use parser::Span;
use parser::StatementAddress;
use parser::StatementRef;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io;
use std::io::Read;
use std::fs::File;
use std::env;
use std::str;
use std::sync::Arc;
use std::path::PathBuf;

#[derive(Debug)]
pub struct SegmentSet {
    pub order: Arc<SegmentOrder>,
    pub segments: HashMap<SegmentId, Arc<Segment>>,
}

impl SegmentSet {
    pub fn new() -> Self {
        SegmentSet { order: Arc::new(SegmentOrder::new()), segments: HashMap::new() }
    }

    pub fn segments(&self) -> Vec<SegmentRef> {
        let mut out: Vec<SegmentRef> = self.segments.iter().map(|(&seg_id, seg)| SegmentRef { id: seg_id, segment: seg }).collect();
        out.sort_by(|x, y| self.order.cmp(&x.id, &y.id));
        out
    }

    pub fn segment(&self, seg_id: SegmentId) -> SegmentRef {
        SegmentRef { id: seg_id, segment: &self.segments[&seg_id] }
    }

    pub fn statement(&self, addr: StatementAddress) -> StatementRef {
        self.segment(addr.segment_id).statement(addr.index)
    }

    pub fn parse_diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sgref in self.segments() {
            for stref in sgref.statement_iter() {
                for &ref d in &stref.statement.diagnostics {
                    out.push((stref.address(), d.clone()));
                }
            }
        }
        out
    }

    pub fn read(&mut self, path: PathBuf, data: Vec<(PathBuf, Vec<u8>)>) {
        struct RecState {
            segments: Vec<Segment>,
            pre_included: HashSet<PathBuf>,
            included: HashSet<PathBuf>,
            preload: HashMap<PathBuf, Vec<u8>>,
            workdir: Option<PathBuf>,
        }

        fn canonicalize_and_read(state: &mut RecState, path: PathBuf) -> io::Result<Vec<Segment>> {
            let cpath = try!(path.canonicalize());
            if state.workdir.is_none() {
                state.workdir = Some(try!(try!(env::current_dir()).canonicalize()));
            }
            let relcpath = cpath.strip_prefix(&state.workdir.as_ref().unwrap()).unwrap_or(&cpath).to_owned();
            if !state.included.insert(relcpath.to_path_buf()) {
                return Ok(Vec::new());
            }
            let mut fh = try!(File::open(&relcpath));
            let mut buf = Vec::new();
            try!(fh.read_to_end(&mut buf));

            return Ok(parser::parse_segments(relcpath.to_string_lossy().into_owned(), &Arc::new(buf)));
        }

        fn read_and_parse(state: &mut RecState, path: PathBuf) -> Vec<Segment> {
            if !state.pre_included.insert(path.clone()) {
                return Vec::new();
            }
            let path_str = path.to_string_lossy().into_owned();
            match state.preload.get(&path).cloned() {
                None => {
                    // read from FS
                    match canonicalize_and_read(state, path) {
                        Err(cerr) => vec![parser::dummy_segment(path_str, Diagnostic::IoError(format!("{}", cerr)))],
                        Ok(segments) => segments,
                    }
                }
                Some(data) => {
                    parser::parse_segments(path_str, &Arc::new(data))
                }
            }
        }

        fn recurse(state: &mut RecState, path: PathBuf) {
            for seg in read_and_parse(state, path.clone()) {
                if seg.next_file != Span::null() {
                    let chain = str::from_utf8(seg.next_file.as_ref(&seg.buffer)).expect("parser verified ASCII").to_owned();
                    state.segments.push(seg);
                    recurse(state, path.parent().unwrap_or(&path).join(PathBuf::from(chain)));
                } else {
                    state.segments.push(seg);
                }
            }
        }

        let mut state = RecState {
            segments: Vec::new(), included: HashSet::new(), pre_included: HashSet::new(),
            preload: data.into_iter().collect(), workdir: None,
        };

        recurse(&mut state, path);

        let mut order = SegmentOrder::new();
        self.segments = HashMap::new();

        let start = order.start();
        for seg in state.segments {
            let id = order.new_before(start);
            self.segments.insert(id, Arc::new(seg));
        }
        self.order = Arc::new(order);
    }
}