use database::DbOptions;
use database::Executor;
use database::Promise;
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
use std::collections::VecDeque;
use std::io;
use std::io::Read;
use std::fs::File;
use std::env;
use std::str;
use std::sync::Arc;
use std::path::PathBuf;
use util::find_chapter_header;
use util::HashMap;
use util::HashSet;
use util::new_map;
use util::new_set;

#[derive(Debug,Clone)]
pub struct SegmentSet {
    pub options: Arc<DbOptions>,
    pub exec: Executor,
    pub order: Arc<SegmentOrder>,
    pub segments: HashMap<SegmentId, Arc<Segment>>,
}

impl SegmentSet {
    pub fn new(opts: Arc<DbOptions>, exec: &Executor) -> Self {
        SegmentSet {
            options: opts,
            exec: exec.clone(),
            order: Arc::new(SegmentOrder::new()),
            segments: new_map(),
        }
    }

    pub fn segments(&self) -> Vec<SegmentRef> {
        let mut out: Vec<SegmentRef> = self.segments
            .iter()
            .map(|(&seg_id, seg)| {
                SegmentRef {
                    id: seg_id,
                    segment: seg,
                }
            })
            .collect();
        out.sort_by(|x, y| self.order.cmp(&x.id, &y.id));
        out
    }

    pub fn segment(&self, seg_id: SegmentId) -> SegmentRef {
        SegmentRef {
            id: seg_id,
            segment: &self.segments[&seg_id],
        }
    }

    pub fn statement(&self, addr: StatementAddress) -> StatementRef {
        self.segment(addr.segment_id).statement(addr.index)
    }

    pub fn parse_diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sgref in self.segments() {
            for &(ix, ref d) in &sgref.segment.diagnostics {
                out.push((StatementAddress::new(sgref.id, ix), d.clone()));
            }
        }
        out
    }

    pub fn read(&mut self, path: PathBuf, data: Vec<(PathBuf, Vec<u8>)>) {
        struct RecState {
            options: Arc<DbOptions>,
            segments: Vec<Segment>,
            pre_included: HashSet<PathBuf>,
            included: HashSet<PathBuf>,
            preload: HashMap<PathBuf, Vec<u8>>,
            workdir: Option<PathBuf>,
            exec: Executor,
        }

        fn split_and_parse(state: &RecState,
                           diagpath: String,
                           buf: Vec<u8>)
                           -> Vec<Promise<Vec<Segment>>> {
            if state.options.autosplit && buf.len() > 1_048_576 {
                let mut promises = Vec::new();
                let mut sstart = 0;
                loop {
                    if let Some(chap) = find_chapter_header(&buf[sstart..]) {
                        let diagpath = diagpath.clone();
                        let subbuf = buf[sstart..sstart + chap].to_owned();

                        promises.push(state.exec
                            .exec(move || parser::parse_segments(diagpath, &Arc::new(subbuf))));
                        sstart += chap;
                    } else {
                        let subbuf = buf[sstart..].to_owned();
                        promises.push(state.exec
                            .exec(move || parser::parse_segments(diagpath, &Arc::new(subbuf))));
                        return promises;
                    }
                }
            } else {
                vec![state.exec.exec(move || parser::parse_segments(diagpath, &Arc::new(buf)))]
            }
        }

        fn canonicalize_and_read(state: &mut RecState,
                                 path: PathBuf)
                                 -> io::Result<Vec<Promise<Vec<Segment>>>> {
            let cpath = try!(path.canonicalize());
            if state.workdir.is_none() {
                state.workdir = Some(try!(try!(env::current_dir()).canonicalize()));
            }
            let relcpath =
                cpath.strip_prefix(&state.workdir.as_ref().unwrap()).unwrap_or(&cpath).to_owned();
            if !state.included.insert(relcpath.to_path_buf()) {
                return Ok(Vec::new());
            }
            let mut fh = try!(File::open(&relcpath));
            let mut buf = Vec::new();
            try!(fh.read_to_end(&mut buf));

            let diagpath = relcpath.to_string_lossy().into_owned();
            Ok(split_and_parse(state, diagpath, buf))
        }

        fn read_and_parse(state: &mut RecState, path: PathBuf) -> Vec<Promise<Vec<Segment>>> {
            if !state.pre_included.insert(path.clone()) {
                return Vec::new();
            }
            let path_str = path.to_string_lossy().into_owned();
            match state.preload.get(&path).cloned() {
                None => {
                    // read from FS
                    match canonicalize_and_read(state, path) {
                        Err(cerr) => {
                            let svec = vec![parser::dummy_segment(path_str,
                                                       Diagnostic::IoError(format!("{}", cerr)))];
                            vec![state.exec.exec(move || svec)]
                        }
                        Ok(segments) => segments,
                    }
                }
                Some(data) => split_and_parse(state, path_str, data),
            }
        }

        fn flat(inp: Vec<Promise<Vec<Segment>>>) -> Vec<Segment> {
            inp.into_iter().flat_map(|x| x.wait()).collect()
        }

        fn recurse(state: &mut RecState, path: PathBuf, segments: Vec<Segment>) {
            let mut promises = VecDeque::new();
            for seg in &segments {
                if seg.next_file != Span::null() {
                    let chain = str::from_utf8(seg.next_file.as_ref(&seg.buffer))
                        .expect("parser verified ASCII")
                        .to_owned();
                    let newpath = path.parent().unwrap_or(&path).join(PathBuf::from(chain));
                    promises.push_back((newpath.clone(), read_and_parse(state, newpath)));
                }
            }
            for seg in segments {
                if seg.next_file != Span::null() {
                    state.segments.push(seg);
                    let (newpath, pp) = promises.pop_front().unwrap();
                    recurse(state, newpath, flat(pp));
                } else {
                    state.segments.push(seg);
                }
            }
        }

        let mut state = RecState {
            options: self.options.clone(),
            segments: Vec::new(),
            included: new_set(),
            pre_included: new_set(),
            preload: data.into_iter().collect(),
            workdir: None,
            exec: self.exec.clone(),
        };

        let isegs = flat(read_and_parse(&mut state, path.clone()));
        recurse(&mut state, path, isegs);

        let mut order = SegmentOrder::new();
        self.segments = new_map();

        let start = order.start();
        for seg in state.segments {
            let id = order.new_before(start);
            self.segments.insert(id, Arc::new(seg));
        }
        self.order = Arc::new(order);
    }
}
