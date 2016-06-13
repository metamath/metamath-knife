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
use std::env;
use std::fs::File;
use std::hash::Hash;
use std::hash::Hasher;
use std::io;
use std::io::Read;
use std::mem;
use std::path::PathBuf;
use std::str;
use std::sync::Arc;
use util::find_chapter_header;
use util::HashMap;
use util::HashSet;
use util::new_map;
use util::new_set;
use util::ptr_eq;

#[derive(Eq,PartialEq,Clone,Debug)]
struct LongBuf(Arc<Vec<u8>>);

impl Hash for LongBuf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
    }
}

#[derive(Debug,Clone)]
pub struct SegmentSet {
    pub options: Arc<DbOptions>,
    pub exec: Executor,
    pub order: Arc<SegmentOrder>,
    pub segments: HashMap<SegmentId, Arc<Segment>>,
    parse_cache: HashMap<(String, LongBuf), Vec<Arc<Segment>>>,
}

impl SegmentSet {
    pub fn new(opts: Arc<DbOptions>, exec: &Executor) -> Self {
        SegmentSet {
            options: opts,
            exec: exec.clone(),
            order: Arc::new(SegmentOrder::new()),
            segments: new_map(),
            parse_cache: new_map(),
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
            existing: HashMap<(String, LongBuf), Vec<Arc<Segment>>>,
            new_cache: HashMap<(String, LongBuf), Vec<Arc<Segment>>>,
            segments: Vec<Arc<Segment>>,
            pre_included: HashSet<PathBuf>,
            included: HashSet<PathBuf>,
            preload: HashMap<PathBuf, Vec<u8>>,
            workdir: Option<PathBuf>,
            exec: Executor,
        }

        type ScanResult = (Option<(String, LongBuf)>, Vec<Arc<Segment>>);

        fn split_and_parse(state: &RecState,
                           diagpath: String,
                           buf: Vec<u8>)
                           -> Vec<Promise<ScanResult>> {
            let mut parts = Vec::new();
            if state.options.autosplit && buf.len() > 1_048_576 {
                let mut sstart = 0;
                loop {
                    if let Some(chap) = find_chapter_header(&buf[sstart..]) {
                        parts.push(buf[sstart..sstart + chap].to_owned());
                        sstart += chap;
                    } else {
                        parts.push(buf[sstart..].to_owned());
                        break;
                    }
                }
            } else {
                parts.push(buf);
            }

            let mut promises = Vec::new();
            for buf in parts {
                let buf = Arc::new(buf);
                let diagpath = diagpath.clone();
                let name = (diagpath.clone(), LongBuf(buf.clone()));
                match state.existing.get(&name) {
                    Some(eseg) => {
                        let sres = (Some(name), eseg.clone());
                        promises.push(state.exec.exec(move || sres));
                    }
                    None => {
                        promises.push(state.exec
                            .exec(move || (Some(name), parser::parse_segments(diagpath, &buf))));
                    }
                }
            }
            promises
        }

        fn canonicalize_and_read(state: &mut RecState,
                                 path: PathBuf)
                                 -> io::Result<Vec<Promise<ScanResult>>> {
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

        fn read_and_parse(state: &mut RecState, path: PathBuf) -> Vec<Promise<ScanResult>> {
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
                            vec![state.exec.exec(move || (None, svec))]
                        }
                        Ok(segments) => segments,
                    }
                }
                Some(data) => split_and_parse(state, path_str, data),
            }
        }

        fn flat(state: &mut RecState, inp: Vec<Promise<ScanResult>>) -> Vec<Arc<Segment>> {
            let mut out = Vec::new();
            for promise in inp {
                let (nameo, vec) = promise.wait();
                if let Some(name) = nameo {
                    state.new_cache.insert(name, vec.clone());
                }
                out.extend_from_slice(&vec);
            }
            out
        }

        fn recurse(state: &mut RecState, path: PathBuf, segments: Vec<Arc<Segment>>) {
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
                    let nsegs = flat(state, pp);
                    recurse(state, newpath, nsegs);
                } else {
                    state.segments.push(seg);
                }
            }
        }

        let mut state = RecState {
            options: self.options.clone(),
            existing: mem::replace(&mut self.parse_cache, new_map()),
            new_cache: new_map(),
            segments: Vec::new(),
            included: new_set(),
            pre_included: new_set(),
            preload: data.into_iter().collect(),
            workdir: None,
            exec: self.exec.clone(),
        };

        let isegs = read_and_parse(&mut state, path.clone());
        let isegs = flat(&mut state, isegs);
        recurse(&mut state, path, isegs);

        let mut old_segs = Vec::new();
        for (&seg_id, seg) in &self.segments {
            old_segs.push((seg_id, seg.clone()));
        }
        old_segs.sort_by(|x, y| self.order.cmp(&x.0, &y.0));
        let mut new_segs = state.segments;

        let mut old_r = 0..old_segs.len();
        let mut new_r = 0..new_segs.len();

        // LCS lite
        while old_r.start < old_r.end && new_r.start < new_r.end &&
              ptr_eq::<Segment>(&old_segs[old_r.start].1, &new_segs[new_r.start]) {
            old_r.start += 1;
            new_r.start += 1;
        }

        while old_r.start < old_r.end && new_r.start < new_r.end &&
              ptr_eq::<Segment>(&old_segs[old_r.end - 1].1, &new_segs[new_r.end - 1]) {
            old_r.end -= 1;
            new_r.end -= 1;
        }

        // reuse as many IDs as possible
        self.parse_cache = state.new_cache;
        while old_r.start < old_r.end && new_r.start < new_r.end {
            self.segments.insert(old_segs[old_r.start].0, new_segs[new_r.start].clone());
            new_r.start += 1;
            old_r.start += 1;
        }

        let order = Arc::make_mut(&mut self.order);
        for &(id, _) in &old_segs[old_r.clone()] {
            order.free_id(id);
            self.segments.remove(&id);
        }

        let before = if old_r.end == old_segs.len() {
            order.start()
        } else {
            old_segs[old_r.end].0
        };

        for seg in new_segs.drain(new_r) {
            let id = order.new_before(before);
            self.segments.insert(id, seg);
        }
    }
}
