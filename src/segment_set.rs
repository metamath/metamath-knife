use database::DbOptions;
use database::Executor;
use database::Promise;
use diag::Diagnostic;
use filetime::FileTime;
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
use std::fs;
use std::fs::File;
use std::hash::Hash;
use std::hash::Hasher;
use std::io;
use std::io::Read;
use std::mem;
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

#[derive(Debug)]
pub struct SourceInfo {
    pub name: String,
    pub text: Arc<Vec<u8>>,
    pub span: Span,
}

#[derive(Debug,Clone)]
struct SliceSR(Option<LongBuf>, Vec<Arc<Segment>>, Arc<SourceInfo>);
#[derive(Debug,Clone)]
struct FileSR(Option<(String, FileTime)>, Vec<SliceSR>);

#[derive(Debug,Clone)]
pub struct SegmentSet {
    pub options: Arc<DbOptions>,
    pub exec: Executor,
    pub order: Arc<SegmentOrder>,
    pub segments: HashMap<SegmentId, (Arc<Segment>, Arc<SourceInfo>)>,
    parse_cache: HashMap<LongBuf, Vec<Arc<Segment>>>,
    file_cache: HashMap<(String, FileTime), FileSR>,
}

impl SegmentSet {
    pub fn new(opts: Arc<DbOptions>, exec: &Executor) -> Self {
        SegmentSet {
            options: opts,
            exec: exec.clone(),
            order: Arc::new(SegmentOrder::new()),
            segments: new_map(),
            parse_cache: new_map(),
            file_cache: new_map(),
        }
    }

    pub fn segments(&self) -> Vec<SegmentRef> {
        let mut out: Vec<SegmentRef> = self.segments
            .iter()
            .map(|(&seg_id, &(ref seg, ref _sinfo))| {
                SegmentRef {
                    id: seg_id,
                    segment: &seg,
                }
            })
            .collect();
        out.sort_by(|x, y| self.order.cmp(&x.id, &y.id));
        out
    }

    pub fn segment(&self, seg_id: SegmentId) -> SegmentRef {
        SegmentRef {
            id: seg_id,
            segment: &self.segments[&seg_id].0,
        }
    }

    pub fn source_info(&self, seg_id: SegmentId) -> &Arc<SourceInfo> {
        &self.segments[&seg_id].1
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

    pub fn read(&mut self, path: String, data: Vec<(String, Vec<u8>)>) {
        struct RecState {
            options: Arc<DbOptions>,
            old_by_content: HashMap<LongBuf, Vec<Arc<Segment>>>,
            new_by_content: HashMap<LongBuf, Vec<Arc<Segment>>>,
            old_by_time: HashMap<(String, FileTime), FileSR>,
            new_by_time: HashMap<(String, FileTime), FileSR>,
            segments: SegList,
            included: HashSet<String>,
            preload: HashMap<String, Vec<u8>>,
            exec: Executor,
        }

        type SegList = Vec<(Arc<Segment>, Arc<SourceInfo>)>;

        fn split_and_parse(state: &RecState,
                           path: String,
                           timestamp: Option<FileTime>,
                           buf: Vec<u8>)
                           -> Promise<FileSR> {
            let mut parts = Vec::new();
            let buf = Arc::new(buf);
            if state.options.autosplit && buf.len() > 1_048_576 {
                let mut sstart = 0;
                loop {
                    if let Some(chap) = find_chapter_header(&buf[sstart..]) {
                        parts.push(sstart..sstart + chap);
                        sstart += chap;
                    } else {
                        parts.push(sstart..buf.len());
                        break;
                    }
                }
            } else {
                parts.push(0..buf.len());
            }

            let mut promises = Vec::new();
            for range in parts {
                let partbuf = if range == (0..buf.len()) {
                    buf.clone()
                } else {
                    Arc::new(buf[range.clone()].to_owned())
                };

                let srcinfo = Arc::new(SourceInfo {
                    name: path.clone(),
                    text: buf.clone(),
                    span: Span::new(range.start, range.end),
                });

                let name = LongBuf(partbuf.clone());

                match state.old_by_content.get(&name) {
                    Some(eseg) => {
                        let sres = SliceSR(Some(name), eseg.clone(), srcinfo);
                        promises.push(Promise::new(sres));
                    }
                    None => {
                        let trace = state.options.trace_recalc;
                        promises.push(state.exec.exec(partbuf.len(), move || {
                            if trace {
                                println!("parse({:?})", parser::guess_buffer_name(&partbuf));
                            }
                            SliceSR(Some(name), parser::parse_segments(&partbuf), srcinfo)
                        }));
                    }
                }
            }
            Promise::join(promises)
                .map(move |srlist| FileSR(timestamp.map(move |s| (path.clone(), s)), srlist))
        }

        fn canonicalize_and_read(state: &mut RecState,
                                 path: String)
                                 -> io::Result<Promise<FileSR>> {
            let time = FileTime::from_last_modification_time(&try!(fs::metadata(&path)));

            match state.old_by_time.get(&(path.clone(), time)) {
                Some(old_fsr) => Ok(Promise::new(old_fsr.clone())),
                None => {
                    let mut fh = try!(File::open(&path));
                    let mut buf = Vec::new();
                    try!(fh.read_to_end(&mut buf));

                    Ok(split_and_parse(state, path, Some(time), buf))
                }
            }
        }

        fn read_and_parse(state: &mut RecState, path: String) -> Promise<FileSR> {
            if !state.included.insert(path.clone()) {
                return Promise::new(FileSR(None, Vec::new()));
            }
            match state.preload.get(&path).cloned() {
                None => {
                    // read from FS
                    match canonicalize_and_read(state, path.clone()) {
                        Err(cerr) => {
                            let sinfo = SourceInfo {
                                name: path.clone(),
                                text: Arc::new(Vec::new()),
                                span: Span::null(),
                            };
                            let svec = vec![parser::dummy_segment(Diagnostic::IoError(format!("{}",
                                                                                       cerr)))];
                            Promise::new(FileSR(None, vec![SliceSR(None, svec, Arc::new(sinfo))]))
                        }
                        Ok(segments) => segments,
                    }
                }
                Some(data) => split_and_parse(state, path, None, data),
            }
        }

        fn flat(state: &mut RecState, inp: FileSR) -> SegList {
            let mut out = Vec::new();
            if let Some(key) = inp.0.clone() {
                state.new_by_time.insert(key, inp.clone());
            }
            for SliceSR(nameo, vec, sinfo) in inp.1 {
                if let Some(name) = nameo {
                    state.new_by_content.insert(name, vec.clone());
                }
                for aseg in vec {
                    out.push((aseg, sinfo.clone()));
                }
            }
            out
        }

        fn recurse(state: &mut RecState, segments: SegList) {
            let mut promises = VecDeque::new();
            for seg in &segments {
                if seg.0.next_file != Span::null() {
                    let chain = str::from_utf8(seg.0.next_file.as_ref(&seg.0.buffer))
                        .expect("parser verified ASCII")
                        .to_owned();
                    promises.push_back(read_and_parse(state, chain));
                }
            }
            for seg in segments {
                if seg.0.next_file != Span::null() {
                    state.segments.push(seg);
                    let pp = promises.pop_front().unwrap().wait();
                    let nsegs = flat(state, pp);
                    recurse(state, nsegs);
                } else {
                    state.segments.push(seg);
                }
            }
        }

        let mut state = RecState {
            options: self.options.clone(),
            old_by_content: mem::replace(&mut self.parse_cache, new_map()),
            new_by_content: new_map(),
            old_by_time: mem::replace(&mut self.file_cache, new_map()),
            new_by_time: new_map(),
            segments: Vec::new(),
            included: new_set(),
            preload: data.into_iter().collect(),
            exec: self.exec.clone(),
        };

        let isegs = read_and_parse(&mut state, path.clone());
        let isegs = flat(&mut state, isegs.wait());
        recurse(&mut state, isegs);

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
              ptr_eq::<Segment>(&(old_segs[old_r.start].1).0, &new_segs[new_r.start].0) {
            old_r.start += 1;
            new_r.start += 1;
        }

        while old_r.start < old_r.end && new_r.start < new_r.end &&
              ptr_eq::<Segment>(&(old_segs[old_r.end - 1].1).0, &new_segs[new_r.end - 1].0) {
            old_r.end -= 1;
            new_r.end -= 1;
        }

        // reuse as many IDs as possible
        self.parse_cache = state.new_by_content;
        self.file_cache = state.new_by_time;

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
