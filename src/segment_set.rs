//! Incremental multi-file parser and result set.
//!
//! Again, if you're not writing an analysis pass you should be dealing with
//! `database`, not this directly.
//!
//! The `parser` handles low-level parsing for slices of text, producing one or
//! more segments; but this module handles the generation of slices, including
//! the recursive loading of files from disk, implements the autosplit
//! heuristic, and caching.
//!
//! # Caching
//!
//! The caching is the trickiest bit here.  Most analysis passes identify work
//! granules by `SegmentId`, and then decide if work needs to be redone by
//! checking if there is a new id or the address of the `Segment` for that ID
//! has changed; since we're responsible for ID assignment, we can't use IDs for
//! caching inside this module.
//!
//! segment_set implements two levels of caching:
//!
//! 1. When a file is loaded from disk, its pathname and modification time are
//! saved, along with all of the segments which it generated.  If the file
//! hasn't changed at all, we can reuse the segments after a single `stat`.
//!
//! 1. After a file is loaded and split, slices are cached by content.  This
//! speeds up operation when local changes are made to large files, or when
//! modification times cannot be used (such as some language server scenarios).
//!
//! In either case, some care is needed to retain only data which is relevant in
//! the cache.  The caches are discarded on every read, but any data obtained
//! from a cache miss is forwarded immediatly to the new cache; and hits in the
//! first cache also copy the data for the second cache.  I'm not convinced the
//! logic is right.
//!
//! # Diffing
//!
//! After the segments are read and parsed (possibly with cache hits), segment
//! IDs need to be assigned.  The rule is that two segment IDs will never change
//! relative order; thus adding and removing segments is easy, but we can't
//! always reuse the ID even if we can reuse the `Segment`, if the order has
//! changed.
//!
//! The most correct thing to do here would be a longest common subsequence
//! calculation; currently we cheat and renumber all segments except for the
//! common prefix and common suffix.  Thus, highly localized changes will keep
//! most IDs the same, but if you make changes and the beginning and the end,
//! most IDs will change and require new work from analysis passes.  A full LCS
//! would make changing the beginning and end at the same time faster, and is
//! attractive future work.

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

/// Memory buffer wrapper which hashes by length.
///
/// We don't want to repeatedly hash tens of MBs of source text; but the
/// segments are long enough that their lengths are likely to contain enough
/// entropy already.
#[derive(Eq,PartialEq,Clone,Debug)]
struct LongBuf(Arc<Vec<u8>>);

impl Hash for LongBuf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
    }
}

/// Tracks source information for a Segment that can be used by the diagnostic
/// printer.
///
/// By separating this data from the segment itself, the segment can be reused
/// even if its filename or (more likely) byte offset within a sliced file
/// changes.
///
/// _This is likely to change when line number calculation is added._
#[derive(Debug)]
pub struct SourceInfo {
    /// Name of the source file as loaded.
    pub name: String,
    /// Reference to the full unsliced source buffer.
    pub text: Arc<Vec<u8>>,
    /// Span of the parser input within the file; all spans reported by the
    /// parser are relative to this.
    pub span: Span,
}

/// The result of parsing one or more segments from a single slice of a source
/// file is a segment collection, a source file reference, and possibly text to
/// use for inserting into the second cache.  If this parsing result applies to
/// an I/O error, then it will not be inserted into the second cache as the
/// "source" is not discriminating in that case (it will be empty).
#[derive(Debug,Clone)]
struct SliceSR(Option<LongBuf>, Vec<Arc<Segment>>, Arc<SourceInfo>);
/// The result of parsing an actual source file is one or more slice results,
/// and a key for the first cache if successful.
#[derive(Debug,Clone)]
struct FileSR(Option<(String, FileTime)>, Vec<SliceSR>);

/// SegmentSet is a container for parsed databases.
///
/// If you're not writing an analysis pass you want to handle this through
/// `Database`, but if you are then aliasing prevents using that and you'll be
/// using this directly.
///
/// The SegmentSet tracks all of the segments reachable from the current start
/// file with parsing results and cache information to allow fast incremental
/// reloads.  It maintains the ordering of the segments, and provides a
/// `SegmentOrder` object which can be used to compare segment IDs.  It is
/// currently also a convenient access point for analysis passes to get the
/// option block and the work queue executor, although those responsibilities
/// may be moved.
#[derive(Debug,Clone)]
pub struct SegmentSet {
    /// The option block controlling this database.
    pub options: Arc<DbOptions>,
    /// The work queue for use with this database.
    pub exec: Executor,
    /// Order structure which records the relative order of segment IDs created
    /// by the SegmentSet.
    pub order: Arc<SegmentOrder>,
    /// Track segment and source info in parallel so they can be updated
    /// independently in the slicing case and if a file is renamed.
    segments: HashMap<SegmentId, (Arc<Segment>, Arc<SourceInfo>)>,
    /// First cache as described in the module comment.
    file_cache: HashMap<(String, FileTime), FileSR>,
    /// Second cache as described in the module comment.
    parse_cache: HashMap<LongBuf, Vec<Arc<Segment>>>,
}

impl SegmentSet {
    /// Start a new empty segment set in the context of an option block and
    /// executor which were previously created by the `Database`.
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

    /// Iterates over all loaded segments in logical order.
    pub fn segments(&self) -> Vec<SegmentRef> {
        // this might be an actual iterator in the future if needs be
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

    /// Fetch a handle to a loaded segment given its ID.
    pub fn segment(&self, seg_id: SegmentId) -> SegmentRef {
        SegmentRef {
            id: seg_id,
            segment: &self.segments[&seg_id].0,
        }
    }

    /// Fetch a handle to a loaded segment given a possibly stale ID.
    pub fn segment_opt(&self, seg_id: SegmentId) -> Option<SegmentRef> {
        self.segments.get(&seg_id).map(|&(ref seg, ref _srcinfo)| {
            SegmentRef {
                id: seg_id,
                segment: &seg,
            }
        })
    }

    /// Fetch source information for a loaded segment given its ID.
    pub fn source_info(&self, seg_id: SegmentId) -> &Arc<SourceInfo> {
        &self.segments[&seg_id].1
    }

    /// Fetches a handle to a statement given a global address.
    pub fn statement(&self, addr: StatementAddress) -> StatementRef {
        self.segment(addr.segment_id).statement(addr.index)
    }

    /// Reports any parse errors associated with loaded segments.
    pub fn parse_diagnostics(&self) -> Vec<(StatementAddress, Diagnostic)> {
        let mut out = Vec::new();
        for sref in self.segments() {
            for &(ix, ref d) in &sref.diagnostics {
                out.push((StatementAddress::new(sref.id, ix), d.clone()));
            }
        }
        out
    }

    /// Replaces the content of the `SegmentSet` with data loaded from disk
    /// files or memory.
    ///
    /// Each element of `data` intercedes a file with the same name for the
    /// purposes of file inclusion statements.  If a match is not made in
    /// `data`, it will be accessed as a file relative to the current directory.
    pub fn read(&mut self, path: String, data: Vec<(String, Vec<u8>)>) {
        // data which is kept during the recursive load process, which does
        // _not_ have access to the SegmentSet
        struct RecState {
            options: Arc<DbOptions>,
            /// second cache from the last load
            old_by_content: HashMap<LongBuf, Vec<Arc<Segment>>>,
            /// second cache which will be saved after this load is done
            new_by_content: HashMap<LongBuf, Vec<Arc<Segment>>>,
            /// first cache from the last load
            old_by_time: HashMap<(String, FileTime), FileSR>,
            /// first cache which will be saved after this load is done
            new_by_time: HashMap<(String, FileTime), FileSR>,
            /// segments which have been placed in the order so far
            segments: SegList,
            included: HashSet<String>,
            preload: HashMap<String, Vec<u8>>,
            exec: Executor,
        }

        /// one or more segments with provenance, the output of the cache
        type SegList = Vec<(Arc<Segment>, Arc<SourceInfo>)>;

        /// Given a buffer of data from a file, split it and queue jobs to do
        /// the parsing.
        fn split_and_parse(state: &RecState,
                           path: String,
                           timestamp: Option<FileTime>,
                           buf: Vec<u8>)
                           -> Promise<FileSR> {
            let mut parts = Vec::new();
            let buf = Arc::new(buf);
            // see if we need to parse this file in multiple slices.  the
            // slicing is a slight incompatibility (no chapter headers inside
            // groups) but is needed for full parallelism
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

                let cachekey = LongBuf(partbuf.clone());

                // probe the old second cache
                match state.old_by_content.get(&cachekey) {
                    Some(eseg) => {
                        // hit, don't queue a job.  keep the name so that it
                        // gets reinserted into the new second cache.
                        let sres = SliceSR(Some(cachekey), eseg.clone(), srcinfo);
                        promises.push(Promise::new(sres));
                    }
                    None => {
                        let trace = state.options.trace_recalc;
                        // parse it on a worker thread
                        promises.push(state.exec.exec(partbuf.len(), move || {
                            if trace {
                                println!("parse({:?})", parser::guess_buffer_name(&partbuf));
                            }
                            SliceSR(Some(cachekey), parser::parse_segments(&partbuf), srcinfo)
                        }));
                    }
                }
            }
            // make a wrapper promise to build the proper file result.  this
            // does _not_ run on a worker thread
            Promise::join(promises)
                .map(move |srlist| FileSR(timestamp.map(move |s| (path.clone(), s)), srlist))
        }

        // read a file from disk (intercessions have already been checked, but
        // the first cache has not) and split/parse it; returns by try! on I/O
        // error
        fn canonicalize_and_read(state: &mut RecState,
                                 path: String)
                                 -> io::Result<Promise<FileSR>> {
            let metadata = try!(fs::metadata(&path));
            let time = FileTime::from_last_modification_time(&metadata);

            // probe 1st cache
            match state.old_by_time.get(&(path.clone(), time)) {
                Some(old_fsr) => Ok(Promise::new(old_fsr.clone())),
                None => {
                    // miss, but we have the file size, so try to read in one
                    // call to a buffer we won't have to move
                    let mut fh = try!(File::open(&path));
                    let mut buf = Vec::with_capacity(metadata.len() as usize + 1);
                    // note: File's read_to_end uses the buffer capacity to choose how much to read
                    try!(fh.read_to_end(&mut buf));

                    Ok(split_and_parse(state, path, Some(time), buf))
                }
            }
        }

        // We have a filename and an incomplete database in the RecState, read
        // it and queue tasks to parse
        fn read_and_parse(state: &mut RecState, path: String) -> Promise<FileSR> {
            // THIS IS WRONG: https://github.com/sorear/smetamath-rs/issues/22

            // We do need to avoid issuing multiple parses for the same file,
            // but catching it here leads to misassociation
            if !state.included.insert(path.clone()) {
                return Promise::new(FileSR(None, Vec::new()));
            }
            // check intercessions
            match state.preload.get(&path).cloned() {
                None => {
                    // read from FS
                    canonicalize_and_read(state, path.clone()).unwrap_or_else(|cerr| {
                        // read failed, insert a bogus segment so we have a
                        // place to hang the errors
                        let sinfo = SourceInfo {
                            name: path.clone(),
                            text: Arc::new(Vec::new()),
                            span: Span::null(),
                        };
                        let seg = parser::dummy_segment(Diagnostic::IoError(format!("{}", cerr)));
                        // cache keys are None so this won't pollute any caches
                        Promise::new(FileSR(None, vec![SliceSR(None, vec![seg], Arc::new(sinfo))]))
                    })
                }
                Some(data) => split_and_parse(state, path, None, data),
            }
        }

        // File data has come back from the worker thread, make sure it's in the
        // first and second caches as appropriate, even if it came from a hit
        // earlier
        fn flat(state: &mut RecState, inp: FileSR) -> SegList {
            let mut out = Vec::new();
            if let Some(key) = inp.0.clone() {
                // insert into 1st cache
                state.new_by_time.insert(key, inp.clone());
            }
            for SliceSR(nameo, vec, sinfo) in inp.1 {
                if let Some(name) = nameo {
                    // insert into 2nd cache
                    state.new_by_content.insert(name, vec.clone());
                }
                for aseg in vec {
                    // we have a contextualized segment
                    out.push((aseg, sinfo.clone()));
                }
            }
            out
        }

        // The main recursive parsing driver; we've already parsed one file, now
        // incorporate it into the database under construction while parsing
        // includes
        fn recurse(state: &mut RecState, segments: SegList) {
            let mut promises = VecDeque::new();

            for seg in &segments {
                if seg.0.next_file != Span::null() {
                    let chain = str::from_utf8(seg.0.next_file.as_ref(&seg.0.buffer))
                        .expect("parser verified ASCII")
                        .to_owned();
                    // parse this include in the background
                    promises.push_back(read_and_parse(state, chain));
                }
            }
            for seg in segments {
                if seg.0.next_file != Span::null() {
                    state.segments.push(seg);
                    // wait for include to be done parsing, incorporate it and
                    // recurse
                    let pp = promises.pop_front().unwrap().wait();
                    let nsegs = flat(state, pp);
                    recurse(state, nsegs);
                } else {
                    state.segments.push(seg);
                }
            }
        }

        // Note that we clear out the caches immediately, and only copy forward
        // things that are actually used, to avoid memory bloat

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

        // parse and recursively incorporate the initial file
        let isegs = read_and_parse(&mut state, path.clone());
        let isegs = flat(&mut state, isegs.wait());
        recurse(&mut state, isegs);

        // we now have the new and old segment lists, time for ID allocaton.
        // see module comment about LCS options
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

        // reuse as many IDs as possible even if the segment isn't exactly the
        // same.  Hopefully the corresponding new and old segments are _similar_
        // and later passes will be able to leverage that similarity
        self.parse_cache = state.new_by_content;
        self.file_cache = state.new_by_time;

        while old_r.start < old_r.end && new_r.start < new_r.end {
            self.segments.insert(old_segs[old_r.start].0, new_segs[new_r.start].clone());
            new_r.start += 1;
            old_r.start += 1;
        }

        // now actually reassign the IDs
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
