use diag;
use diag::Notation;
use nameck::Nameset;
use scopeck;
use scopeck::ScopeResult;
use segment_set::SegmentSet;
use std::collections::VecDeque;
use std::fmt;
use std::panic;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;
use std::thread;
use std::time::Instant;
use verify;
use verify::VerifyResult;

#[derive(Default,Debug)]
pub struct DbOptions {
    pub autosplit: bool,
    pub timing: bool,
    pub verify: bool,
    pub jobs: usize,
}

#[derive(Clone)]
pub struct Executor {
    concurrency: usize,
    mutex: Arc<Mutex<VecDeque<Box<FnMut() + Send>>>>,
    work_cv: Arc<Condvar>,
}

impl fmt::Debug for Executor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let g = self.mutex.lock().unwrap();
        write!(f, "Executor(active={})", g.len())
    }
}

fn queue_work(exec: &Executor, mut f: Box<FnMut() + Send>) {
    if exec.concurrency <= 1 {
        f();
        return;
    }
    let mut wq = exec.mutex.lock().unwrap();
    wq.push_back(f);
    exec.work_cv.notify_one();
}

impl Executor {
    pub fn new(concurrency: usize) -> Executor {
        let mutex: Arc<Mutex<VecDeque<Box<FnMut() + Send>>>> = Default::default();
        let cv: Arc<Condvar> = Default::default();

        if concurrency > 1 {
            for _ in 0..concurrency {
                let mutex = mutex.clone();
                let cv = cv.clone();
                thread::spawn(move || {
                    loop {
                        let mut task = {
                            let mut mutexg = mutex.lock().unwrap();
                            while mutexg.is_empty() {
                                mutexg = cv.wait(mutexg).unwrap();
                            }
                            mutexg.pop_front().unwrap()
                        };
                        task();
                    }
                });
            }
        }

        Executor {
            concurrency: concurrency,
            mutex: mutex,
            work_cv: cv,
        }
    }

    pub fn exec<TASK, RV>(&self, task: TASK) -> Promise<RV>
        where TASK: FnOnce() -> RV,
              TASK: Send + 'static,
              RV: Send + 'static
    {
        let parts: Arc<(Mutex<Option<thread::Result<RV>>>, Condvar)> = Default::default();

        let partsc = parts.clone();
        let mut tasko = Some(task);
        queue_work(self,
                   Box::new(move || {
            let mut g = partsc.0.lock().unwrap();
            let taskf = panic::AssertUnwindSafe(tasko.take().expect("should only be called once"));
            *g = Some(panic::catch_unwind(taskf));
            partsc.1.notify_one();
        }));

        Promise { inner: parts }
    }
}

pub struct Promise<T> {
    inner: Arc<(Mutex<Option<thread::Result<T>>>, Condvar)>,
}

impl<T> Promise<T> {
    pub fn wait(self) -> T {
        let mut g = self.inner.0.lock().unwrap();
        while g.is_none() {
            g = self.inner.1.wait(g).unwrap();
        }
        g.take().unwrap().unwrap()
    }
}

pub struct Database {
    options: Arc<DbOptions>,
    segments: Option<Arc<SegmentSet>>,
    nameset: Option<Arc<Nameset>>,
    scopes: Option<Arc<ScopeResult>>,
    verify: Option<Arc<VerifyResult>>,
}

fn time<R, F: FnOnce() -> R>(opts: &DbOptions, name: &str, f: F) -> R {
    let now = Instant::now();
    let ret = f();
    if opts.timing {
        println!("{} {}ms", name, (now.elapsed() * 1000).as_secs());
    }
    ret
}

#[derive(Copy,Clone,Eq,PartialEq,Debug)]
pub enum DiagnosticClass {
    Parse,
    Scope,
    Verify,
}

impl Drop for Database {
    fn drop(&mut self) {
        time(&self.options.clone(), "free", move || {
            self.verify = None;
            self.scopes = None;
            self.nameset = None;
            self.segments = None;
        });
    }
}

impl Database {
    pub fn new(options: DbOptions) -> Database {
        let options = Arc::new(options);
        let exec = Executor::new(options.jobs);
        Database {
            segments: Some(Arc::new(SegmentSet::new(options.clone(), &exec))),
            options: options,
            nameset: None,
            scopes: None,
            verify: None,
        }
    }

    pub fn parse(&mut self, start: PathBuf, text: Vec<(PathBuf, Vec<u8>)>) {
        time(&self.options.clone(), "parse", || {
            Arc::make_mut(self.segments.as_mut().unwrap()).read(start, text);
            self.nameset = None;
            self.scopes = None;
            self.verify = None;
        });
    }

    pub fn parse_result(&mut self) -> &Arc<SegmentSet> {
        self.segments.as_ref().unwrap()
    }

    pub fn name_result(&mut self) -> &Arc<Nameset> {
        if self.nameset.is_none() {
            self.nameset = time(&self.options.clone(), "nameck", || {
                let mut ns = Nameset::new();
                ns.update(self.parse_result());
                Some(Arc::new(ns))
            });
        }

        self.nameset.as_ref().unwrap()
    }

    pub fn scope_result(&mut self) -> &Arc<ScopeResult> {
        if self.scopes.is_none() {
            self.name_result();
            self.scopes = time(&self.options.clone(), "scopeck", || {
                let parse = self.parse_result().clone();
                let name = self.name_result().clone();
                Some(Arc::new(scopeck::scope_check(&parse, &name)))
            });
        }

        self.scopes.as_ref().unwrap()
    }

    pub fn verify_result(&mut self) -> &Arc<VerifyResult> {
        if self.verify.is_none() {
            self.name_result();
            self.scope_result();
            self.verify = time(&self.options.clone(), "verify", || {
                let parse = self.parse_result().clone();
                let scope = self.scope_result().clone();
                let name = self.name_result().clone();
                Some(Arc::new(verify::verify(&parse, &name, &scope)))
            });
        }
        self.verify.as_ref().unwrap()
    }

    pub fn diag_notations(&mut self, types: Vec<DiagnosticClass>) -> Vec<Notation> {
        let mut diags = Vec::new();
        if types.contains(&DiagnosticClass::Parse) {
            diags.extend(self.parse_result().parse_diagnostics());
        }
        if types.contains(&DiagnosticClass::Scope) {
            diags.extend(self.scope_result().diagnostics());
        }
        if types.contains(&DiagnosticClass::Verify) {
            diags.extend(self.verify_result().diagnostics());
        }
        time(&self.options.clone(),
             "diag",
             || diag::to_annotations(self.parse_result(), diags))
    }
}
