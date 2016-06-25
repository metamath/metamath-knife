use diag;
use diag::Notation;
use nameck::Nameset;
use scopeck;
use scopeck::ScopeResult;
use segment_set::SegmentSet;
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt;
use std::panic;
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
    pub trace_recalc: bool,
    pub verify: bool,
    pub incremental: bool,
    pub jobs: usize,
}

struct Job(usize, Box<FnMut() + Send>);
impl PartialEq for Job {
    fn eq(&self, other: &Job) -> bool {
        self.0 == other.0
    }
}
impl Eq for Job {}
impl PartialOrd for Job {
    fn partial_cmp(&self, other: &Job) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}
impl Ord for Job {
    fn cmp(&self, other: &Job) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[derive(Clone)]
pub struct Executor {
    concurrency: usize,
    mutex: Arc<Mutex<BinaryHeap<Job>>>,
    work_cv: Arc<Condvar>,
}

impl fmt::Debug for Executor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let g = self.mutex.lock().unwrap();
        write!(f, "Executor(active={})", g.len())
    }
}

fn queue_work(exec: &Executor, estimate: usize, mut f: Box<FnMut() + Send>) {
    if exec.concurrency <= 1 {
        f();
        return;
    }
    let mut wq = exec.mutex.lock().unwrap();
    wq.push(Job(estimate, f));
    exec.work_cv.notify_one();
}

impl Executor {
    pub fn new(concurrency: usize) -> Executor {
        let mutex: Arc<Mutex<BinaryHeap<Job>>> = Default::default();
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
                            mutexg.pop().unwrap()
                        };
                        (task.1)();
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

    pub fn exec<TASK, RV>(&self, estimate: usize, task: TASK) -> Promise<RV>
        where TASK: FnOnce() -> RV,
              TASK: Send + 'static,
              RV: Send + 'static
    {
        let parts: Arc<(Mutex<Option<thread::Result<RV>>>, Condvar)> = Default::default();

        let partsc = parts.clone();
        let mut tasko = Some(task);
        queue_work(self,
                   estimate,
                   Box::new(move || {
            let mut g = partsc.0.lock().unwrap();
            let taskf = panic::AssertUnwindSafe(tasko.take().expect("should only be called once"));
            *g = Some(panic::catch_unwind(taskf));
            partsc.1.notify_one();
        }));

        let awaiter = move || {
            let mut g = parts.0.lock().unwrap();
            while g.is_none() {
                g = parts.1.wait(g).unwrap();
            }
            g.take().unwrap().unwrap()
        };
        Promise(Box::new(awaiter))
    }
}

// if we start getting serious about performance, this will have to be fancier
// note: boxed function will be called once only
pub struct Promise<T>(Box<FnMut() -> T + Send>);

impl<T> Promise<T> {
    pub fn wait(mut self) -> T {
        (self.0)()
    }

    pub fn new_once<FN>(fun: FN) -> Promise<T>
        where FN: FnOnce() -> T + Send + 'static
    {
        let mut funcell = Some(fun);
        Promise(Box::new(move || (funcell.take().unwrap())()))
    }

    pub fn new(value: T) -> Self
        where T: Send + 'static
    {
        Promise::new_once(move || value)
    }

    pub fn map<FN, RV>(self, fun: FN) -> Promise<RV>
        where T: 'static,
              FN: 'static,
              FN: Send + FnOnce(T) -> RV
    {
        Promise::new_once(move || fun(self.wait()))
    }
}

impl<T: 'static> Promise<Vec<T>> {
    pub fn join(promises: Vec<Promise<T>>) -> Promise<Vec<T>> {
        let mut pcell = Some(promises);
        Promise(Box::new(move || pcell.take().unwrap().into_iter().map(|x| x.wait()).collect()))
    }
}

pub struct Database {
    options: Arc<DbOptions>,
    segments: Option<Arc<SegmentSet>>,
    prev_nameset: Option<Arc<Nameset>>,
    nameset: Option<Arc<Nameset>>,
    prev_scopes: Option<Arc<ScopeResult>>,
    scopes: Option<Arc<ScopeResult>>,
    prev_verify: Option<Arc<VerifyResult>>,
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
            self.prev_verify = None;
            self.verify = None;
            self.prev_scopes = None;
            self.scopes = None;
            self.prev_nameset = None;
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
            prev_nameset: None,
            prev_scopes: None,
            prev_verify: None,
        }
    }

    pub fn parse(&mut self, start: String, text: Vec<(String, Vec<u8>)>) {
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
            time(&self.options.clone(), "nameck", || {
                if self.prev_nameset.is_none() {
                    self.prev_nameset = Some(Arc::new(Nameset::new()));
                }
                let pr = self.parse_result().clone();
                {
                    let mut ns = Arc::make_mut(self.prev_nameset.as_mut().unwrap());
                    ns.update(&pr);
                }
                self.nameset = self.prev_nameset.clone();
            });
        }

        self.nameset.as_ref().unwrap()
    }

    pub fn scope_result(&mut self) -> &Arc<ScopeResult> {
        if self.scopes.is_none() {
            self.name_result();
            time(&self.options.clone(), "scopeck", || {
                if self.prev_scopes.is_none() {
                    self.prev_scopes = Some(Arc::new(ScopeResult::default()));
                }

                let parse = self.parse_result().clone();
                let name = self.name_result().clone();
                {
                    let mut ns = Arc::make_mut(self.prev_scopes.as_mut().unwrap());
                    scopeck::scope_check(ns, &parse, &name);
                }
                self.scopes = self.prev_scopes.clone();
            });
        }

        self.scopes.as_ref().unwrap()
    }

    pub fn verify_result(&mut self) -> &Arc<VerifyResult> {
        if self.verify.is_none() {
            self.name_result();
            self.scope_result();
            time(&self.options.clone(), "verify", || {
                if self.prev_verify.is_none() {
                    self.prev_verify = Some(Arc::new(VerifyResult::default()));
                }

                let parse = self.parse_result().clone();
                let scope = self.scope_result().clone();
                let name = self.name_result().clone();
                {
                    let mut ver = Arc::make_mut(self.prev_verify.as_mut().unwrap());
                    verify::verify(ver, &parse, &name, &scope);
                }
                self.verify = self.prev_verify.clone();
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
