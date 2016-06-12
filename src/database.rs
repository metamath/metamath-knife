use std::collections::VecDeque;
use std::fmt;
use std::panic;
use std::sync::Arc;
use std::sync::Condvar;
use std::sync::Mutex;
use std::thread;

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
