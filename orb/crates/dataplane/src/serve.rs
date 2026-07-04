//! The Lean seam: boot the proven runtime and cross it, once per request.
//!
//! Every crossing is one call to the exported `drorb_serve`
//! (`ByteArray -> ByteArray`), the same proven pipeline the shipped binaries
//! run. The bytes read off the wire go in unchanged and the proven response
//! bytes come back unchanged; the host decides nothing about a request's
//! meaning.
//!
//! ## Concurrency model
//!
//! The Lean runtime is a process-global singleton: `initialize_Dataplane`
//! installs the module's top-level constants once, and there is no way to stand
//! up N independent runtimes in one process. So a per-worker runtime is not an
//! option, and rather than rely on the compiled serve being safe to call from
//! many threads (the closure inc/dec's runtime objects and the small allocator
//! keeps thread-local state), the host confines every seam crossing to a single
//! dedicated thread that owns the runtime. That thread runs [`lean_boot`] and is
//! the only thread that ever calls `drorb_serve`; correctness never depends on
//! the compiled serve being reentrant.
//!
//! IO concurrency lives elsewhere (the event loops in `blocking`/`uring`): many
//! connections read and write in parallel and funnel completed requests to this
//! one serve thread over a channel. The serve computation itself is serialized
//! on the runtime-owner thread — the deliberate trade, and the one shared
//! resource in an otherwise share-nothing design (see `SINGLE-OWNER` note in
//! [`spawn_serve_thread`]).

use std::slice;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;

use crate::pool::{BufferPool, PooledBuf};

/// Opaque Lean heap object. We only ever hold `*mut LeanObject` and hand it
/// straight back across the FFI; its layout is the runtime's concern.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    // Real exported runtime + module symbols (libleanshared / the drorb archive).
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    fn initialize_Dataplane(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve] drorbServe : ByteArray -> ByteArray` — the proven
    /// pipeline. Consumes its argument, returns an owned ByteArray.
    fn drorb_serve(input: *mut LeanObject) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) for lean.h's inline sarray API.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Bring up the Lean runtime and initialize the proven module. Must run once,
/// before any `drorb_serve` call, on the thread that will own the runtime.
fn lean_boot() {
    // SAFETY: the exact runtime-init sequence leanc emits for a module main:
    // init the runtime, run the module initializer once against a fresh IO
    // world, check it succeeded, drop the result, then mark init end. Called
    // exactly once, on the runtime-owner thread, before any `drorb_serve`.
    unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Dataplane(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Dataplane returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    }
}

/// The one and only seam crossing: run the proven pipeline over `req` and
/// append the response bytes into `out` (cleared first). `out` is a pooled
/// buffer, so no response `Vec` is allocated per request on the host side.
/// Only ever invoked from the runtime-owning serve thread.
fn serve_into(req: &[u8], out: &mut Vec<u8>) {
    // SAFETY: `drorb_sarray_of_bytes` copies `req` into a fresh owned Lean
    // ByteArray (the runtime's per-call input alloc); `drorb_serve` consumes it
    // and returns an owned ByteArray whose bytes we copy out before dropping our
    // reference with `drorb_obj_dec`. Pointers from `drorb_sarray_ptr` are valid
    // for `len` bytes until that dec. All calls are on the single runtime-owner
    // thread.
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve(input); // consumes `input`, returns owned ByteArray
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// How a finished response is delivered back to the IO path that requested it.
pub enum ServeReply {
    /// Blocking thread-per-connection path: the worker blocks on this channel.
    Sync(Sender<PooledBuf>),
    /// io_uring path: the completed response is posted to the requesting
    /// shard's mailbox and the shard is woken through its eventfd.
    #[cfg(target_os = "linux")]
    Shard(Sender<ShardDone>, std::os::fd::RawFd, u32),
}

/// A response delivered to an io_uring shard: which connection it belongs to
/// and the pooled response bytes to write.
#[cfg(target_os = "linux")]
pub struct ShardDone {
    pub conn: u32,
    pub resp: PooledBuf,
}

/// A unit of work for the serve thread: request bytes plus where to deliver the
/// response.
pub struct ServeJob {
    pub req: PooledBuf,
    pub reply: ServeReply,
}

/// A cloneable handle the IO paths use to reach the serve thread.
#[derive(Clone)]
pub struct ServeGateway {
    tx: Sender<ServeJob>,
    pool: Arc<BufferPool>,
}

impl ServeGateway {
    /// The shared buffer pool. IO paths draw request/receive buffers from the
    /// same pool the serve thread draws response buffers from, so buffers
    /// recycle across the whole hot path.
    pub fn pool(&self) -> &Arc<BufferPool> {
        &self.pool
    }

    /// Submit one request to the proven core. The response is delivered per
    /// `reply`. Returns `false` only if the serve thread is gone (shutdown).
    pub fn submit(&self, req: PooledBuf, reply: ServeReply) -> bool {
        self.tx.send(ServeJob { req, reply }).is_ok()
    }

    /// Blocking convenience for the thread-per-connection path: submit `req`
    /// and wait for the pooled response. `reply_tx`/`reply_rx` are the worker's
    /// own reusable channel (one per connection, reused across keep-alive
    /// requests — no per-request channel allocation on the hot path). Returns
    /// `None` if the serve thread is gone.
    pub fn call(
        &self,
        req: PooledBuf,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        if !self.submit(req, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }
}

/// Boot the runtime on a dedicated thread and return a gateway to it. Blocks
/// until the runtime is up so bind failures are reported before we accept.
///
/// SINGLE-OWNER: this thread is the sole caller of `drorb_serve`. Every request
/// from every connection/shard serializes here, so the steady-state throughput
/// ceiling is `1 / (serve latency)` — one core's worth of the proven pipeline,
/// however many IO cores feed it. The IO path (recv/send, framing, TLS) scales
/// across cores; the pure `ByteArray -> ByteArray` transform does not, because
/// the runtime is a process-global singleton. This is the honest bottleneck to
/// measure and, if it binds, to lift only by a design that admits multiple
/// runtime owners.
pub fn spawn_serve_thread(pool: Arc<BufferPool>) -> ServeGateway {
    let (tx, rx) = channel::<ServeJob>();
    let (ready_tx, ready_rx) = channel::<()>();
    let serve_pool = Arc::clone(&pool);
    std::thread::Builder::new()
        .name("drorb-serve".into())
        .spawn(move || {
            lean_boot();
            let _ = ready_tx.send(());
            for job in rx {
                let mut resp = serve_pool.take();
                serve_into(&job.req, &mut resp);
                // `job.req` drops here, returning the request buffer to the pool.
                match job.reply {
                    ServeReply::Sync(tx) => {
                        let _ = tx.send(resp);
                    }
                    #[cfg(target_os = "linux")]
                    ServeReply::Shard(mailbox, efd, conn) => {
                        if mailbox.send(ShardDone { conn, resp }).is_ok() {
                            crate::uring::wake(efd);
                        }
                    }
                }
            }
        })
        .expect("failed to spawn the drorb serve thread");
    ready_rx
        .recv()
        .expect("serve thread died before finishing runtime init");
    ServeGateway { tx, pool }
}
