//! The native dataplane: a real keep-alive, concurrent HTTP/1.1 host whose
//! request-handling core is the leanc-compiled proven serve.
//!
//! Every crossing of the boundary is one call to the exported `drorb_serve`
//! (`ByteArray -> ByteArray`), the same proven pipeline the shipped binaries
//! run. This host owns the sockets, the accept loop, and the connection
//! lifecycle; it never rewrites a request or a response. The bytes read off the
//! wire go in unchanged and the proven response bytes go back out unchanged. The
//! host reads only HTTP/1.1 *framing* metadata — message length and connection
//! disposition — so it knows where one request ends and the next begins and
//! whether to keep the connection open. The meaning of every request is decided
//! solely by the proven core.
//!
//! ## Structure
//!
//! - `serve`    — the Lean seam: boot the runtime and cross it, on one owner
//!                thread; the gateway other threads use to reach it.
//! - `pool`     — a fixed pool of reusable byte buffers; zero steady-state
//!                host-side allocation on the request hot path.
//! - `http`     — IO-agnostic HTTP/1.1 framing shared by both IO paths.
//! - `uring`    — the high-performance Linux IO path: per-core io_uring shards
//!                (preferred on Linux).
//! - `blocking` — the portable thread-per-connection fallback (macOS and other
//!                platforms; also selectable on Linux for comparison).

use std::net::{TcpListener, ToSocketAddrs};
use std::sync::atomic::{AtomicBool, AtomicUsize};

mod blocking;
mod http;
mod pool;
mod serve;
#[cfg(target_os = "linux")]
mod uring;

/// Set once a SIGINT is received; the IO paths observe it and stop.
pub static SHUTDOWN: AtomicBool = AtomicBool::new(false);

/// Count of connection threads currently in flight, for the blocking path's
/// soft cap.
pub static ACTIVE_CONNS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn on_sigint(_sig: i32) {
    SHUTDOWN.store(true, std::sync::atomic::Ordering::SeqCst);
}

unsafe extern "C" {
    fn signal(signum: i32, handler: usize) -> usize;
}

const SIGINT: i32 = 2;

/// Which IO path to run.
#[derive(Clone, Copy, PartialEq)]
enum IoMode {
    /// io_uring on Linux, blocking elsewhere.
    Auto,
    /// Force the blocking thread-per-connection path.
    Blocking,
    /// Force the io_uring path (Linux only).
    Uring,
}

struct Config {
    bind: String,
    io: IoMode,
    /// io_uring shard count — read only by the Linux io_uring path.
    #[cfg_attr(not(target_os = "linux"), allow(dead_code))]
    shards: usize,
}

fn usage() {
    eprintln!(
        "\
drorb dataplane — a keep-alive, concurrent HTTP/1.1 host driving the
leanc-compiled proven serve.

USAGE:
    dataplane [ADDR]
    dataplane --bind ADDR [--io auto|blocking|uring] [--shards N]
    dataplane --help

ADDR is HOST:PORT (e.g. 127.0.0.1:8080 or 0.0.0.0:443) or a bare PORT
(e.g. 8080), which binds 127.0.0.1. If omitted, the DRORB_BIND environment
variable is used, else 127.0.0.1:8080.

--io selects the IO path: 'auto' (io_uring on Linux, blocking elsewhere),
'blocking' (thread-per-connection), or 'uring' (Linux io_uring). Overridable
via DRORB_IO. --shards sets the io_uring shard count (default: CPU count),
overridable via DRORB_SHARDS.

Every request is answered by the proven `drorb_serve` core; the host owns only
the sockets, the accept loop, and HTTP/1.1 framing. SIGINT stops it."
    );
}

/// Normalize an ADDR argument: a bare port binds 127.0.0.1; HOST:PORT is used
/// verbatim.
fn normalize_addr(a: &str) -> String {
    if a.parse::<u16>().is_ok() {
        format!("127.0.0.1:{a}")
    } else {
        a.to_string()
    }
}

fn parse_io(s: &str) -> IoMode {
    match s {
        "auto" => IoMode::Auto,
        "blocking" => IoMode::Blocking,
        "uring" => IoMode::Uring,
        other => {
            eprintln!("dataplane: unknown --io mode {other} (want auto|blocking|uring)");
            std::process::exit(2);
        }
    }
}

fn default_shards() -> usize {
    std::env::var("DRORB_SHARDS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        })
}

fn parse_config() -> Config {
    let mut args = std::env::args().skip(1);
    let mut bind: Option<String> = None;
    let mut io: Option<IoMode> = None;
    let mut shards: Option<usize> = None;
    while let Some(a) = args.next() {
        match a.as_str() {
            "-h" | "--help" => {
                usage();
                std::process::exit(0);
            }
            "--bind" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --bind needs an ADDR argument");
                    std::process::exit(2);
                });
                bind = Some(normalize_addr(&v));
            }
            "--io" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --io needs a mode argument");
                    std::process::exit(2);
                });
                io = Some(parse_io(&v));
            }
            "--shards" => {
                let v = args.next().unwrap_or_else(|| {
                    eprintln!("dataplane: --shards needs a count argument");
                    std::process::exit(2);
                });
                shards = Some(v.parse().unwrap_or_else(|_| {
                    eprintln!("dataplane: --shards wants a positive integer");
                    std::process::exit(2);
                }));
            }
            other if other.starts_with('-') => {
                eprintln!("dataplane: unknown option {other}");
                usage();
                std::process::exit(2);
            }
            other => bind = Some(normalize_addr(other)),
        }
    }
    let bind = bind
        .or_else(|| std::env::var("DRORB_BIND").ok().map(|v| normalize_addr(&v)))
        .unwrap_or_else(|| "127.0.0.1:8080".to_string());
    let io = io
        .or_else(|| std::env::var("DRORB_IO").ok().map(|v| parse_io(&v)))
        .unwrap_or(IoMode::Auto);
    let shards = shards.unwrap_or_else(default_shards).max(1);
    Config { bind, io, shards }
}

fn bind_listener(bind: &str) -> TcpListener {
    let addrs: Vec<_> = match bind.to_socket_addrs() {
        Ok(a) => a.collect(),
        Err(e) => {
            eprintln!("dataplane: cannot resolve bind address {bind}: {e}");
            std::process::exit(1);
        }
    };
    TcpListener::bind(&addrs[..]).unwrap_or_else(|e| {
        eprintln!("dataplane: bind {bind} failed: {e}");
        std::process::exit(1);
    })
}

fn main() {
    let cfg = parse_config();

    // Install the SIGINT handler before we bring anything up.
    // SAFETY: `on_sigint` is an `extern "C"` handler that only stores into an
    // atomic — async-signal-safe; installing it before any work is standard.
    unsafe { signal(SIGINT, on_sigint as *const () as usize) };

    // The shared buffer pool: request/response buffers up to a typical head+small
    // body reserve; retain a generous warm set so a burst does not thrash.
    let pool = pool::BufferPool::new(16 << 10, 4096);

    // Bring up the runtime on its dedicated owner thread; the gateway routes
    // every request there. Blocks until the runtime is up.
    let gw = serve::spawn_serve_thread(pool);

    let listener = bind_listener(&cfg.bind);
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| cfg.bind.clone());

    // Choose the IO path. io_uring is preferred on Linux; the blocking path is
    // the portable fallback and is also selectable on Linux for comparison.
    let use_uring = match cfg.io {
        IoMode::Auto => cfg!(target_os = "linux"),
        IoMode::Blocking => false,
        IoMode::Uring => {
            if !cfg!(target_os = "linux") {
                eprintln!("dataplane: --io uring requires Linux; falling back to blocking");
                false
            } else {
                true
            }
        }
    };

    #[cfg(target_os = "linux")]
    if use_uring {
        use std::os::fd::AsRawFd;
        eprintln!(
            "dataplane: listening on {local} (io_uring, {} shards, over the leanc-compiled proven serve; SIGINT to stop)",
            cfg.shards
        );
        let fd = listener.as_raw_fd();
        let gw2 = gw.clone();
        // Watch for SIGINT and exit promptly; the shards block in the ring.
        std::thread::spawn(watch_shutdown);
        uring::run(fd, gw2, cfg.shards);
        drop(listener);
        std::process::exit(0);
    }

    let _ = use_uring; // (non-Linux: always the blocking path)
    eprintln!(
        "dataplane: listening on {local} (keep-alive HTTP/1.1, blocking thread-per-connection, over the leanc-compiled proven serve; SIGINT to stop)"
    );
    blocking::run(listener, gw);
    std::process::exit(0);
}

/// Watch the shutdown flag and exit the process once set. Used by the io_uring
/// path, whose shards block inside the ring and are torn down with the process.
#[cfg(target_os = "linux")]
fn watch_shutdown() {
    use std::sync::atomic::Ordering;
    loop {
        if SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping");
            std::process::exit(0);
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
}
