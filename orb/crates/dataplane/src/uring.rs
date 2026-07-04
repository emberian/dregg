//! The high-performance Linux IO path: an io_uring accept/recv/send event loop.
//!
//! This is the preferred IO path on Linux. It replaces the thread-per-connection
//! blocking model with a small number of **shards** — one event-loop thread per
//! core — each driving its own `io_uring` instance over its own connection set.
//! Accept, receive and send are submitted as SQEs and reaped as CQEs in batches;
//! a shard thread never blocks on a single connection, so one thread services
//! thousands of connections. This is the share-nothing model of a Cloudflare-tier
//! reactor: no connection state, buffer, or slab is shared between shards.
//!
//! ## The one shared resource, and where the ceiling is
//!
//! The proven core is a pure `ByteArray -> ByteArray` transform, so shards need
//! no shared mutable engine state to run it — but the Lean runtime is a
//! process-global singleton, so there is exactly one runtime-owner thread (see
//! `serve`). Every shard hands its completed requests to that one thread over
//! the gateway channel and is woken with the response through its own eventfd.
//! The IO fabric (accept/recv/send, framing) scales across all shard cores; the
//! serve transform does not. The steady-state ceiling is therefore
//! `1 / (serve latency)` regardless of shard count — the honest bottleneck,
//! measured in the perf report, not papered over.
//!
//! ## Copy discipline
//!
//! This loop uses ordinary pooled receive buffers, not a provided-buffer ring
//! (`buf_ring`). At this seam that costs nothing over zero-copy: `drorb_serve`
//! consumes an **owned** `ByteArray`, so the request bytes are copied into the
//! runtime's input array no matter how they were received — the copy-once
//! discipline is intrinsic to the proven ABI. A provided-buffer ring only pays
//! off for a parser that reads in place across the recv buffer; the proven core
//! does not, so a straightforward submit/complete loop with pooled buffers is
//! the right first rung. (buf_ring parse-in-place is the named successor for a
//! future in-host parser that holds the lease across the parse.)

use std::os::fd::RawFd;
use std::sync::atomic::Ordering;
use std::sync::mpsc::{channel, Receiver, Sender};

use io_uring::{opcode, squeue, types, IoUring};

use crate::http::{
    next_request, request_wants_keepalive, response_is_self_delimited, Frame, H2_PREFACE,
};
use crate::pool::PooledBuf;
use crate::serve::{ServeGateway, ServeReply, ShardDone};

/// Bytes offered to the kernel per receive.
const RECV_CHUNK: usize = 16384;
/// SQ/CQ depth per shard.
const RING_ENTRIES: u32 = 4096;
/// Cap on live connections per shard; new accepts beyond it are closed.
const MAX_CONNS_PER_SHARD: usize = 16384;

// user_data tag space: high 32 bits classify the op, low 32 carry the slot.
const TAG_ACCEPT: u64 = 1 << 32;
const TAG_EVENTFD: u64 = 2 << 32;
const TAG_RECV: u64 = 3 << 32;
const TAG_SEND: u64 = 4 << 32;
const TAG_CLOSE: u64 = 5 << 32;
const TAG_MASK: u64 = 0xffff_ffff << 32;
const SLOT_MASK: u64 = 0xffff_ffff;

/// Signal a shard that a serve response is waiting in its mailbox, by writing to
/// its eventfd. Called from the serve thread.
pub fn wake(efd: RawFd) {
    let one: u64 = 1;
    // SAFETY: an 8-byte write to an eventfd is the documented wakeup; `efd` is a
    // live eventfd owned by the target shard for the process lifetime, and
    // `&one` is a valid 8-byte source. The write cannot block (the counter only
    // saturates near u64::MAX, far beyond in-flight wakeups).
    unsafe {
        libc::write(efd, &one as *const u64 as *const libc::c_void, 8);
    }
}

/// Per-connection state owned by a single shard. No field is shared across
/// shards; a `Conn` and its buffers live and die on one shard thread.
struct Conn {
    fd: RawFd,
    /// Accumulation buffer: recv completions extend it; framing consumes it.
    acc: PooledBuf,
    /// Response being written, and how many of its bytes are already out.
    resp: Option<PooledBuf>,
    sent: usize,
    /// The in-flight request's keep-alive intent (HTTP/1.1 framing).
    req_keepalive: bool,
    /// Whether this connection stays open after the in-flight response — the
    /// request's intent AND the response being self-delimited.
    keepalive: bool,
    /// h2c connections are served once then closed (no HTTP/1.1 keep-alive).
    h2c: bool,
}

/// A free-list slab of connections (the `PendingSlab` shape: O(1)
/// insert/remove, slot reuse). One per shard.
struct Slab {
    conns: Vec<Option<Conn>>,
    free: Vec<u32>,
}

impl Slab {
    fn new() -> Self {
        Slab {
            conns: Vec::new(),
            free: Vec::new(),
        }
    }
    fn live(&self) -> usize {
        self.conns.len() - self.free.len()
    }
    fn insert(&mut self, c: Conn) -> u32 {
        if let Some(i) = self.free.pop() {
            self.conns[i as usize] = Some(c);
            i
        } else {
            let i = self.conns.len() as u32;
            self.conns.push(Some(c));
            i
        }
    }
    fn get(&mut self, i: u32) -> Option<&mut Conn> {
        self.conns.get_mut(i as usize).and_then(|s| s.as_mut())
    }
    fn remove(&mut self, i: u32) {
        if let Some(slot) = self.conns.get_mut(i as usize) {
            if slot.take().is_some() {
                self.free.push(i);
            }
        }
    }
}

/// Run `shards` io_uring shard threads over `listener_fd`, driving every request
/// through `gw`. Blocks until every shard exits (on shutdown).
pub fn run(listener_fd: RawFd, gw: ServeGateway, shards: usize) {
    let mut handles = Vec::new();
    for id in 0..shards {
        let gw = gw.clone();
        handles.push(
            std::thread::Builder::new()
                .name(format!("drorb-shard-{id}"))
                .spawn(move || {
                    if let Err(e) = shard_loop(listener_fd, gw) {
                        eprintln!("dataplane: shard {id} exited: {e}");
                    }
                })
                .expect("failed to spawn io_uring shard"),
        );
    }
    for h in handles {
        let _ = h.join();
    }
}

/// Everything a shard threads through its completion handlers.
struct Shard {
    gw: ServeGateway,
    efd: RawFd,
    mtx: Sender<ShardDone>,
    slab: Slab,
    backlog: Vec<squeue::Entry>,
}

/// One shard: its own ring, eventfd, connection slab, and serve mailbox.
fn shard_loop(listener_fd: RawFd, gw: ServeGateway) -> std::io::Result<()> {
    let mut ring: IoUring = IoUring::new(RING_ENTRIES)?;

    // eventfd for serve-completion wakeups from the runtime-owner thread.
    // SAFETY: eventfd(2) with a zero initial count and valid flags; the returned
    // fd is checked and owned by this shard until the process exits.
    let efd = unsafe { libc::eventfd(0, libc::EFD_CLOEXEC | libc::EFD_NONBLOCK) };
    if efd < 0 {
        return Err(std::io::Error::last_os_error());
    }

    let (mtx, mrx): (Sender<ShardDone>, Receiver<ShardDone>) = channel();
    let mut sh = Shard {
        gw,
        efd,
        mtx,
        slab: Slab::new(),
        backlog: Vec::new(),
    };
    // Stable 8-byte target for the eventfd read; its address must outlive each
    // in-flight read op, so the loop owns it for its whole lifetime.
    let mut efd_buf: u64 = 0;

    // Prime the ring: one accept on the shared listener, one eventfd read.
    sh.backlog.push(accept_sqe(listener_fd));
    sh.backlog.push(eventfd_sqe(efd, &mut efd_buf));

    loop {
        flush(&mut ring, &mut sh.backlog)?;
        match ring.submit_and_wait(1) {
            Ok(_) => {}
            Err(ref e) if e.raw_os_error() == Some(libc::EINTR) => {
                if crate::SHUTDOWN.load(Ordering::SeqCst) {
                    return Ok(());
                }
                continue;
            }
            Err(e) => return Err(e),
        }

        // Reap this batch. Copy out (user_data, result) so the completion borrow
        // is released before we push new SQEs.
        let batch: Vec<(u64, i32)> = ring
            .completion()
            .map(|c| (c.user_data(), c.result()))
            .collect();

        for (ud, res) in batch {
            let slot = (ud & SLOT_MASK) as u32;
            match ud & TAG_MASK {
                TAG_ACCEPT => on_accept(&mut sh, res, listener_fd),
                TAG_EVENTFD => on_wakeup(&mut sh, &mrx, &mut efd_buf),
                TAG_RECV => on_recv(&mut sh, slot, res),
                TAG_SEND => on_send(&mut sh, slot, res),
                TAG_CLOSE => {} // fire-and-forget; the slot was freed at submit time
                _ => {}
            }
        }

        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return Ok(());
        }
    }
}

// --- SQE builders ---------------------------------------------------------

fn accept_sqe(listener_fd: RawFd) -> squeue::Entry {
    opcode::Accept::new(types::Fd(listener_fd), std::ptr::null_mut(), std::ptr::null_mut())
        .build()
        .user_data(TAG_ACCEPT)
}

fn eventfd_sqe(efd: RawFd, buf: &mut u64) -> squeue::Entry {
    opcode::Read::new(types::Fd(efd), buf as *mut u64 as *mut u8, 8)
        .build()
        .user_data(TAG_EVENTFD)
}

/// Reserve receive space at the tail of `conn.acc` and build a recv SQE that
/// fills it. The pointer is into `acc`'s heap allocation, which is stable across
/// slab moves (the `Vec` control block may move; the allocation it points to
/// does not), so the in-flight op stays valid until its completion.
fn recv_sqe(conn: &mut Conn, slot: u32) -> squeue::Entry {
    conn.acc.reserve(RECV_CHUNK);
    let len = conn.acc.len();
    // SAFETY: `reserve` guaranteed capacity for RECV_CHUNK bytes past `len`; the
    // pointer is valid for that many bytes and the kernel initializes them.
    let ptr = unsafe { conn.acc.as_mut_ptr().add(len) };
    opcode::Recv::new(types::Fd(conn.fd), ptr, RECV_CHUNK as u32)
        .build()
        .user_data(TAG_RECV | slot as u64)
}

fn send_sqe(conn: &Conn, slot: u32) -> squeue::Entry {
    let resp = conn.resp.as_ref().expect("send with no response staged");
    let ptr = resp[conn.sent..].as_ptr();
    let len = (resp.len() - conn.sent) as u32;
    opcode::Send::new(types::Fd(conn.fd), ptr, len)
        .build()
        .user_data(TAG_SEND | slot as u64)
}

fn close_sqe(fd: RawFd) -> squeue::Entry {
    opcode::Close::new(types::Fd(fd)).build().user_data(TAG_CLOSE)
}

// --- completion handlers --------------------------------------------------

fn on_accept(sh: &mut Shard, res: i32, listener_fd: RawFd) {
    // Always re-arm accept so the shard keeps taking new connections.
    sh.backlog.push(accept_sqe(listener_fd));
    if res < 0 {
        return; // transient accept error (e.g. EMFILE); the re-arm retries
    }
    let fd = res as RawFd;
    if sh.slab.live() >= MAX_CONNS_PER_SHARD {
        sh.backlog.push(close_sqe(fd)); // at the shard cap: refuse
        return;
    }
    let conn = Conn {
        fd,
        acc: sh.gw.pool().take(),
        resp: None,
        sent: 0,
        req_keepalive: false,
        keepalive: false,
        h2c: false,
    };
    let slot = sh.slab.insert(conn);
    let sqe = recv_sqe(sh.slab.get(slot).unwrap(), slot);
    sh.backlog.push(sqe);
}

fn on_wakeup(sh: &mut Shard, mrx: &Receiver<ShardDone>, efd_buf: &mut u64) {
    // Drain every completed response (coalesced eventfd counts may batch them).
    while let Ok(done) = mrx.try_recv() {
        if let Some(conn) = sh.slab.get(done.conn) {
            conn.keepalive =
                !conn.h2c && conn.req_keepalive && response_is_self_delimited(&done.resp);
            conn.resp = Some(done.resp);
            conn.sent = 0;
            let sqe = send_sqe(conn, done.conn);
            sh.backlog.push(sqe);
        }
        // else: connection already gone; drop the response (returns to pool).
    }
    sh.backlog.push(eventfd_sqe(sh.efd, efd_buf));
}

fn on_recv(sh: &mut Shard, slot: u32, res: i32) {
    let n = match res {
        n if n > 0 => n as usize,
        _ => return close(sh, slot), // 0 = EOF, <0 = error
    };
    {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        // SAFETY: the kernel wrote `n` bytes into the reserved tail region of
        // `acc` (see `recv_sqe`); extending the logical length to cover the
        // now-initialized bytes is sound.
        let new_len = conn.acc.len() + n;
        unsafe { conn.acc.set_len(new_len) };
    }
    dispatch_or_read(sh, slot);
}

/// Try to extract one complete request from `conn.acc` and hand it to the serve
/// gateway; if the request is not yet complete, arm another recv.
fn dispatch_or_read(sh: &mut Shard, slot: u32) {
    let conn = match sh.slab.get(slot) {
        Some(c) => c,
        None => return,
    };

    // h2c preface: not HTTP/1.1-framed. Wait for the full preface, then hand the
    // whole opening burst to the core once and close after the response.
    if !conn.h2c && conn.acc.len() < H2_PREFACE.len() && H2_PREFACE.starts_with(&conn.acc) {
        let sqe = recv_sqe(conn, slot);
        sh.backlog.push(sqe);
        return;
    }
    if !conn.h2c && conn.acc.starts_with(H2_PREFACE) {
        conn.h2c = true;
        conn.req_keepalive = false;
        let mut req = sh.gw.pool().take();
        req.extend_from_slice(&conn.acc);
        conn.acc.clear();
        let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
        if !sh.gw.submit(req, reply) {
            close(sh, slot);
        }
        return;
    }

    match next_request(&conn.acc) {
        Frame::Complete(total) => {
            let mut req = sh.gw.pool().take();
            req.extend_from_slice(&conn.acc[..total]);
            conn.acc.drain(..total);
            conn.req_keepalive = request_wants_keepalive(&req);
            let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
            if !sh.gw.submit(req, reply) {
                close(sh, slot);
            }
        }
        Frame::NeedMore => {
            let sqe = recv_sqe(conn, slot);
            sh.backlog.push(sqe);
        }
        Frame::Oversize => close(sh, slot),
    }
}

fn on_send(sh: &mut Shard, slot: u32, res: i32) {
    if res <= 0 {
        return close(sh, slot);
    }
    let finished = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        conn.sent += res as usize;
        let total = conn.resp.as_ref().map(|r| r.len()).unwrap_or(0);
        if conn.sent < total {
            // Short write: send the remainder.
            let sqe = send_sqe(conn, slot);
            sh.backlog.push(sqe);
            return;
        }
        // Whole response written; release it (returns to the pool).
        conn.resp = None;
        conn.sent = 0;
        conn.keepalive
    };
    if finished {
        dispatch_or_read(sh, slot);
    } else {
        close(sh, slot);
    }
}

fn close(sh: &mut Shard, slot: u32) {
    if let Some(conn) = sh.slab.get(slot) {
        let fd = conn.fd;
        sh.backlog.push(close_sqe(fd));
    }
    sh.slab.remove(slot); // drops the Conn: acc/resp buffers return to the pool
}

// --- submission plumbing --------------------------------------------------

/// Move every backlogged SQE into the submission queue, submitting to the kernel
/// to free slots whenever the queue fills.
fn flush(ring: &mut IoUring, backlog: &mut Vec<squeue::Entry>) -> std::io::Result<()> {
    while !backlog.is_empty() {
        let mut pushed = 0;
        {
            let mut sq = ring.submission();
            for e in backlog.iter() {
                // SAFETY: each `e` describes a valid op whose referenced buffers
                // (recv tail of `acc`, `resp` slice, `efd_buf`) outlive the op —
                // they live in the slab / loop until the matching completion.
                if unsafe { sq.push(e) }.is_err() {
                    break; // SQ full
                }
                pushed += 1;
            }
        }
        backlog.drain(..pushed);
        if pushed == 0 {
            // SQ full and nothing drained: submit to free slots, then retry.
            ring.submit()?;
        }
    }
    Ok(())
}
