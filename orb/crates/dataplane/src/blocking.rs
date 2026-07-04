//! The portable fallback IO path: a thread-per-connection blocking host.
//!
//! Each accepted connection is handled by its own thread (soft-capped), which
//! reads a request off the wire, hands the request bytes to the serve thread
//! over the gateway, waits for the response, and writes it back — all while
//! other connection threads overlap their own reads, writes, and keep-alive idle
//! waits. This is the path used on platforms without io_uring (macOS and
//! others); on Linux the io_uring loop is preferred but this path remains
//! available for comparison.
//!
//! Buffers are pooled: the connection's accumulation buffer, the request buffer
//! handed to the serve thread, and the response buffer handed back all come from
//! and return to the shared [`BufferPool`], so a warm host allocates nothing per
//! request on the Rust side (§ `pool`).

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::time::Duration;

use crate::http::{
    next_request, request_wants_keepalive, response_is_self_delimited, Frame, H2_PREFACE,
};
use crate::pool::PooledBuf;
use crate::serve::ServeGateway;

/// How long a kept-alive connection may sit idle between requests before the
/// host reclaims it.
const IDLE_TIMEOUT: Duration = Duration::from_secs(60);

/// Ceiling on concurrent connection threads. Beyond it, new connections are
/// closed immediately (refused) rather than spawning unbounded threads.
const MAX_CONNS: usize = 1024;

/// One socket read into a pooled accumulation buffer. Returns bytes read
/// (0 = clean EOF).
fn fill(data: &mut Vec<u8>, stream: &mut TcpStream) -> std::io::Result<usize> {
    let mut chunk = [0u8; 16384];
    let n = stream.read(&mut chunk)?;
    data.extend_from_slice(&chunk[..n]);
    Ok(n)
}

/// Handle one accepted connection: the keep-alive loop. Reads a request, routes
/// it through the proven core, writes the response, and loops on the same socket
/// until the client asks to close, the response cannot be kept alive, EOF, an
/// idle timeout, or an error.
fn handle_conn(mut stream: TcpStream, gw: &ServeGateway) {
    use std::io::ErrorKind;

    // Sockets accepted from a non-blocking listener inherit non-blocking mode on
    // BSD/macOS; force this connection back to blocking so the idle read below
    // blocks (up to the read timeout) instead of returning WouldBlock at once.
    let _ = stream.set_nonblocking(false);
    let _ = stream.set_nodelay(true);
    let _ = stream.set_read_timeout(Some(IDLE_TIMEOUT));

    // Pooled accumulation buffer, reused across every request on this
    // connection; a per-connection reply channel, reused across keep-alive
    // requests so no channel is allocated per request.
    let mut acc: PooledBuf = gw.pool().take();
    let (reply_tx, reply_rx) = channel::<PooledBuf>();

    'conn: loop {
        // Peek at the connection opener: an h2c preface is not HTTP/1.1-framed.
        if acc.is_empty() {
            match fill(&mut acc, &mut stream) {
                Ok(0) => return,
                Ok(_) => {}
                Err(e)
                    if e.kind() == ErrorKind::WouldBlock || e.kind() == ErrorKind::TimedOut =>
                {
                    return
                }
                Err(_) => return,
            }
            if acc.len() >= H2_PREFACE.len() && acc.starts_with(H2_PREFACE) {
                // h2c: hand the whole available opening burst to the core once.
                let _ = fill(&mut acc, &mut stream);
                let mut req = gw.pool().take();
                req.extend_from_slice(&acc);
                if let Some(resp) = gw.call(req, &reply_tx, &reply_rx) {
                    let _ = stream.write_all(&resp);
                }
                return;
            }
        }

        // Read exactly one complete request into `acc`.
        let total = loop {
            match next_request(&acc) {
                Frame::Complete(n) => break n,
                Frame::Oversize => return,
                Frame::NeedMore => match fill(&mut acc, &mut stream) {
                    Ok(0) => {
                        // Clean close only on a request boundary (empty buffer).
                        return;
                    }
                    Ok(_) => {}
                    Err(_) => return, // I/O error or idle timeout
                },
            }
        };

        // Move the request bytes into a pooled buffer, then drop them from the
        // accumulation buffer, retaining any pipelined bytes for the next round.
        let mut req = gw.pool().take();
        req.extend_from_slice(&acc[..total]);
        acc.drain(..total);

        let keepalive_req = request_wants_keepalive(&req);

        let resp = match gw.call(req, &reply_tx, &reply_rx) {
            Some(r) => r,
            None => return, // serve thread gone (shutdown)
        };

        let keepalive = keepalive_req && response_is_self_delimited(&resp);
        if stream.write_all(&resp).is_err() {
            return;
        }
        if !keepalive {
            return;
        }
        continue 'conn; // serve the next request (pipelined bytes already buffered)
    }
}

/// Run the blocking accept loop on `listener` until shutdown, driving every
/// request through `gw`.
pub fn run(listener: TcpListener, gw: ServeGateway) {
    // Non-blocking accept so the SIGINT flag is observed promptly.
    listener
        .set_nonblocking(true)
        .expect("failed to set the listener non-blocking");

    let gw = Arc::new(gw);
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping accept loop");
            break;
        }
        match listener.accept() {
            Ok((stream, _peer)) => {
                if crate::ACTIVE_CONNS.load(Ordering::SeqCst) >= MAX_CONNS {
                    drop(stream); // at the soft cap: refuse by closing immediately
                    continue;
                }
                crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
                let gw = Arc::clone(&gw);
                let _ = std::thread::Builder::new()
                    .name("drorb-conn".into())
                    .spawn(move || {
                        handle_conn(stream, &gw);
                        crate::ACTIVE_CONNS.fetch_sub(1, Ordering::SeqCst);
                    });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(_) => {
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}
