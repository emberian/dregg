//! HTTP/1.1 framing. The host reads only what it needs to delimit messages on
//! the byte stream (where a request ends, where the next begins) and to decide
//! whether the connection stays open. It parses no request semantics and
//! rewrites nothing — the meaning of every request is the proven core's job.
//!
//! The framing is IO-agnostic: [`next_request`] inspects an accumulation buffer
//! and reports whether a complete request is present, without knowing how the
//! bytes arrived. Both the blocking thread-per-connection loop and the io_uring
//! loop drive it — one by filling the buffer with blocking reads, the other by
//! appending io_uring recv completions.

/// Cap on a single buffered request (head + body). A request larger than this
/// is refused by closing the connection rather than growing without bound.
pub const REQUEST_CAP: usize = 8 << 20; // 8 MiB

/// The HTTP/2 cleartext (h2c) connection preface. If a connection opens with
/// this, its framing is binary HTTP/2 frames, not CRLF-delimited HTTP/1.1
/// messages; the host hands the whole opening burst to the proven core once
/// (which forks to the H2 engine) and then closes — it does not attempt
/// HTTP/1.1 keep-alive framing on an h2c stream.
pub const H2_PREFACE: &[u8] = b"PRI * HTTP/2.0\r\n";

/// The result of scanning an accumulation buffer for the next complete request.
pub enum Frame {
    /// Not enough bytes yet; read more and rescan.
    NeedMore,
    /// A complete request occupies the first `usize` bytes of the buffer.
    Complete(usize),
    /// The request exceeds [`REQUEST_CAP`]; the connection must be closed.
    Oversize,
}

/// Scan `data` for one complete HTTP/1.1 request (head through CRLFCRLF plus a
/// framed body). Pure: it does no IO and mutates nothing.
pub fn next_request(data: &[u8]) -> Frame {
    // 1. Find the end of the head (CRLFCRLF).
    let head_end = match data.windows(4).position(|w| w == b"\r\n\r\n") {
        Some(p) => p + 4,
        None => {
            return if data.len() > REQUEST_CAP {
                Frame::Oversize
            } else {
                Frame::NeedMore
            };
        }
    };

    // 2. Frame the body.
    match body_frame(&data[..head_end]) {
        BodyFrame::Fixed(n) => {
            let total = head_end + n;
            if total > REQUEST_CAP {
                Frame::Oversize
            } else if data.len() < total {
                Frame::NeedMore
            } else {
                Frame::Complete(total)
            }
        }
        BodyFrame::Chunked => match chunked_len(data, head_end) {
            Some(clen) => {
                let total = head_end + clen;
                if total > REQUEST_CAP {
                    Frame::Oversize
                } else {
                    Frame::Complete(total)
                }
            }
            None => {
                if data.len() > REQUEST_CAP {
                    Frame::Oversize
                } else {
                    Frame::NeedMore
                }
            }
        },
    }
}

/// Where a request's body ends, once the head is in hand.
enum BodyFrame {
    /// Body is exactly `len` bytes (Content-Length, or none → 0).
    Fixed(usize),
    /// Body is chunked; the host must scan chunk framing to find its end.
    Chunked,
}

/// Case-insensitive search for `needle` (lowercase ASCII) in `hay`.
fn find_ci(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || hay.len() < needle.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()]
            .iter()
            .zip(needle)
            .all(|(a, b)| a.to_ascii_lowercase() == *b)
    })
}

/// Read a header value (bytes after `name:` up to CRLF) from a header block.
/// `name` is lowercase and colon-free.
fn header_value<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
    let mut i = 0;
    while i < head.len() {
        let line_end = head[i..]
            .windows(2)
            .position(|w| w == b"\r\n")
            .map(|p| i + p)
            .unwrap_or(head.len());
        let line = &head[i..line_end];
        if let Some(colon) = line.iter().position(|&c| c == b':') {
            let (n, v) = line.split_at(colon);
            if n.len() == name.len()
                && n.iter().zip(name).all(|(a, b)| a.to_ascii_lowercase() == *b)
            {
                let val = &v[1..]; // skip ':'
                let start = val
                    .iter()
                    .position(|&c| c != b' ' && c != b'\t')
                    .unwrap_or(val.len());
                let end = val
                    .iter()
                    .rposition(|&c| c != b' ' && c != b'\t')
                    .map(|p| p + 1)
                    .unwrap_or(start);
                return Some(&val[start..end]);
            }
        }
        i = line_end + 2;
    }
    None
}

/// Given the head bytes (through CRLFCRLF), decide how the body is framed.
fn body_frame(head: &[u8]) -> BodyFrame {
    if let Some(te) = header_value(head, b"transfer-encoding") {
        if find_ci(te, b"chunked").is_some() {
            return BodyFrame::Chunked;
        }
    }
    if let Some(cl) = header_value(head, b"content-length") {
        let s = std::str::from_utf8(cl).ok().map(str::trim).unwrap_or("");
        if let Ok(n) = s.parse::<usize>() {
            return BodyFrame::Fixed(n);
        }
    }
    BodyFrame::Fixed(0)
}

/// Scan chunked body framing starting at `start` in `buf`. Returns the byte
/// length of the whole chunked section (including the terminating 0-chunk and
/// trailers) if it is fully present, or `None` if more bytes are needed.
fn chunked_len(buf: &[u8], start: usize) -> Option<usize> {
    let mut i = start;
    loop {
        // chunk-size line: hex digits up to CRLF (ignore any ;ext).
        let nl = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
        let size_str = std::str::from_utf8(&buf[i..nl]).ok()?;
        let hex = size_str.split(';').next().unwrap_or("").trim();
        let size = usize::from_str_radix(hex, 16).ok()?;
        i = nl + 2; // past the size line's CRLF
        if size == 0 {
            // trailers: header lines until an empty line (CRLF).
            loop {
                let end = buf[i..].windows(2).position(|w| w == b"\r\n")? + i;
                if end == i {
                    return Some(end + 2 - start); // empty line — end of trailers
                }
                i = end + 2;
            }
        }
        i += size; // chunk data
        if i + 2 > buf.len() {
            return None;
        }
        i += 2; // trailing CRLF after chunk data
    }
}

/// Whether the connection should stay open after this request, per HTTP/1.1
/// rules: HTTP/1.1 defaults to keep-alive unless `Connection: close`; HTTP/1.0
/// defaults to close unless `Connection: keep-alive`.
pub fn request_wants_keepalive(head: &[u8]) -> bool {
    let is_11 = find_ci(head, b"http/1.1").is_some();
    match header_value(head, b"connection") {
        Some(v) if find_ci(v, b"close").is_some() => false,
        Some(v) if find_ci(v, b"keep-alive").is_some() => true,
        _ => is_11,
    }
}

/// Whether the *response* is self-delimiting (has Content-Length or is chunked).
/// A response with neither is delimited by connection close, so keep-alive is
/// impossible and the host must close after writing it. Reads response framing
/// headers only; never rewrites the response.
pub fn response_is_self_delimited(resp: &[u8]) -> bool {
    let head_end = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(resp.len());
    let head = &resp[..head_end];
    header_value(head, b"content-length").is_some()
        || header_value(head, b"transfer-encoding")
            .map(|te| find_ci(te, b"chunked").is_some())
            .unwrap_or(false)
}
