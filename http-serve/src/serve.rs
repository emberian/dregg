//! `serve` — the portable `std`-net HTTP/1.1 serving core.
//!
//! Given a handler `Fn(&ServeRequest) -> WebResponse`, [`serve_http`] binds a `std`
//! [`TcpListener`] and serves each connection on its own thread: it parses one
//! HTTP/1.1 request into a [`ServeRequest`] (method, `Host`, target, body, headers),
//! runs the handler, and writes the response. The HTTP/1.1 connection plumbing
//! (header read, request-line + content-length parse, body read, response write) is
//! written ONCE here.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use crate::http::{HttpMethod, WebResponse};

const MAX_HEADER_BYTES: usize = 64 * 1024;

/// One parsed HTTP/1.1 request the serving core hands to a handler: the parsed
/// method, the `Host` header, the request target, the body, and all headers.
pub struct ServeRequest {
    /// The parsed HTTP method (a request with an unsupported method is answered `405`
    /// before the handler is called, so this is always a method the handler can act on).
    pub method: HttpMethod,
    /// The `Host` header value (empty if absent).
    pub host: String,
    /// The request target (path + query).
    pub target: String,
    /// The request body bytes (read up to `Content-Length`; empty for a bodyless GET).
    pub body: Vec<u8>,
    /// All request header `(name, value)` pairs (name lower-cased), in order — for a
    /// handler that authenticates on a proxy-set header (e.g. `x-dregg-subject`).
    /// Use [`header`](ServeRequest::header), which is duplicate-safe.
    pub headers: Vec<(String, String)>,
}

impl ServeRequest {
    /// The value of header `name` (case-insensitive) IFF it appears EXACTLY ONCE.
    /// Returns `None` for zero or MULTIPLE occurrences — so a client that smuggles a
    /// duplicate identity header (banking on a proxy that appends rather than strips)
    /// gets no value, never the wrong one. The fail-closed default for auth headers.
    pub fn header(&self, name: &str) -> Option<&str> {
        let mut found: Option<&str> = None;
        for (n, v) in &self.headers {
            if n.eq_ignore_ascii_case(name) {
                if found.is_some() {
                    return None; // duplicate — ambiguous, refuse
                }
                found = Some(v.as_str());
            }
        }
        found
    }
}

/// Bind `bind` (e.g. `"127.0.0.1:8080"`) and serve forever — one thread per
/// connection — dispatching each request through `handler`. Returns only on a fatal
/// bind/accept error.
pub fn serve_http<H>(bind: &str, handler: H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static,
{
    let handler = Arc::new(handler);
    let listener = TcpListener::bind(bind)?;
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let handler = Arc::clone(&handler);
                std::thread::spawn(move || {
                    if let Err(e) = serve_http_connection(stream, handler.as_ref()) {
                        eprintln!("http-serve: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("http-serve: accept error: {e}"),
        }
    }
    Ok(())
}

/// Read one HTTP/1.1 request off `stream`, parse it into a [`ServeRequest`], run
/// `handler`, and write the response. Public so a caller (or test) can drive a single
/// connection directly. An unsupported method is answered `405` without calling
/// `handler`; an oversized header block is answered `431`.
pub fn serve_http_connection<H>(mut stream: TcpStream, handler: &H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse,
{
    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > MAX_HEADER_BYTES {
            return write_response(&mut stream, &WebResponse::error(431, "header too large"));
        }
    };

    let header_block = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = header_block.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/").to_string();
    let mut host = String::new();
    let mut content_length = 0usize;
    let mut headers: Vec<(String, String)> = Vec::new();
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let (name, value) = (name.trim(), value.trim());
        if name.eq_ignore_ascii_case("host") {
            host = value.to_string();
        } else if name.eq_ignore_ascii_case("content-length") {
            content_length = value.parse().unwrap_or(0);
        }
        headers.push((name.to_ascii_lowercase(), value.to_string()));
    }

    let Some(method) = HttpMethod::parse(method) else {
        return write_response(
            &mut stream,
            &WebResponse::error(405, format!("unsupported method `{method}`")),
        );
    };

    // Read the body up to Content-Length (already-buffered bytes after the header
    // block first, then more from the socket). A bodyless GET is content_length 0.
    let mut body = buf[header_end..].to_vec();
    while body.len() < content_length {
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&tmp[..n]);
    }
    body.truncate(content_length);

    let req = ServeRequest {
        method,
        host,
        target,
        body,
        headers,
    };
    let resp = handler(&req);
    write_response(&mut stream, &resp)
}

fn write_response(stream: &mut TcpStream, resp: &WebResponse) -> std::io::Result<()> {
    let head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        resp.status,
        reason_phrase(resp.status),
        resp.content_type,
        resp.body.len(),
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(&resp.body)?;
    stream.flush()
}

fn reason_phrase(status: u16) -> &'static str {
    match status {
        200 => "OK",
        400 => "Bad Request",
        401 => "Unauthorized",
        402 => "Payment Required",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        409 => "Conflict",
        431 => "Request Header Fields Too Large",
        500 => "Internal Server Error",
        502 => "Bad Gateway",
        _ => "Status",
    }
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A genuine local TCP round-trip: bind an ephemeral port, serve one connection
    /// in a thread with a trivial echo handler, and prove a real HTTP POST returns
    /// the handler's response — including the `Host` and a duplicate-safe header read.
    #[test]
    fn serves_a_real_tcp_round_trip() {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().unwrap();
        std::thread::spawn(move || {
            if let Ok((stream, _)) = listener.accept() {
                let _ = serve_http_connection(stream, &|req: &ServeRequest| {
                    let subject = req.header("x-dregg-subject").unwrap_or("anon");
                    WebResponse::json(
                        format!("{{\"host\":\"{}\",\"subject\":\"{subject}\"}}", req.host)
                            .into_bytes(),
                    )
                });
            }
        });

        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(
            b"POST /drive HTTP/1.1\r\nHost: alice.agents.dregg\r\nX-Dregg-Subject: dga1_bob\r\nContent-Length: 2\r\nConnection: close\r\n\r\nhi",
        )
        .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 200"), "status line: {resp}");
        assert!(resp.contains("alice.agents.dregg"), "host echoed: {resp}");
        assert!(resp.contains("dga1_bob"), "subject echoed: {resp}");
    }

    /// A smuggled duplicate identity header reads back `None` (fail-closed).
    #[test]
    fn duplicate_header_is_refused() {
        let req = ServeRequest {
            method: HttpMethod::Post,
            host: "h".into(),
            target: "/".into(),
            body: Vec::new(),
            headers: vec![
                ("x-dregg-subject".into(), "alice".into()),
                ("x-dregg-subject".into(), "mallory".into()),
            ],
        };
        assert_eq!(req.header("x-dregg-subject"), None);
    }
}
