//! The minimal HTTP request/response vocabulary a served app handler speaks.
//!
//! These are deliberately small, server-independent value types: a [`WebRequest`]
//! (method, path, parsed query, body) and a [`WebResponse`] (status, content-type,
//! body). Keeping them independent of any HTTP server is what lets the same handler
//! run under the portable [`serve_http`](crate::serve::serve_http) loop (std TCP,
//! cross-platform) and, later, under any other serving engine.

use std::collections::BTreeMap;

/// An HTTP method, the subset the router classifies on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Patch,
    Head,
    Options,
}

impl HttpMethod {
    /// Parse a method token (case-insensitive); unknown methods are `None`.
    pub fn parse(s: &str) -> Option<HttpMethod> {
        Some(match s.to_ascii_uppercase().as_str() {
            "GET" => HttpMethod::Get,
            "POST" => HttpMethod::Post,
            "PUT" => HttpMethod::Put,
            "DELETE" => HttpMethod::Delete,
            "PATCH" => HttpMethod::Patch,
            "HEAD" => HttpMethod::Head,
            "OPTIONS" => HttpMethod::Options,
            _ => return None,
        })
    }

    /// The canonical uppercase token.
    pub const fn as_str(self) -> &'static str {
        match self {
            HttpMethod::Get => "GET",
            HttpMethod::Post => "POST",
            HttpMethod::Put => "PUT",
            HttpMethod::Delete => "DELETE",
            HttpMethod::Patch => "PATCH",
            HttpMethod::Head => "HEAD",
            HttpMethod::Options => "OPTIONS",
        }
    }
}

impl std::fmt::Display for HttpMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One inbound request to a served app.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WebRequest {
    /// The request method.
    pub method: HttpMethod,
    /// The request path (no query string), e.g. `/add`.
    pub path: String,
    /// The parsed, percent-decoded query parameters (`?a=40&b=2` → `{a:40, b:2}`).
    pub query: BTreeMap<String, String>,
    /// The raw request body.
    pub body: Vec<u8>,
}

impl WebRequest {
    /// Build a request from a method and a raw request target (`path[?query]`),
    /// splitting + percent-decoding the query string.
    pub fn new(method: HttpMethod, target: &str, body: Vec<u8>) -> WebRequest {
        let (path, query_str) = match target.split_once('?') {
            Some((p, q)) => (p, q),
            None => (target, ""),
        };
        WebRequest {
            method,
            path: path.to_string(),
            query: parse_query(query_str),
            body,
        }
    }

    /// A `GET path` with no body (the common read request).
    pub fn get(target: &str) -> WebRequest {
        WebRequest::new(HttpMethod::Get, target, Vec::new())
    }
}

/// One response a served app returns.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WebResponse {
    /// The HTTP status code.
    pub status: u16,
    /// The `Content-Type` header value.
    pub content_type: String,
    /// The response body.
    pub body: Vec<u8>,
}

impl WebResponse {
    /// A `200 OK` text/plain response.
    pub fn text(body: impl Into<String>) -> WebResponse {
        WebResponse {
            status: 200,
            content_type: "text/plain; charset=utf-8".to_string(),
            body: body.into().into_bytes(),
        }
    }

    /// A `200 OK` application/json response from raw JSON bytes.
    pub fn json(body: impl Into<Vec<u8>>) -> WebResponse {
        WebResponse {
            status: 200,
            content_type: "application/json".to_string(),
            body: body.into(),
        }
    }

    /// An error response (`status`) with a JSON `{"error": msg}` body.
    pub fn error(status: u16, msg: impl Into<String>) -> WebResponse {
        let msg = msg.into();
        let body = serde_json::json!({ "error": msg }).to_string().into_bytes();
        WebResponse {
            status,
            content_type: "application/json".to_string(),
            body,
        }
    }

    /// The body as a UTF-8 string (lossy), for tests + logging.
    pub fn body_str(&self) -> std::borrow::Cow<'_, str> {
        String::from_utf8_lossy(&self.body)
    }
}

/// Parse + percent-decode an `a=1&b=two` query string into a map. Last value
/// wins on a repeated key; a bare `k` (no `=`) maps to the empty string.
fn parse_query(q: &str) -> BTreeMap<String, String> {
    let mut map = BTreeMap::new();
    for pair in q.split('&').filter(|s| !s.is_empty()) {
        let (k, v) = match pair.split_once('=') {
            Some((k, v)) => (k, v),
            None => (pair, ""),
        };
        map.insert(percent_decode(k), percent_decode(v));
    }
    map
}

/// Decode `%XX` escapes and `+` (form-encoded space) in a query token. Invalid
/// escapes are left verbatim.
fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b'%' if i + 2 < bytes.len() => {
                let hi = (bytes[i + 1] as char).to_digit(16);
                let lo = (bytes[i + 2] as char).to_digit(16);
                if let (Some(hi), Some(lo)) = (hi, lo) {
                    out.push((hi * 16 + lo) as u8);
                    i += 3;
                } else {
                    out.push(bytes[i]);
                    i += 1;
                }
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_method_path_and_query() {
        let r = WebRequest::get("/add?a=40&b=2");
        assert_eq!(r.method, HttpMethod::Get);
        assert_eq!(r.path, "/add");
        assert_eq!(r.query.get("a").map(String::as_str), Some("40"));
        assert_eq!(r.query.get("b").map(String::as_str), Some("2"));
    }

    #[test]
    fn no_query_is_empty_map() {
        let r = WebRequest::get("/hello");
        assert_eq!(r.path, "/hello");
        assert!(r.query.is_empty());
    }

    #[test]
    fn percent_and_plus_decode() {
        let r = WebRequest::get("/q?msg=hello+world%21");
        assert_eq!(r.query.get("msg").map(String::as_str), Some("hello world!"));
    }

    #[test]
    fn method_round_trips() {
        assert_eq!(HttpMethod::parse("post"), Some(HttpMethod::Post));
        assert_eq!(HttpMethod::parse("GET").unwrap().as_str(), "GET");
        assert_eq!(HttpMethod::parse("teleport"), None);
    }
}
