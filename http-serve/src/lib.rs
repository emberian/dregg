//! # http-serve — a tiny, server-independent HTTP/1.1 vocabulary + serve loop.
//!
//! Two small pieces:
//!
//! - [`http`] — the value types: [`HttpMethod`], [`WebRequest`], [`WebResponse`].
//!   Deliberately server-independent, so the same handler runs anywhere.
//! - [`serve`] — the portable `std`-net serving core: [`ServeRequest`] (one parsed
//!   HTTP/1.1 request with its `Host` and headers) and [`serve_http`] /
//!   [`serve_http_connection`], a one-thread-per-connection loop that dispatches
//!   each request through a `Fn(&ServeRequest) -> WebResponse` handler.
//!
//! No async runtime, no framework, no external HTTP crate — the minimal surface a
//! cap-gated app handler drives. This is the substrate HTTP-serve surface the
//! hosting platform's `serve` layer binds to.

pub mod http;
pub mod serve;

pub use http::{HttpMethod, WebRequest, WebResponse};
pub use serve::{serve_http, serve_http_connection, ServeRequest};
