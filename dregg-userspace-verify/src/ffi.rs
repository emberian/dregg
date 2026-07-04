//! C-ABI FFI surface for TS / Python (and any other) bindings — a single
//! `json → json` entry over the C boundary.
//!
//! The whole toolkit is *pure, total, dependency-light* (it reads a value, runs
//! arithmetic, returns a verdict — no I/O, no executor, no Lean link), so the
//! cross-language binding is the thinnest possible shim: marshal a JSON request
//! in, marshal a JSON response out. A TS or Python caller serializes a
//! [`CallForest`] (the SDK already round-trips it through `serde`), hands the
//! bytes to [`uverify_analyze`], and deserializes the [`crate::Assurance`] (plus
//! the app-level findings) back. No bespoke struct marshalling, no ABI churn
//! when a check is added — the wire is JSON and the schema is `serde`.
//!
//! ## The settled wire shape
//!
//! **Request** (`json_ptr` / `len` → UTF-8 JSON):
//!
//! ```json
//! {
//!   "forest": { ...a serde-serialized dregg_turn::CallForest... },
//!   "treat_as_ring": false,
//!   "app": {                          // OPTIONAL — opt into app-level checks
//!     "escrow":     { "cell": "<hex32>", "escrowed_slot": 5, "released_slot": 7,
//!                     "refunded_slot": 8, "prior_escrowed": null },
//!     "bounty":     { "cell": "<hex32>", "state_slot": 4, "ladder": [1,2,3,4],
//!                     "prior_state": null },
//!     "provenance": { "cell": "<hex32>", "entry_base": 4,
//!                     "claims": ["<hex32>", ...],
//!                     "prior_committed": ["<hex32>", ...] },
//!     "exposure":   { "cell": "<hex32>", "reserve_slot": 6,
//!                     "prior_reserve": null }
//!   }
//! }
//! ```
//!
//! **Response** (a NUL-terminated UTF-8 JSON C string the caller must free with
//! [`uverify_free`]):
//!
//! ```json
//! {
//!   "ok": true,
//!   "pass": true,
//!   "assurance": { "conservation": "Pass", "no_amplification": "Pass",
//!                  "wellformed": "Pass", "ring_balance": "Pass",
//!                  "exposure": "Pass" },
//!   "app_findings": [ { "guarantee": "...", "locus": {...}, "message": "..." } ],
//!   "error": null
//! }
//! ```
//!
//! The `exposure` sub-request populates `assurance.exposure` (the `≤` ceiling
//! `Σ provisional-exposure ≤ reserve`); when it is omitted that field is `Pass`
//! (vacuously — no reserve to exceed), exactly as `ring_balance` is without
//! `treat_as_ring`.
//!
//! On a malformed request (bad UTF-8, bad JSON, an `app.*.cell` that is not
//! 32-byte hex) the response is `{ "ok": false, "pass": false, "error":
//! "<reason>", ... }` — errors are reported *in band* (a valid JSON string with
//! `ok: false`), never as a null pointer, so every binding has one code path.
//! A null/empty input is the sole exception that returns a null pointer.
//!
//! ## Building the cdylib
//!
//! `dregg-userspace-verify` declares `crate-type = ["cdylib", "rlib"]`, so
//! `cargo build -p dregg-userspace-verify` produces both `libdregg_userspace_
//! verify.{so,dylib,dll}` (the C-ABI shared object the TS/Py FFI loads) and the
//! `rlib` (for in-tree Rust callers, e.g. the SDK's `analyze()` sugar and this
//! crate's own tests). The FFI symbols are `uverify_analyze` and `uverify_free`.

use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_uchar};

use dregg_turn::CallForest;
use dregg_types::CellId;

use crate::app;

/// The request envelope the binding sends (see the module wire shape).
#[derive(serde::Deserialize)]
struct Request {
    forest: CallForest,
    #[serde(default)]
    treat_as_ring: bool,
    #[serde(default)]
    app: Option<AppRequest>,
}

/// The optional app-level-check selector. Each present field runs the
/// corresponding app check and folds its findings into `app_findings`.
#[derive(serde::Deserialize)]
struct AppRequest {
    #[serde(default)]
    escrow: Option<EscrowReq>,
    #[serde(default)]
    bounty: Option<BountyReq>,
    #[serde(default)]
    provenance: Option<ProvenanceReq>,
    #[serde(default)]
    exposure: Option<ExposureReq>,
}

#[derive(serde::Deserialize)]
struct EscrowReq {
    cell: String,
    escrowed_slot: usize,
    released_slot: usize,
    refunded_slot: usize,
    #[serde(default)]
    prior_escrowed: Option<u64>,
}

#[derive(serde::Deserialize)]
struct BountyReq {
    cell: String,
    state_slot: usize,
    ladder: Vec<u64>,
    #[serde(default)]
    prior_state: Option<u64>,
}

#[derive(serde::Deserialize)]
struct ProvenanceReq {
    cell: String,
    entry_base: usize,
    #[serde(default)]
    claims: Vec<String>,
    #[serde(default)]
    prior_committed: Vec<String>,
}

#[derive(serde::Deserialize)]
struct ExposureReq {
    cell: String,
    reserve_slot: usize,
    #[serde(default)]
    prior_reserve: Option<u64>,
}

/// The response envelope the binding receives.
#[derive(serde::Serialize)]
struct Response {
    ok: bool,
    pass: bool,
    assurance: Option<crate::Assurance>,
    app_findings: Vec<crate::Finding>,
    error: Option<String>,
}

impl Response {
    fn err(msg: impl Into<String>) -> Self {
        Response {
            ok: false,
            pass: false,
            assurance: None,
            app_findings: Vec::new(),
            error: Some(msg.into()),
        }
    }
}

fn parse_hex32(s: &str) -> Result<[u8; 32], String> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 64 {
        return Err(format!("expected 64 hex chars (32 bytes), got {}", s.len()));
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16)
            .map_err(|_| format!("invalid hex byte at position {}", 2 * i))?;
    }
    Ok(out)
}

fn parse_cell(s: &str) -> Result<CellId, String> {
    Ok(CellId(parse_hex32(s)?))
}

/// The pure core: a JSON request string → a JSON response string. Factored out
/// of the `unsafe` FFI shell so it is unit-testable without raw pointers.
pub(crate) fn analyze_json(input: &str) -> String {
    let req: Request = match serde_json::from_str(input) {
        Ok(r) => r,
        Err(e) => {
            return to_json(&Response::err(format!(
                "request is not a valid uverify Request JSON: {e}"
            )));
        }
    };

    let mut assurance = crate::analyze(&req.forest, req.treat_as_ring);
    let mut app_findings = Vec::new();

    if let Some(appreq) = req.app {
        if let Some(es) = appreq.escrow {
            let cell = match parse_cell(&es.cell) {
                Ok(c) => c,
                Err(e) => return to_json(&Response::err(format!("app.escrow.cell: {e}"))),
            };
            let schema = app::EscrowSchema {
                cell,
                escrowed_slot: es.escrowed_slot,
                released_slot: es.released_slot,
                refunded_slot: es.refunded_slot,
            };
            app_findings.extend(
                app::check_escrow_conservation(&req.forest, &schema, es.prior_escrowed)
                    .findings()
                    .iter()
                    .cloned(),
            );
        }
        if let Some(b) = appreq.bounty {
            let cell = match parse_cell(&b.cell) {
                Ok(c) => c,
                Err(e) => return to_json(&Response::err(format!("app.bounty.cell: {e}"))),
            };
            let schema = app::LifecycleSchema {
                cell,
                state_slot: b.state_slot,
                ladder: b.ladder,
            };
            app_findings.extend(
                app::check_bounty_lifecycle(&req.forest, &schema, b.prior_state)
                    .findings()
                    .iter()
                    .cloned(),
            );
        }
        if let Some(p) = appreq.provenance {
            let cell = match parse_cell(&p.cell) {
                Ok(c) => c,
                Err(e) => return to_json(&Response::err(format!("app.provenance.cell: {e}"))),
            };
            let claims = match p
                .claims
                .iter()
                .map(|s| parse_hex32(s))
                .collect::<Result<Vec<_>, _>>()
            {
                Ok(c) => c,
                Err(e) => return to_json(&Response::err(format!("app.provenance.claims: {e}"))),
            };
            let prior = match p
                .prior_committed
                .iter()
                .map(|s| parse_hex32(s))
                .collect::<Result<Vec<_>, _>>()
            {
                Ok(c) => c,
                Err(e) => {
                    return to_json(&Response::err(format!(
                        "app.provenance.prior_committed: {e}"
                    )));
                }
            };
            let schema = app::ProvenanceSchema {
                cell,
                entry_base: p.entry_base,
            };
            app_findings.extend(
                app::check_provenance_chain_in_forest(&req.forest, &schema, &claims, &prior)
                    .findings()
                    .iter()
                    .cloned(),
            );
        }
        if let Some(ex) = appreq.exposure {
            let cell = match parse_cell(&ex.cell) {
                Ok(c) => c,
                Err(e) => return to_json(&Response::err(format!("app.exposure.cell: {e}"))),
            };
            let schema = app::ExposureSchema {
                cell,
                reserve_slot: ex.reserve_slot,
            };
            // The exposure ceiling is surfaced as a first-class Assurance verdict
            // (the `≤` twin of conservation), not folded into `app_findings` — so
            // the light-client Response carries it under `assurance.exposure` and
            // `assurance.pass()` accounts for it below.
            assurance.exposure = app::check_exposure_bound(&req.forest, &schema, ex.prior_reserve);
        }
    }

    let pass = assurance.pass() && app_findings.is_empty();
    to_json(&Response {
        ok: true,
        pass,
        assurance: Some(assurance),
        app_findings,
        error: None,
    })
}

fn to_json(r: &Response) -> String {
    // Response is plain data; serialization cannot realistically fail, but if it
    // somehow did we still hand back a valid JSON error rather than panic.
    serde_json::to_string(r).unwrap_or_else(|e| {
        format!("{{\"ok\":false,\"pass\":false,\"assurance\":null,\"app_findings\":[],\"error\":\"serialize failed: {e}\"}}")
    })
}

/// **`uverify_analyze`** — the C-ABI entry. Reads `len` bytes of UTF-8 JSON from
/// `json_ptr` (a [`Request`]), runs the static assurance + any selected
/// app-level checks, and returns a freshly-allocated NUL-terminated UTF-8 JSON C
/// string (a [`Response`]).
///
/// The returned pointer is owned by the caller and MUST be released with
/// [`uverify_free`] (it was allocated by Rust's allocator via [`CString`]).
///
/// Returns a null pointer ONLY when `json_ptr` is null or `len` is 0. Every
/// other error (bad UTF-8, bad JSON, a malformed app cell id) is reported in
/// band as a valid JSON string with `"ok": false` and a populated `"error"`.
///
/// # Safety
/// `json_ptr` must point to at least `len` valid, readable bytes. The bytes are
/// copied immediately; the caller may free its buffer after this returns. The
/// returned pointer must be freed exactly once with [`uverify_free`] and not
/// used afterward.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn uverify_analyze(json_ptr: *const c_uchar, len: usize) -> *mut c_char {
    if json_ptr.is_null() || len == 0 {
        return std::ptr::null_mut();
    }
    // SAFETY: per the function contract, `json_ptr` points to `len` valid bytes.
    let bytes = unsafe { std::slice::from_raw_parts(json_ptr, len) };
    let response = match std::str::from_utf8(bytes) {
        Ok(s) => analyze_json(s),
        Err(_) => to_json(&Response::err("request bytes are not valid UTF-8")),
    };
    // CString::new fails only on an interior NUL; our JSON never contains one.
    match CString::new(response) {
        Ok(c) => c.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// **`uverify_free`** — release a string returned by [`uverify_analyze`].
///
/// # Safety
/// `ptr` must be a pointer previously returned by [`uverify_analyze`] (and not
/// already freed). A null pointer is accepted and ignored.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn uverify_free(ptr: *mut c_char) {
    if !ptr.is_null() {
        // SAFETY: per the contract, `ptr` was returned by `uverify_analyze`
        // (a `CString::into_raw`) and is freed exactly once here.
        drop(unsafe { CString::from_raw(ptr) });
    }
}

/// **`uverify_version`** — the crate semver as a static C string (no free
/// needed; it has `'static` lifetime). Lets a binding assert ABI/feature parity
/// at load time.
#[unsafe(no_mangle)]
pub extern "C" fn uverify_version() -> *const c_char {
    // A compile-time NUL-terminated literal; never freed.
    concat!(env!("CARGO_PKG_VERSION"), "\0").as_ptr() as *const c_char
}

// Keep `CStr` referenced so a future round-trip helper (used by bindings that
// echo a request) does not warn; also documents the inbound contract type.
#[allow(dead_code)]
fn _inbound_is_cstr_compatible(p: *const c_char) -> Option<usize> {
    if p.is_null() {
        return None;
    }
    // SAFETY: documented contract — only called on a valid NUL-terminated ptr.
    Some(unsafe { CStr::from_ptr(p) }.to_bytes().len())
}
