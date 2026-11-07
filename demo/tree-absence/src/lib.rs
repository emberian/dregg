//! tree-absence: the Rust certificate producer for initiative 12 (tree automata over JSON/CBOR).
//!
//! Everything here PRODUCES certificates in the wire format of
//! `docs/automata/tree/FORMAT.md`; acceptance is decided only by the Lean executable
//! `tree-check verify` (`metatheory/TreeCheck.lean`). The projection `json::parse` mirrors
//! `Dregg2.Tree.Json.parse` and is held to it by `tree-cert conform`.

pub mod cert;
pub mod invocation;
pub mod json;
pub mod merkle;
pub mod schema;
pub mod value;

use std::path::PathBuf;

/// The Lean checker: `$TREE_CHECK`, else the metatheory build output next to this crate.
pub fn tree_check_path() -> PathBuf {
    match std::env::var_os("TREE_CHECK") {
        Some(p) => PathBuf::from(p),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../metatheory/.lake/build/bin/tree-check"),
    }
}

/// `tree-check project`'s line for a projected value (keys sorted, compact).
pub fn project_line(v: &value::JVal) -> String {
    serde_json::json!({
        "cbor": value::hex(&value::encode(v)),
        "tree_root": value::hex(&merkle::digest(v)),
        "flat_digest": value::hex(&value::flat_digest(v)),
    })
    .to_string()
}

/// Inputs on which the projection is easy to get wrong; `conform --edges` runs both sides on them.
pub const EDGES: &[&[u8]] = &[
    br#"{"b":1,"a":[true,null,-0,1.50,1e2,-2.5e-3]}"#,
    b"0.000",
    b"10e-1",
    b"1e400",
    b"1e4096",
    b"1e4097",
    b"1E-4096",
    b"-0.0e+0",
    b"123456789012345678901234567890.0100",
    b"18446744073709551615",
    b"18446744073709551616",
    b"-18446744073709551616",
    b"-18446744073709551617",
    b"9007199254740993",
    b"\"\\u0070kill\\u0020-f\"",
    b"\"\\ud83d\\ude00\"",
    b"\"\\ud800\"",
    b"\"\\udc00\"",
    b"\"\\ud800\\u0041\"",
    b"\"\\uD83D\\uDE00\"",
    b"\"\\u00e9\"",
    b"\"\xc3\xa9\"",
    b"\"e\\u0301\"",
    br#""\"\\\/\b\f\n\r\t""#,
    br#""\x""#,
    br#""\u12""#,
    b"\"\x0a\"",
    b"\"\x7f\"",
    b"\"\xc0\xaf\"",
    b"\"\xed\xa0\x80\"",
    b"\"\xf4\x90\x80\x80\"",
    br#"{"a":1,"a":2}"#,
    b"{\"a\":1,\"\\u0061\":2}",
    br#"{"aa":1,"b":2,"":3}"#,
    b"[]",
    b"{ }",
    b" \t\n\r 7 \r\n",
    b"1 2",
    b"{} x",
    b"01",
    b"-01",
    b".5",
    b"1.",
    b"+1",
    b"-",
    b"1e",
    b"1e+",
    b"{a:1}",
    b"[1,]",
    br#"{"a":1,}"#,
    b"[,1]",
    b"",
    b"tru",
    b"nul",
    b"nullx",
    br#""abc"#,
    b"[1",
    b"[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]",
    br#"[[[]],{"k":[{}]}]"#,
    b"{\"command\":\"\\u0070kill -f x\"}",
];
