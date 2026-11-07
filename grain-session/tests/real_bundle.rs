//! The stranger's check on the REAL bundle, and the four tamper classes refused on it.
//!
//! Needs the bundle (kept out of git until publication is decided) and the renter pins:
//!   GRAIN_SESSION_BUNDLE=<bundle.json> GRAIN_SESSION_RENTER=<renter.key> GRAIN_SESSION_VK=<hex> \
//!   cargo test -p grain-session --test real_bundle -- --ignored --nocapture
//! `renter.key` is `keygen`'s file (seed line, nonce line); only the PUBLIC key and the nonce are
//! used here. The Lean core must be linked (the R3 accept has no Rust fallback).

use std::path::PathBuf;

use grain_session::{Bundle, Refusal, parse32, tamper, verify_bundle};

fn pins() -> Option<(Bundle, [u8; 32], [u8; 32], [u8; 32])> {
    let b = PathBuf::from(std::env::var("GRAIN_SESSION_BUNDLE").ok()?);
    let k = std::fs::read_to_string(std::env::var("GRAIN_SESSION_RENTER").ok()?).ok()?;
    let mut lines = k.lines();
    let seed = parse32(lines.next()?).ok()?;
    let nonce = parse32(lines.next()?).ok()?;
    let public = dregg_agent::receipt::ReceiptSigner::from_seed(seed).public();
    let vk = parse32(&std::env::var("GRAIN_SESSION_VK").ok()?).ok()?;
    Some((Bundle::load(&b).ok()?, public, nonce, vk))
}

#[test]
#[ignore = "needs the real bundle (GRAIN_SESSION_BUNDLE, GRAIN_SESSION_RENTER) and the linked Lean core"]
fn the_real_bundle_is_accepted_and_every_tamper_class_is_refused() {
    let (b, renter, nonce, vk) =
        pins().expect("set GRAIN_SESSION_BUNDLE, GRAIN_SESSION_RENTER and GRAIN_SESSION_VK");
    let a = verify_bundle(&b, &renter, &nonce, &vk).expect("the honest bundle verifies");
    eprintln!(
        "ACCEPT: {} calls, {} windows, {} receipts linked, {} folded legs",
        a.calls, a.windows, a.ladder.linked, a.r3.num_turns
    );
    for (name, t) in tamper::cases(&b) {
        let r = verify_bundle(&t, &renter, &nonce, &vk);
        match &r {
            Err(e) => eprintln!("{name:<28} {e}"),
            Ok(_) => panic!("{name}: a tampered bundle was ACCEPTED"),
        }
        // Each class is refused by the rung that owns it, not by an incidental parse failure.
        let ok = match (name, r.as_ref().unwrap_err()) {
            ("truncate: last window", Refusal::Ladder(_)) => true,
            (
                "truncate: last call"
                | "unreceipted: a call appended"
                | "unreceipted: a call inserted",
                Refusal::WindowMismatch { .. } | Refusal::WindowCount { .. },
            ) => true,
            (
                "rewrite: a call's tool"
                | "rewrite: a call's commitment"
                | "reorder: two adjacent calls",
                Refusal::WindowMismatch { .. },
            ) => true,
            ("reorder: two receipts" | "rewrite: a receipt label", Refusal::Ladder(_)) => true,
            ("R3: aggregate byte flipped", Refusal::R3(_) | Refusal::Malformed(_)) => true,
            (
                "executor: last receipt forged" | "executor: last receipt unsigned",
                Refusal::ExecutorReceipts(_),
            ) => true,
            _ => false,
        };
        assert!(
            ok,
            "{name}: refused by the wrong rung: {:?}",
            r.unwrap_err()
        );
    }
    // A stranger who pins a DIFFERENT renter key is refused at the statement.
    let other = dregg_agent::receipt::ReceiptSigner::from_seed([9u8; 32]).public();
    assert!(matches!(
        verify_bundle(&b, &other, &nonce, &vk),
        Err(Refusal::StatementSignature)
    ));
    // A VK that is not the stranger's anchor is refused.
    assert!(matches!(
        verify_bundle(&b, &renter, &nonce, &[7u8; 32]),
        Err(Refusal::StatementMismatch(_))
    ));
}

#[test]
#[ignore = "needs the cv exports (GRAIN_SESSION_EXPORTS) and demo (b)'s transcript.json"]
fn the_projection_is_demo_b_s_projection() {
    let dir = PathBuf::from(std::env::var("GRAIN_SESSION_EXPORTS").expect("GRAIN_SESSION_EXPORTS"));
    let calls = grain_session::project_exports(&dir).expect("project");
    let demo: serde_json::Value = serde_json::from_slice(
        &std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../demo/datalog-governance/data/transcript.json"
        ))
        .expect("demo (b) transcript.json"),
    )
    .unwrap();
    let mut want = Vec::new();
    for t in demo["transcripts"].as_array().unwrap() {
        for c in t["calls"].as_array().unwrap() {
            want.push((
                t["agent"].as_str().unwrap().to_string(),
                c["seq"].as_u64().unwrap(),
                c["tool"].as_str().unwrap().to_string(),
                c["use_id"].as_str().unwrap().to_string(),
                c["ts"].as_str().unwrap_or("").to_string(),
                c.get("path").and_then(|p| p.as_str()).map(str::to_string),
                c.get("spawned")
                    .and_then(|p| p.as_str())
                    .map(str::to_string),
            ));
        }
    }
    let got: Vec<_> = calls
        .iter()
        .map(|c| {
            let p = &c.public;
            (
                p.agent.clone(),
                p.seq,
                p.tool.clone(),
                p.use_id.clone(),
                p.ts.clone(),
                p.path.clone(),
                p.spawned.clone(),
            )
        })
        .collect();
    assert_eq!(got.len(), want.len(), "call count");
    assert_eq!(got, want, "field-for-field the published projection");
}
