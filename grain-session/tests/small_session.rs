//! A small session end to end: produce (real minter, signed executor receipts, threaded fold),
//! countersign, verify (R0-R2, windows, executor receipts, head opening, Lean R3), then every
//! tamper class refused. SLOW (two folds): `cargo test -p grain-session --test small_session --
//! --ignored --nocapture`. The VK is minted by `synthetic_setup` from a content-free session of
//! the same shape, never taken from the bundle.

use grain_session::{CallPublic, Refusal, countersign, produce, tamper, verify_bundle};

fn calls(n: usize) -> Vec<CallPublic> {
    (0..n)
        .map(|i| CallPublic {
            agent: "root".into(),
            seq: i as u64,
            tool: if i % 2 == 0 {
                "Bash".into()
            } else {
                "Read".into()
            },
            use_id: format!("toolu_test_{i}"),
            ts: format!("2026-11-06T00:00:{i:02}Z"),
            path: (i % 2 == 1).then(|| format!("/tmp/f{i}")),
            spawned: None,
            commit: hex::encode([i as u8; 32]),
        })
        .collect()
}

#[test]
#[ignore = "SLOW: two recursive folds (~30 min on bb2); run with --ignored"]
fn a_small_session_verifies_and_every_tamper_is_refused() {
    let nonce = [0x5au8; 32];
    let seed = [0x11u8; 32];
    let (mut bundle, stats) =
        produce::produce("test-session", calls(6), 2, nonce).expect("produce");
    eprintln!("{stats:?}");
    let vk = produce::synthetic_setup(stats.windows).expect("independent setup");
    let renter = countersign(&mut bundle, seed, &nonce, &vk).expect("countersign");
    let a = verify_bundle(&bundle, &renter, &nonce, &vk).expect("ACCEPT");
    assert_eq!((a.calls, a.windows), (6, 3));
    for (name, t) in tamper::cases(&bundle) {
        let r = verify_bundle(&t, &renter, &nonce, &vk);
        eprintln!(
            "{name:<32} {}",
            r.as_ref()
                .map(|_| "ACCEPTED".to_string())
                .unwrap_or_else(|e| e.to_string())
        );
        assert!(r.is_err(), "{name} must be refused");
        if name.starts_with("executor:") {
            assert!(matches!(r, Err(Refusal::ExecutorReceipts(_))), "{name}");
        }
    }
}
