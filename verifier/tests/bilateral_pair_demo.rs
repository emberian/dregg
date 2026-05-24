//! Stage 7-γ.2 Phase 1 — bilateral-pair demo / integration test.
//!
//! Demonstrates an end-to-end bilateral verification flow:
//!
//!   1. Build a [`Turn`] with a Transfer(alice → bob).
//!   2. Fabricate per-cell [`WitnessedReceipt`]s for alice + bob with the
//!      γ.2 bilateral PI slots populated.
//!   3. Serialize a [`BilateralBundle`] to a tempfile.
//!   4. Invoke the `pyana-verifier bilateral-pair <bundle.json>` subprocess.
//!   5. Confirm exit code 0 + `verified == true` in the JSON verdict.
//!   6. Tamper with the bundle (overwrite Alice's `OUTGOING_TRANSFER_ROOT`
//!      with garbage), re-invoke, confirm exit code 1 + `verified == false`.
//!
//! This is the "demo wire-up" deliverable for Stage 7-γ.2 Phase 1: an
//! executable witness that the off-AIR bilateral verifier rejects tampered
//! cross-cell evidence. The flow runs entirely in-tree without requiring
//! the full two-AI MCP harness — the WRs are fabricated for the bilateral
//! slots only, since γ.2 Phase 1 is PI-only and does not require a real
//! STARK proof inside each WR for the cross-cell check (the STARK proof
//! verification is orthogonal — Phase 1 layers cross-cell agreement on top
//! of per-cell STARK soundness).

use std::io::Write;
use std::process::Command;

use pyana_circuit::effect_vm::pi as p;
use pyana_turn::{ActionBuilder, Turn, TurnBuilder, TurnReceipt};
use pyana_types::CellId;
use pyana_verifier::{
    BilateralBundle, BilateralEntry, BilateralVerdict, fabricate_witnessed_receipt,
};

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

fn dummy_receipt(agent: CellId) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
    }
}

fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
        .effect_transfer(alice, bob, amount)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

fn write_bundle(bundle: &BilateralBundle) -> tempfile::NamedTempFile {
    let mut f = tempfile::NamedTempFile::new().expect("tempfile");
    let json = serde_json::to_string_pretty(bundle).expect("serialize");
    f.write_all(json.as_bytes()).expect("write");
    f
}

fn run_subcommand(bundle_path: &std::path::Path) -> (i32, BilateralVerdict) {
    let bin = env!("CARGO_BIN_EXE_pyana-verifier");
    let out = Command::new(bin)
        .arg("bilateral-pair")
        .arg(bundle_path)
        .output()
        .expect("spawn pyana-verifier");
    let code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let verdict: BilateralVerdict = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("parse verdict failed: {e}; stdout={stdout}"));
    (code, verdict)
}

#[test]
fn bilateral_pair_demo_happy_path_then_tamper() {
    // ---- Step 1-3: build the honest bundle ----
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = make_transfer_turn(alice, bob, 100, 1);
    let alice_wr = fabricate_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
    let bob_wr = fabricate_witnessed_receipt(&turn, &bob, dummy_receipt(alice));

    let bundle = BilateralBundle {
        turn: turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: alice_wr.clone(),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: bob_wr.clone(),
            },
        ],
    };
    let bundle_file = write_bundle(&bundle);

    // ---- Step 4-5: invoke verifier subprocess ----
    let (code, verdict) = run_subcommand(bundle_file.path());
    assert_eq!(
        code, 0,
        "honest bilateral bundle should exit 0; verdict={:?}",
        verdict
    );
    assert!(
        verdict.verified,
        "verdict.verified must be true: {verdict:?}"
    );
    assert_eq!(verdict.entry_count, 2);
    assert_eq!(verdict.transfer_count, 1);
    assert_eq!(verdict.grant_count, 0);
    assert_eq!(verdict.introduce_count, 0);

    // ---- Step 6: tamper with Alice's OUTGOING_TRANSFER_ROOT ----
    let mut tampered_alice = alice_wr;
    tampered_alice.public_inputs[p::OUTGOING_TRANSFER_ROOT_BASE] = 0xDEAD_BEEF & 0x7FFF_FFFF;
    let tampered_bundle = BilateralBundle {
        turn,
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: tampered_alice,
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: bob_wr,
            },
        ],
    };
    let tampered_file = write_bundle(&tampered_bundle);
    let (code, verdict) = run_subcommand(tampered_file.path());
    assert_eq!(
        code, 1,
        "tampered bundle should exit 1; verdict={:?}",
        verdict
    );
    assert!(
        !verdict.verified,
        "tampered bundle must report verified=false: {verdict:?}"
    );
    assert!(
        verdict.reason.contains("root") || verdict.reason.contains("outgoing_transfer"),
        "expected root-mismatch reason, got: {}",
        verdict.reason
    );
}

#[test]
fn bilateral_pair_demo_missing_peer_rejects() {
    // Demo: a malicious prover who tries to ship only one half of a
    // bilateral Transfer (the sender's WR) and elide the receiver. The
    // bilateral-pair verifier rejects on the cross-side existence check
    // — this is the §4.5 "sender invents a transfer to a non-existent cell"
    // adversarial case from STAGE-7-GAMMA-2-PI-DESIGN.md.
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = make_transfer_turn(alice, bob, 100, 1);
    let alice_wr = fabricate_witnessed_receipt(&turn, &alice, dummy_receipt(alice));

    let bundle = BilateralBundle {
        turn,
        entries: vec![BilateralEntry {
            cell_id: alice,
            witnessed_receipt: alice_wr,
        }],
    };
    let bundle_file = write_bundle(&bundle);
    let (code, verdict) = run_subcommand(bundle_file.path());
    assert_eq!(code, 1, "missing-peer bundle should exit 1");
    assert!(!verdict.verified);
    assert!(
        verdict.reason.contains("missing peer") || verdict.reason.contains("Transfer"),
        "expected missing-peer reason, got: {}",
        verdict.reason
    );
}
