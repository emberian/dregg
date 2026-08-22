//! THE POSITIVE POLARITY of the coord 2PC gate — the missing half of
//! `dregg-coord/tests/twin_fail_closed.rs`.
//!
//! # Why this test exists
//!
//! `twoc_pc_fails_closed_without_gate` (registry row `dregg-coord :: test:twin_fail_closed`) pins
//! the NEGATIVE polarity: with no verified gate registered, a full-Yes tally must Abort rather than
//! silently native-decide. That falsifier is correct and it is load-bearing — but it is green
//! *precisely in the disarmed configuration*, so on its own it cannot distinguish "the fail-closed
//! path works" from "nothing verified is linked and nothing ever will be". A pair of polarities
//! can; one alone cannot.
//!
//! This is the other half: register the REAL `dregg-exec-lean::register_distributed_gates()` gate
//! over the linked archive and assert that the SAME full-Yes tally now COMMITS through the
//! Lean-PROVEN `dregg_coord_2pc_decide` (= `Dregg2.Coord.TwoPhaseCommit.evaluate`). Together the
//! two say: absent ⇒ refuse, present ⇒ the proven verdict — and neither is satisfiable by the
//! other's configuration.
//!
//! It lives HERE and not in `dregg-coord` for the same reason `fulfillment_ffi_verified.rs` does:
//! `dregg-coord` is FFI-free by construction (see its `Cargo.toml` — no `dregg-lean-ffi`, no
//! `dregg-exec-lean`, no dev-dependencies at all), so it structurally CANNOT register a gate. Only
//! the FFI boundary crate can.
//!
//! # Honest skip, armed panic
//!
//! Gated on `dregg_lean_ffi::demand_lean`: without a linked archive that exports the distributed
//! decisions this test SKIPS and says so, and under `DREGG_TEST_REQUIRE_LEAN=1` (the arming CI
//! test lane uses) it PANICS instead of reporting a green that asserted nothing.
//!
//! Run with: `cargo test -p dregg-exec-lean --test coord_gate_positive_polarity`

use std::collections::HashMap;

use dregg_cell::{CellId, Preconditions};
use dregg_coord::atomic::{AtomicForest, Coordinator, Decision, Vote};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
use dregg_turn::{CallForest, ComputronCosts};

fn node_id(n: u8) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = n;
    id
}

fn keypair(n: u8) -> ([u8; 32], [u8; 32]) {
    let seed = *blake3::hash(&[n; 1]).as_bytes();
    let pk = Vote::public_key_from_signing_key(&seed);
    (seed, pk)
}

#[test]
fn twoc_pc_commits_through_the_verified_gate_when_present() {
    dregg_exec_lean::register_distributed_gates();
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::distributed_exports_available(),
        "verified distributed exports (dregg_captp_validate_handoff / dregg_coord_2pc_decide)",
    ) {
        return;
    }

    // The SAME shape as the fail-closed twin: 3 participants, threshold 2, all Yes.
    let nodes = vec![node_id(1), node_id(2), node_id(3)];
    let mut signing_keys = Vec::new();
    let mut participant_keys: HashMap<[u8; 32], [u8; 32]> = HashMap::new();
    for nid in &nodes {
        let (sk, pk) = keypair(nid[0]);
        signing_keys.push(sk);
        participant_keys.insert(*nid, pk);
    }

    let initiator = CellId::from_bytes([9u8; 32]);
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: initiator,
        method: *blake3::hash(b"noop").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    });
    let af = AtomicForest::new(nodes.clone(), forest, vec![], initiator, 0, None);

    let mut coord = Coordinator::new(
        node_id(1),
        *blake3::hash(b"coord-gate-positive-polarity").as_bytes(),
        2, // threshold
        ComputronCosts::zero(),
        u64::MAX,
        participant_keys,
    );
    let prop = coord.propose(af.clone()).expect("propose");

    let mut terminal = Decision::Pending;
    for (i, nid) in nodes.iter().enumerate() {
        let sig = Vote::sign_yes(&prop.proposal_id, &af.hash, &signing_keys[i]);
        if let Some(d) = coord
            .receive_vote(*nid, Vote::yes(sig))
            .expect("receive_vote")
        {
            terminal = d;
            break;
        }
    }

    assert_eq!(
        terminal,
        Decision::Commit,
        "with the verified Lean gate REGISTERED, a threshold-reaching all-Yes tally must COMMIT \
         through dregg_coord_2pc_decide. Abort here would mean the gate is registered but the \
         export is not answering — i.e. the fail-closed path is the ONLY path the system has, and \
         `twoc_pc_fails_closed_without_gate` is passing for the wrong reason."
    );
}

/// The gate's own availability probe must agree with the archive. Cheap, but it is the assertion
/// that makes an un-spliced archive visible HERE rather than only as a missing `#[cfg]`.
#[test]
fn distributed_gate_availability_matches_the_linked_archive() {
    dregg_exec_lean::register_distributed_gates();
    let available = dregg_lean_ffi::distributed_exports_available();
    if !dregg_lean_ffi::demand_lean(available, "verified distributed exports") {
        return;
    }
    // A linked, spliced archive answers the wire; a seed-only archive would not.
    let verdict = dregg_lean_ffi::verified_2pc_decide("y=2;n=0;N=3;t=2")
        .expect("the distributed exports are available, so the 2PC wire must decide");
    assert!(
        matches!(verdict, dregg_lean_ffi::Decision2pc::Commit),
        "2/3 Yes at threshold 2 is a COMMIT under Dregg2.Coord.TwoPhaseCommit.evaluate; got \
         {verdict:?}"
    );
}
