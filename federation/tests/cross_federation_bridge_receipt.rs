//! Stage 9 P3.E: end-to-end cross-federation receipt chain test.
//!
//! Demonstrates that the Stage 9 receipt overhaul composes correctly across
//! a federation boundary:
//!
//! 1. Federation A locks a note (Phase 1 — `BridgeReceiptEnvelope::Locked`).
//!    Its committee signs the lock's `body_hash` via BLS threshold; the
//!    resulting `ThresholdQC` is the cross-federation evidence.
//! 2. Federation B receives the lock envelope + QC, verifies the QC against
//!    A's committee, admits the lock to its own `BridgePhaseLog`, mints,
//!    and produces a Phase-2 (Witnessed) envelope with its own QC.
//! 3. Federation A receives B's Witnessed envelope, verifies B's QC against
//!    B's committee, admits to its phase log, and finalizes (Phase 3).
//! 4. Federation A's Phase-3 receipt then re-verifies under B (so a
//!    finalize-after-finalize replay can be detected from either side).
//!
//! This is the "cross-federation receipt chain" property called out in
//! EFFECT-VM-SHAPE-A.md Stage 9: receipts cross federation boundaries
//! intact, with monotone phase advancement and replay rejection working
//! symmetrically on both sides.
//!
//! ## Documented cross-federation receipt format
//!
//! Per `DESIGN-receipts.md` §5 (per-phase) plus §4 (federation QC):
//!
//! - **Body**: `BridgeReceiptEnvelope` (`pyana-cell::note_bridge`). Carries
//!   `(version, phase, bridge_id, src_federation, dst_federation,
//!   block_height, previous_phase_receipt_hash, payload)`. Hash:
//!   `body_hash()` = BLAKE3_derive_key("pyana-bridge-envelope-v1", ...).
//! - **Signature**: a `FederationCommittee::aggregate` BLS threshold
//!   signature over `body_hash()`, wrapped in a `ThresholdQC`. Both
//!   federations register each other's committees out of band (the trust
//!   root in this layer — bilateral by design).
//! - **Chain link**: `previous_phase_receipt_hash` ≡ prior phase's
//!   `body_hash()`. The `BridgePhaseLog` enforces this on admission and
//!   rejects any replay or non-monotone advancement.

use pyana_cell::note_bridge::{
    compute_bridge_id, BridgePhase, BridgePhaseLog, BridgeReceiptEnvelope,
};
use pyana_federation::threshold::{
    generate_test_committee, FederationCommittee, MemberSecret, ThresholdQC,
};

/// Sign `body_hash` with `threshold` out of the committee's members.
/// Helper that wraps the BLS aggregation boilerplate.
fn quorum_sign(
    committee: &FederationCommittee,
    members: &[MemberSecret],
    threshold: usize,
    body_hash: &[u8; 32],
) -> ThresholdQC {
    let shares: Vec<(usize, _)> = members
        .iter()
        .take(threshold)
        .map(|m| (m.index, committee.sign_share(m, body_hash)))
        .collect();
    committee
        .aggregate(&shares, body_hash)
        .expect("aggregation must succeed at threshold")
}

#[test]
fn cross_federation_lock_witness_finalize_roundtrip() {
    // ----- Setup: two federations, each with a 4-of-4 threshold committee.
    // (The hints crate's threshold scheme works fine with threshold == n; we
    // use 4-of-4 here for a deterministic test, threshold soundness is
    // exercised in `federation::receipt` unit tests.)
    let threshold = 4usize;
    let (committee_a, members_a) =
        generate_test_committee(4, threshold).expect("federation A committee");
    let (committee_b, members_b) =
        generate_test_committee(4, threshold).expect("federation B committee");

    let fed_a_id: [u8; 32] = [0xAA; 32];
    let fed_b_id: [u8; 32] = [0xBB; 32];

    // Each federation maintains its own phase log. They are populated
    // symmetrically as receipts cross the boundary.
    let mut log_a = BridgePhaseLog::new();
    let mut log_b = BridgePhaseLog::new();

    // ----- Phase 1: federation A locks a note.
    let lock_nullifier = [0xC0; 32];
    let initiating_nonce = 1u64;
    let bridge_id = compute_bridge_id(&lock_nullifier, &fed_a_id, &fed_b_id, initiating_nonce);

    let lock_envelope = BridgeReceiptEnvelope::new_locked(
        bridge_id,
        fed_a_id,
        fed_b_id,
        /* block_height */ 100,
        lock_nullifier,
        /* asset_type */ 7,
        /* value */ 500,
        /* timeout_height */ 200,
        /* spending_proof_digest */ [0x77; 32],
    );
    let lock_hash = lock_envelope.body_hash();
    let lock_qc = quorum_sign(&committee_a, &members_a, threshold, &lock_hash);

    // Federation A records its own lock.
    log_a.admit(&lock_envelope).expect("A admits its own lock");

    // ----- Cross-federation transmission: A → B.
    // B verifies A's QC over the lock body, then admits to its phase log.
    assert!(
        committee_a.verify(&lock_qc, &lock_hash).is_ok(),
        "B verifies A's lock QC against A's registered committee"
    );
    log_b
        .admit(&lock_envelope)
        .expect("B admits A's lock after verifying QC");

    // ----- Phase 2: federation B mints and witnesses.
    let mint_height = 105u64;
    let mint_commitment = [0x42; 32];
    let witness_envelope = BridgeReceiptEnvelope::new_witnessed(
        bridge_id,
        fed_a_id,
        fed_b_id,
        /* block_height */ 110,
        lock_hash,
        mint_height,
        mint_commitment,
    );
    let witness_hash = witness_envelope.body_hash();
    let witness_qc = quorum_sign(&committee_b, &members_b, threshold, &witness_hash);

    // B records its own witness.
    log_b
        .admit(&witness_envelope)
        .expect("B admits its own witness");

    // ----- Cross-federation transmission: B → A.
    // A verifies B's QC, then admits.
    assert!(
        committee_b.verify(&witness_qc, &witness_hash).is_ok(),
        "A verifies B's witness QC against B's registered committee"
    );
    log_a
        .admit(&witness_envelope)
        .expect("A admits B's witness after verifying QC");

    // ----- Phase 3: federation A finalizes.
    let finalize_envelope = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        fed_a_id,
        fed_b_id,
        /* block_height */ 115,
        witness_hash,
        /* finalize_height */ 116,
        /* post_nullifier_root */ [0xEE; 32],
    );
    let finalize_hash = finalize_envelope.body_hash();
    let finalize_qc = quorum_sign(&committee_a, &members_a, threshold, &finalize_hash);

    log_a
        .admit(&finalize_envelope)
        .expect("A admits its own finalize");

    // ----- Cross-federation transmission: A → B.
    // B can re-verify A's finalize and admit it; the chain link from
    // witness → finalize must reconcile.
    assert!(
        committee_a.verify(&finalize_qc, &finalize_hash).is_ok(),
        "B verifies A's finalize QC against A's registered committee"
    );
    log_b
        .admit(&finalize_envelope)
        .expect("B admits A's finalize after verifying QC");

    // ----- Both phase logs end in agreement.
    let (a_phase, a_hash) = log_a.get(&bridge_id).unwrap();
    let (b_phase, b_hash) = log_b.get(&bridge_id).unwrap();
    assert_eq!(a_phase, BridgePhase::Finalized);
    assert_eq!(b_phase, BridgePhase::Finalized);
    assert_eq!(a_hash, b_hash, "both federations must agree on the head");
    assert_eq!(a_hash, finalize_hash);
}

/// Replay rejection across federations: once federation A has finalized,
/// federation B's view of the bridge MUST NOT accept a late refund (or any
/// other re-advancement) even if it carries a valid (but stale) QC.
#[test]
fn cross_federation_replay_rejected_after_finalize() {
    let threshold = 4usize;
    let (committee_a, members_a) = generate_test_committee(4, threshold).unwrap();
    let (committee_b, members_b) = generate_test_committee(4, threshold).unwrap();

    let fed_a_id: [u8; 32] = [0xAA; 32];
    let fed_b_id: [u8; 32] = [0xBB; 32];
    let mut log_a = BridgePhaseLog::new();
    let mut log_b = BridgePhaseLog::new();

    let lock_nullifier = [0xC1; 32];
    let bridge_id = compute_bridge_id(&lock_nullifier, &fed_a_id, &fed_b_id, 1);

    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id,
        fed_a_id,
        fed_b_id,
        100,
        lock_nullifier,
        7,
        500,
        200,
        [0x77; 32],
    );
    let lock_hash = lock.body_hash();
    let _ = quorum_sign(&committee_a, &members_a, threshold, &lock_hash);
    log_a.admit(&lock).unwrap();
    log_b.admit(&lock).unwrap();

    // Phase 2 (Witnessed by B).
    let witness = BridgeReceiptEnvelope::new_witnessed(
        bridge_id, fed_a_id, fed_b_id, 110, lock_hash, 105, [0x42; 32],
    );
    let witness_hash = witness.body_hash();
    let _ = quorum_sign(&committee_b, &members_b, threshold, &witness_hash);
    log_a.admit(&witness).unwrap();
    log_b.admit(&witness).unwrap();

    // Phase 3 (Finalized by A).
    let finalize = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        fed_a_id,
        fed_b_id,
        115,
        witness_hash,
        116,
        [0xEE; 32],
    );
    log_a.admit(&finalize).unwrap();
    log_b.admit(&finalize).unwrap();

    // Adversary attempts: late refund (Phase 4) with a properly-signed body.
    // Federation B's phase log must reject it as non-monotone (Finalized is
    // terminal), even if A's QC over the refund body would have been valid.
    let late_refund = BridgeReceiptEnvelope::new_refunded(
        bridge_id, fed_a_id, fed_b_id, 250, lock_hash, 251,
    );
    let late_refund_hash = late_refund.body_hash();
    // (We don't even need a QC for the test — admission is gated first by
    // the phase log. But to make the test realistic we sign it anyway.)
    let late_qc = quorum_sign(&committee_a, &members_a, threshold, &late_refund_hash);
    assert!(committee_a.verify(&late_qc, &late_refund_hash).is_ok());

    let err = log_b
        .admit(&late_refund)
        .expect_err("late refund must be rejected after finalize");
    use pyana_cell::note_bridge::BridgePhaseError;
    assert!(
        matches!(
            err,
            BridgePhaseError::NonMonotoneAdvancement {
                last_phase: BridgePhase::Finalized,
                attempted_phase: BridgePhase::Refunded,
                ..
            }
        ),
        "expected NonMonotoneAdvancement, got {err:?}"
    );
}
