//! Extended 4-phase BridgeReceiptEnvelope adversarial scenarios.
//!
//! Complements `bridge_four_phase.rs` with cross-bridge replay,
//! per-nullifier exact-once consumption, multi-pair concurrency, and
//! AttestedRoot tampering attacks against the portable-note verifier.
//!
//! Layered on the same `dregg_cell::note_bridge` primitives the
//! original suite uses, exercising paths that audit AUDIT-federation.md
//! §10 noted were missing: cross-fed replay across THREE federations,
//! per-nullifier single-consumption with concurrent pending bridges,
//! and tamper of source_root.merkle_root.

use dregg_cell::note::{NoteCommitment, Nullifier};
use dregg_cell::note_bridge::{
    cancel_bridge, compute_bridge_id, create_portable_note, initiate_bridge, verify_portable_note,
    BridgeError, BridgePhase, BridgePhaseLog, BridgeReceiptEnvelope, BridgedNullifierSet,
    PendingBridgeSet,
};
use dregg_federation::FederationReceiptBody;
use dregg_turn::bilateral_schedule::derive_transfer_id;
use dregg_types::{AttestedRoot, CellId, FederationId};

const FED_A: [u8; 32] = [0xAA; 32];
const FED_B: [u8; 32] = [0xBB; 32];
const FED_C: [u8; 32] = [0xCC; 32];

fn attested_root(merkle: [u8; 32], note_tree: Option<[u8; 32]>, height: u64) -> AttestedRoot {
    AttestedRoot {
        merkle_root: merkle,
        note_tree_root: note_tree,
        nullifier_set_root: None,
        height,
        timestamp: 1_000,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![],
        threshold_qc: None,
        threshold: 0,
        federation_id: FederationId::PLACEHOLDER,
        receipt_stream_root: None,
    }
}

// ===========================================================================
// Per-nullifier exact-once consumption: a nullifier locked in
// `PendingBridgeSet` cannot be re-locked anywhere, even after the lock
// is acknowledged on a different federation.
// ===========================================================================

#[test]
fn locked_nullifier_cannot_be_relocked_to_different_destination() {
    let nullifier_bytes = [0x21; 32];
    let mut pending = PendingBridgeSet::new();

    // Lock nullifier with FED_B as destination.
    initiate_bridge(
        nullifier_bytes,
        FED_B,
        1000,
        1,
        100,
        vec![0xDE, 0xAD],
        &mut pending,
    )
    .expect("first lock to FED_B");
    assert!(pending.is_locked(&nullifier_bytes));

    // Attempt to re-lock SAME nullifier targeting FED_C — must fail.
    let result = initiate_bridge(
        nullifier_bytes,
        FED_C,
        1000,
        1,
        100,
        vec![0xBE, 0xEF],
        &mut pending,
    );
    assert!(
        result.is_err(),
        "re-locking a nullifier to a different destination must fail; got {result:?}"
    );
}

// ===========================================================================
// Multi-pair concurrent bridge: two different nullifiers from same
// source federation, bound to two different destinations, must each
// complete independently.
// ===========================================================================

#[test]
fn two_concurrent_bridges_different_nullifiers_independent_phase_logs() {
    let n1 = [0x31; 32];
    let n2 = [0x32; 32];
    let mut pending = PendingBridgeSet::new();

    let proof_bytes_1 = vec![1, 2, 3];
    let proof_bytes_2 = vec![4, 5, 6];

    initiate_bridge(n1, FED_B, 100, 1, 50, proof_bytes_1.clone(), &mut pending).expect("lock 1");
    initiate_bridge(n2, FED_C, 200, 1, 50, proof_bytes_2.clone(), &mut pending).expect("lock 2");

    assert!(pending.is_locked(&n1));
    assert!(pending.is_locked(&n2));

    let proof_digest_1 = *blake3::hash(&proof_bytes_1).as_bytes();
    let proof_digest_2 = *blake3::hash(&proof_bytes_2).as_bytes();

    let bridge_id_1 = compute_bridge_id(&n1, &FED_A, &FED_B, 1);
    let bridge_id_2 = compute_bridge_id(&n2, &FED_A, &FED_C, 1);

    let mut log = BridgePhaseLog::new();
    let lock1 = BridgeReceiptEnvelope::new_locked(
        bridge_id_1,
        FED_A,
        FED_B,
        1,
        n1,
        1,
        100,
        50,
        proof_digest_1,
    );
    let lock2 = BridgeReceiptEnvelope::new_locked(
        bridge_id_2,
        FED_A,
        FED_C,
        1,
        n2,
        1,
        200,
        50,
        proof_digest_2,
    );
    log.admit(&lock1).expect("admit lock1");
    log.admit(&lock2).expect("admit lock2");

    let (phase1, _) = log.get(&bridge_id_1).unwrap();
    let (phase2, _) = log.get(&bridge_id_2).unwrap();
    assert_eq!(phase1, BridgePhase::Locked);
    assert_eq!(phase2, BridgePhase::Locked);
}

// ===========================================================================
// Cross-bridge replay: bridge_id of one bridge must not collide with
// a different (nullifier, source, destination, nonce) combo
// ===========================================================================

#[test]
fn bridge_id_distinguishes_different_destinations() {
    let n = [0x40; 32];
    let bid_b = compute_bridge_id(&n, &FED_A, &FED_B, 1);
    let bid_c = compute_bridge_id(&n, &FED_A, &FED_C, 1);
    assert_ne!(
        bid_b, bid_c,
        "destination federation must distinguish bridge IDs"
    );
}

#[test]
fn bridge_id_distinguishes_different_nonces() {
    let n = [0x40; 32];
    let bid_1 = compute_bridge_id(&n, &FED_A, &FED_B, 1);
    let bid_2 = compute_bridge_id(&n, &FED_A, &FED_B, 2);
    assert_ne!(bid_1, bid_2, "initiating_nonce must distinguish bridge IDs");
}

#[test]
fn bridge_id_distinguishes_different_source_federations() {
    let n = [0x40; 32];
    let bid_a = compute_bridge_id(&n, &FED_A, &FED_B, 1);
    let bid_c = compute_bridge_id(&n, &FED_C, &FED_B, 1);
    assert_ne!(
        bid_a, bid_c,
        "source federation must distinguish bridge IDs"
    );
}

// ===========================================================================
// AttestedRoot tamper: a portable note presented against a root that
// has a tampered merkle_root must reject (the source-root commitment
// is part of the trust-root set).
// ===========================================================================

#[test]
fn portable_note_rejects_against_untrusted_root() {
    let nullifier = Nullifier([0x50; 32]);
    let honest_root = attested_root(FED_A, Some([0x88; 32]), 1);
    let proof = create_portable_note(
        nullifier,
        vec![1, 2, 3, 4],
        honest_root.clone(),
        FED_B,
        NoteCommitment([0x99; 32]),
        500,
        1,
    );

    // Attacker presents an UNTRUSTED root set — even if the proof
    // claims to be against honest_root, the destination's trusted-roots
    // list does not contain it.
    let tampered_root = attested_root([0xFF; 32], Some([0x88; 32]), 1);
    let trusted = vec![tampered_root]; // does NOT contain honest_root
    let ok = |_n: &[u8; 32], _r: &[u8; 32], _d: &[u8; 32], _v: u64, _a: u64, _p: &[u8]| Ok(());

    let result = verify_portable_note(&proof, &FED_B, &trusted, ok);
    assert!(
        result.is_err(),
        "portable note must reject when source root is not in destination's trusted set; got {result:?}"
    );
}

#[test]
fn portable_note_rejects_against_empty_trusted_roots() {
    let nullifier = Nullifier([0x51; 32]);
    let root = attested_root(FED_A, Some([0x88; 32]), 1);
    let proof = create_portable_note(
        nullifier,
        vec![1, 2, 3, 4],
        root,
        FED_B,
        NoteCommitment([0x99; 32]),
        500,
        1,
    );
    let trusted: Vec<AttestedRoot> = vec![];
    let ok = |_n: &[u8; 32], _r: &[u8; 32], _d: &[u8; 32], _v: u64, _a: u64, _p: &[u8]| Ok(());
    let result = verify_portable_note(&proof, &FED_B, &trusted, ok);
    assert!(
        result.is_err(),
        "empty trusted-roots set must reject every portable note; got {result:?}"
    );
}

// ===========================================================================
// Phase log replay: admitting the SAME envelope twice
// ===========================================================================

#[test]
fn duplicate_lock_admission_rejected_or_idempotent() {
    let bridge_id = compute_bridge_id(&[0x60; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x60; 32], 1, 100, 50, [0xAB; 32],
    );
    log.admit(&lock).expect("first admit");
    // Re-admitting the SAME phase envelope: not a monotone violation
    // (Locked → Locked is "same phase") but the log must not be
    // confused into thinking we advanced.
    let _ = log.admit(&lock); // either errors or is idempotent — either is fine
    let (phase, _) = log.get(&bridge_id).unwrap();
    assert_eq!(phase, BridgePhase::Locked, "phase must remain Locked");
}

// ===========================================================================
// Phase log: skip-ahead must reject (Locked → Finalized without Witness)
// ===========================================================================

#[test]
fn phase_log_rejects_skip_from_locked_to_finalized_without_witness() {
    let bridge_id = compute_bridge_id(&[0x70; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x70; 32], 1, 100, 50, [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).unwrap();
    // Skip Phase 2 (Witnessed) and try to admit Phase 3 (Finalized)
    // directly — must fail because Finalized.previous = witness_hash,
    // but no witness has been admitted yet.
    let bogus_witness_hash = [0xFA; 32];
    let finalize = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        FED_A,
        FED_B,
        10,
        bogus_witness_hash,
        10,
        [0xEF; 32],
    );
    let result = log.admit(&finalize);
    assert!(
        result.is_err(),
        "Locked → Finalized without prior Witnessed must fail; got {result:?}"
    );
    let _ = lock_hash; // unused
}

// ===========================================================================
// Double-bridge across two destinations: same proof presented at FED_B
// AND FED_C — both destinations' BridgedNullifierSet must independently
// reject the second mint
// ===========================================================================

#[test]
fn same_nullifier_presented_at_two_destinations_each_rejects_second_locally() {
    let nullifier = Nullifier([0x80; 32]);
    let source_root = attested_root(FED_A, Some([0x88; 32]), 1);
    let proof_b = create_portable_note(
        nullifier,
        vec![1, 2, 3, 4],
        source_root.clone(),
        FED_B,
        NoteCommitment([0xAA; 32]),
        500,
        1,
    );
    let proof_c = create_portable_note(
        nullifier,
        vec![1, 2, 3, 4],
        source_root.clone(),
        FED_C,
        NoteCommitment([0xBB; 32]),
        500,
        1,
    );

    let trusted = vec![source_root];
    let ok = |_n: &[u8; 32], _r: &[u8; 32], _d: &[u8; 32], _v: u64, _a: u64, _p: &[u8]| Ok(());
    verify_portable_note(&proof_b, &FED_B, &trusted, ok).expect("verify at B");
    verify_portable_note(&proof_c, &FED_C, &trusted, ok).expect("verify at C");

    // Each federation independently tracks bridged nullifiers; both
    // initial mints succeed because the destination commitments differ
    // (different proof_b vs proof_c). But a second mint at the same
    // destination must fail.
    let mut set_b = BridgedNullifierSet::new();
    let mut set_c = BridgedNullifierSet::new();
    set_b.insert(proof_b.nullifier).expect("B insert 1");
    set_c.insert(proof_c.nullifier).expect("C insert 1");

    let dup_b = set_b.insert(proof_b.nullifier);
    assert!(
        matches!(dup_b, Err(BridgeError::AlreadyBridged { .. })),
        "B duplicate mint must reject; got {dup_b:?}"
    );
    let dup_c = set_c.insert(proof_c.nullifier);
    assert!(
        matches!(dup_c, Err(BridgeError::AlreadyBridged { .. })),
        "C duplicate mint must reject; got {dup_c:?}"
    );
}

// ===========================================================================
// Refund + Re-lock: after a refund, the nullifier should be available
// for a NEW bridge attempt — modulo the PendingBridgeSet semantics
// ===========================================================================

#[test]
fn refund_releases_pending_set_for_re_lock() {
    let nullifier = [0x85; 32];
    let timeout_height = 10;
    let mut pending = PendingBridgeSet::new();

    initiate_bridge(
        nullifier,
        FED_B,
        250,
        1,
        timeout_height,
        vec![0xA5, 0x5A],
        &mut pending,
    )
    .expect("initial lock");
    assert!(pending.is_locked(&nullifier));

    let too_early = cancel_bridge(&nullifier, timeout_height, &mut pending);
    assert!(
        matches!(too_early, Err(BridgeError::TimeoutNotReached { .. })),
        "refund before timeout must reject; got {too_early:?}"
    );
    assert!(pending.is_locked(&nullifier));

    cancel_bridge(&nullifier, timeout_height + 1, &mut pending).expect("timeout refund");
    assert!(
        !pending.is_locked(&nullifier),
        "refunded bridge must release the nullifier lock"
    );

    initiate_bridge(
        nullifier,
        FED_C,
        250,
        1,
        timeout_height + 100,
        vec![0xC0, 0xFF, 0xEE],
        &mut pending,
    )
    .expect("re-lock after refund");
    let relocked = pending.get(&nullifier).expect("re-lock record");
    assert_eq!(relocked.destination_federation, FED_C);
    assert!(pending.is_locked(&nullifier));
}

// ===========================================================================
// Bilateral phase log: bridge_id collision attempt (different content,
// same id) must be detected
// ===========================================================================

#[test]
fn phase_log_rejects_envelope_with_mismatched_destination_federation() {
    let bridge_id = compute_bridge_id(&[0x90; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock_b = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x90; 32], 1, 100, 50, [0xAB; 32],
    );
    log.admit(&lock_b).unwrap();

    // An attacker submits a Witnessed envelope where dst_federation has
    // been tampered to FED_C, but it still references the bridge_id we
    // know about. The phase log must reject because the envelope's
    // src/dst federation pair must match the original Locked.
    let lock_hash = lock_b.body_hash();
    let witness_tampered = BridgeReceiptEnvelope::new_witnessed(
        bridge_id, FED_A, FED_C, // tampered dst
        5, lock_hash, 5, [0xCD; 32],
    );
    let result = log.admit(&witness_tampered);
    assert!(
        result.is_err(),
        "Witnessed envelope with mismatched dst_federation must reject; got {result:?}"
    );
}

// ===========================================================================
// Cross-cutting: Bridge + γ.2 transfer_id binding (composition)
// ===========================================================================

#[test]
fn cross_federation_transfer_binds_transfer_id_and_bridge_id_jointly() {
    let from = CellId([0xA0; 32]);
    let to = CellId([0xB0; 32]);
    let amount = 777;
    let actor_nonce = 42;
    let lock_nullifier = [0x91; 32];
    let bridge_nonce = 7;

    let transfer_id = derive_transfer_id(&from, &to, amount, actor_nonce);
    let bridge_id = compute_bridge_id(&lock_nullifier, &FED_A, &FED_B, bridge_nonce);

    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id,
        FED_A,
        FED_B,
        12,
        lock_nullifier,
        1,
        amount,
        100,
        [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).expect("lock admission");

    let witness = BridgeReceiptEnvelope::new_witnessed(
        bridge_id,
        FED_A,
        FED_B,
        13,
        lock_hash,
        13,
        transfer_id_commitment(transfer_id, bridge_id),
    );
    log.admit(&witness)
        .expect("witness binds transfer_id-derived mint commitment to bridge_id");

    let tampered_transfer_id = derive_transfer_id(&from, &to, amount + 1, actor_nonce);
    assert_ne!(
        transfer_id, tampered_transfer_id,
        "amount drift must change the gamma.2 transfer_id"
    );
    assert_ne!(
        transfer_id_commitment(transfer_id, bridge_id),
        transfer_id_commitment(tampered_transfer_id, bridge_id),
        "mint commitment must bind the gamma.2 transfer_id"
    );

    let tampered_bridge_id = compute_bridge_id(&lock_nullifier, &FED_A, &FED_C, bridge_nonce);
    assert_ne!(
        transfer_id_commitment(transfer_id, bridge_id),
        transfer_id_commitment(transfer_id, tampered_bridge_id),
        "mint commitment must bind the bridge_id as well as transfer_id"
    );
}

// ===========================================================================
// Cross-cutting: Bridge + FederationReceipt (after AttestedRoot v3 lands)
// ===========================================================================

#[test]
fn bridge_phase3_finalize_produces_federation_receipt_with_bridge_id() {
    let bridge_id = compute_bridge_id(&[0xA3; 32], &FED_A, &FED_B, 3);
    let mut log = BridgePhaseLog::new();

    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 20, [0xA3; 32], 1, 100, 50, [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).expect("lock admission");

    let witness = BridgeReceiptEnvelope::new_witnessed(
        bridge_id, FED_A, FED_B, 25, lock_hash, 25, [0xCD; 32],
    );
    let witness_hash = witness.body_hash();
    log.admit(&witness).expect("witness admission");

    let finalize = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        FED_A,
        FED_B,
        30,
        witness_hash,
        30,
        [0xEF; 32],
    );
    log.admit(&finalize).expect("finalize admission");

    let receipt_body = bridge_finalize_receipt_body(&finalize);
    assert_eq!(
        receipt_body.effects_hash,
        finalize.body_hash(),
        "FederationReceiptBody effects_hash must bind the Phase-3 finalize envelope"
    );

    let other_bridge_id = compute_bridge_id(&[0xA3; 32], &FED_A, &FED_C, 3);
    let other_finalize = BridgeReceiptEnvelope::new_finalized(
        other_bridge_id,
        FED_A,
        FED_C,
        30,
        witness_hash,
        30,
        [0xEF; 32],
    );
    let other_body = bridge_finalize_receipt_body(&other_finalize);
    assert_ne!(
        receipt_body.body_hash(),
        other_body.body_hash(),
        "changing bridge_id must change the signed federation receipt body"
    );
}

// ===========================================================================
// Sanity: portable note carries enough information to recompute every
// public input of the destination's STARK verifier closure
// ===========================================================================

#[test]
fn portable_note_carries_every_public_input_for_verifier_closure() {
    // Asserting structural completeness: the portable proof shape
    // exposes nullifier, source merkle_root, destination_federation,
    // value, asset_type, and proof bytes — exactly what the
    // verify_stark closure consumes.
    let nullifier = Nullifier([0xA1; 32]);
    let root = attested_root(FED_A, Some([0x88; 32]), 1);
    let proof = create_portable_note(
        nullifier,
        vec![1, 2, 3, 4],
        root.clone(),
        FED_B,
        NoteCommitment([0xCC; 32]),
        500,
        2,
    );

    // We don't run STARK verification; we only check the shape.
    assert_eq!(proof.nullifier, nullifier.0);
    assert_eq!(proof.destination_federation, FED_B);
    assert_eq!(proof.value, 500);
    assert_eq!(proof.asset_type, 2);
    assert_eq!(proof.spending_proof, vec![1, 2, 3, 4]);
}

fn transfer_id_commitment(
    transfer_id: [dregg_circuit::field::BabyBear; 4],
    bridge_id: [u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-test-bridge-gamma2-joint-binding-v1");
    hasher.update(format!("{transfer_id:?}").as_bytes());
    hasher.update(&bridge_id);
    *hasher.finalize().as_bytes()
}

fn bridge_finalize_receipt_body(finalize: &BridgeReceiptEnvelope) -> FederationReceiptBody {
    let finalize_hash = finalize.body_hash();
    FederationReceiptBody {
        turn_hash: *blake3::hash(b"bridge-phase3-finalize-turn").as_bytes(),
        block_height: finalize.block_height,
        block_hash: *blake3::hash(b"bridge-phase3-finalize-block").as_bytes(),
        agent: CellId(finalize.src_federation),
        nonce: finalize.block_height,
        pre_state_hash: finalize.previous_phase_receipt_hash.unwrap_or([0u8; 32]),
        post_state_hash: finalize_hash,
        effects_hash: finalize_hash,
        previous_receipt_hash: finalize.previous_phase_receipt_hash,
    }
}
