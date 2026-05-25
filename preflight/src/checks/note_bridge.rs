//! Preflight: bridge phase-log + portable-note sanity checks.
//!
//! Layer: lightweight. These checks exist so that if any of the
//! `pyana_cell::note_bridge` invariants regress, the whole heavier
//! bridge suite is short-circuited at preflight time.
//!
//! See `teasting/tests/bridge_four_phase.rs` (existing happy/adversarial
//! integration) and `teasting/tests/bridge_four_phase_extended.rs`
//! (extended adversarial coverage). This preflight is a quick smoke
//! test, not exhaustive.

use pyana_cell::note::{NoteCommitment, Nullifier};
use pyana_cell::note_bridge::{
    BridgePhase, BridgePhaseError, BridgePhaseLog, BridgeReceiptEnvelope, BridgedNullifierSet,
    PendingBridgeSet, compute_bridge_id, create_portable_note, initiate_bridge,
    verify_portable_note,
};
use pyana_types::{AttestedRoot, FederationId};

use crate::report::{CheckResult, run_check};

const FED_A: [u8; 32] = [0xAA; 32];
const FED_B: [u8; 32] = [0xBB; 32];
const FED_C: [u8; 32] = [0xCC; 32];

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check(
            "bridge_id_distinguishes_destinations",
            check_bridge_id_distinguishes_destinations,
        ),
        run_check(
            "bridge_id_distinguishes_nonces",
            check_bridge_id_distinguishes_nonces,
        ),
        run_check(
            "phase_log_locked_to_witnessed_to_finalized_ok",
            check_phase_log_happy,
        ),
        run_check(
            "phase_log_rejects_finalize_then_refund",
            check_phase_log_rejects_late_refund,
        ),
        run_check(
            "phase_log_rejects_witness_after_refund",
            check_phase_log_rejects_witness_after_refund,
        ),
        run_check(
            "pending_set_rejects_relock",
            check_pending_set_rejects_relock,
        ),
        run_check(
            "bridged_nullifier_set_rejects_double_mint",
            check_bridged_nullifier_set_rejects_double_mint,
        ),
        run_check(
            "portable_note_rejects_untrusted_destination",
            check_portable_note_rejects_untrusted_destination,
        ),
    ]
}

fn attested_root() -> AttestedRoot {
    AttestedRoot {
        merkle_root: FED_A,
        note_tree_root: Some([0x77; 32]),
        nullifier_set_root: None,
        height: 1,
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

fn check_bridge_id_distinguishes_destinations() -> Result<(), String> {
    let n = [0x40; 32];
    let bid_b = compute_bridge_id(&n, &FED_A, &FED_B, 1);
    let bid_c = compute_bridge_id(&n, &FED_A, &FED_C, 1);
    if bid_b == bid_c {
        Err("destination federation MUST distinguish bridge IDs".into())
    } else {
        Ok(())
    }
}

fn check_bridge_id_distinguishes_nonces() -> Result<(), String> {
    let n = [0x40; 32];
    let bid_1 = compute_bridge_id(&n, &FED_A, &FED_B, 1);
    let bid_2 = compute_bridge_id(&n, &FED_A, &FED_B, 2);
    if bid_1 == bid_2 {
        Err("nonce MUST distinguish bridge IDs".into())
    } else {
        Ok(())
    }
}

fn check_phase_log_happy() -> Result<(), String> {
    let bridge_id = compute_bridge_id(&[0x10; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x10; 32], 1, 100, 50, [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).map_err(|e| format!("lock admit: {e:?}"))?;
    let witness =
        BridgeReceiptEnvelope::new_witnessed(bridge_id, FED_A, FED_B, 5, lock_hash, 5, [0xCD; 32]);
    let witness_hash = witness.body_hash();
    log.admit(&witness)
        .map_err(|e| format!("witness admit: {e:?}"))?;
    let finalize = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        FED_A,
        FED_B,
        10,
        witness_hash,
        10,
        [0xEF; 32],
    );
    log.admit(&finalize)
        .map_err(|e| format!("finalize admit: {e:?}"))?;
    let (phase, _) = log.get(&bridge_id).ok_or("bridge_id missing")?;
    if phase == BridgePhase::Finalized {
        Ok(())
    } else {
        Err(format!("expected Finalized, got {phase:?}"))
    }
}

fn check_phase_log_rejects_late_refund() -> Result<(), String> {
    let bridge_id = compute_bridge_id(&[0x11; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x11; 32], 1, 100, 50, [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).map_err(|e| format!("{e:?}"))?;
    let witness =
        BridgeReceiptEnvelope::new_witnessed(bridge_id, FED_A, FED_B, 5, lock_hash, 5, [0xCD; 32]);
    let witness_hash = witness.body_hash();
    log.admit(&witness).map_err(|e| format!("{e:?}"))?;
    let finalize = BridgeReceiptEnvelope::new_finalized(
        bridge_id,
        FED_A,
        FED_B,
        10,
        witness_hash,
        10,
        [0xEF; 32],
    );
    log.admit(&finalize).map_err(|e| format!("{e:?}"))?;
    let refund = BridgeReceiptEnvelope::new_refunded(bridge_id, FED_A, FED_B, 100, lock_hash, 100);
    match log.admit(&refund) {
        Err(BridgePhaseError::NonMonotoneAdvancement { .. }) => Ok(()),
        Err(e) => Err(format!(
            "expected NonMonotoneAdvancement, got other error: {e:?}"
        )),
        Ok(_) => Err("refund after finalize MUST reject".into()),
    }
}

fn check_phase_log_rejects_witness_after_refund() -> Result<(), String> {
    let bridge_id = compute_bridge_id(&[0x12; 32], &FED_A, &FED_B, 1);
    let mut log = BridgePhaseLog::new();
    let lock = BridgeReceiptEnvelope::new_locked(
        bridge_id, FED_A, FED_B, 2, [0x12; 32], 1, 100, 50, [0xAB; 32],
    );
    let lock_hash = lock.body_hash();
    log.admit(&lock).map_err(|e| format!("{e:?}"))?;
    let refund = BridgeReceiptEnvelope::new_refunded(bridge_id, FED_A, FED_B, 60, lock_hash, 60);
    log.admit(&refund).map_err(|e| format!("{e:?}"))?;
    let late_witness =
        BridgeReceiptEnvelope::new_witnessed(bridge_id, FED_A, FED_B, 100, lock_hash, 100, [0; 32]);
    match log.admit(&late_witness) {
        Err(BridgePhaseError::NonMonotoneAdvancement { .. }) => Ok(()),
        Err(e) => Err(format!("expected NonMonotoneAdvancement, got {e:?}")),
        Ok(_) => Err("witness after refund MUST reject".into()),
    }
}

fn check_pending_set_rejects_relock() -> Result<(), String> {
    let n = [0x21; 32];
    let mut pending = PendingBridgeSet::new();
    initiate_bridge(n, FED_B, 100, 1, 50, vec![1], &mut pending)
        .map_err(|e| format!("first lock: {e:?}"))?;
    if !pending.is_locked(&n) {
        return Err("nullifier not locked after initiate".into());
    }
    let result = initiate_bridge(n, FED_C, 200, 1, 50, vec![2], &mut pending);
    if result.is_ok() {
        Err("re-locking to different destination MUST fail".into())
    } else {
        Ok(())
    }
}

fn check_bridged_nullifier_set_rejects_double_mint() -> Result<(), String> {
    let n = [0x33; 32];
    let mut set = BridgedNullifierSet::new();
    set.insert(n).map_err(|e| format!("first insert: {e:?}"))?;
    let dup = set.insert(n);
    if dup.is_err() {
        Ok(())
    } else {
        Err("duplicate insert MUST fail".into())
    }
}

fn check_portable_note_rejects_untrusted_destination() -> Result<(), String> {
    let nullifier = Nullifier([0x44; 32]);
    let proof = create_portable_note(
        nullifier,
        vec![1, 2, 3],
        attested_root(),
        FED_B,
        NoteCommitment([0x55; 32]),
        500,
        1,
    );
    let trusted = vec![attested_root()];
    let ok = |_n: &[u8; 32], _r: &[u8; 32], _d: &[u8; 32], _v: u64, _a: u64, _p: &[u8]| Ok(());
    // Present at FED_C (not the destination) — must reject.
    let result = verify_portable_note(&proof, &FED_C, &trusted, ok);
    if result.is_err() {
        Ok(())
    } else {
        Err("proof addressed to FED_B presented to FED_C MUST reject".into())
    }
}
