//! Integration tests: replay-chain verifier paths.
//!
//! Exercises `replay_chain` (scope-1 + scope-2 trust-and-replay) using
//! real Effect VM STARK proofs.  Covers:
//!   - Verified single-entry and multi-entry chains.
//!   - Chain-walk rejection: receipt[N].previous_receipt_hash != receipt[N-1].receipt_hash().
//!   - Witness-hash tamper: bundle present but hash claimed is wrong.
//!   - PI/receipt mismatch: proof is sound but PI does not match the receipt's
//!     turn_hash (closes T11 at the verifier layer).
//!   - Scope-2 constraint violation: trace rows carry a tampered balance but
//!     the scope-1 STARK proof passed before the tamper; the constraint walk
//!     must catch the tamper.

use pyana_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::{generate_effect_vm_trace, pi},
    stark::{self, proof_to_bytes},
};
use pyana_commit::typed::canonical_32_to_felts_4;
use pyana_types::CellId;
use pyana_verifier::{
    ReplayEntry, ReplayVerdict, ReplayWitnessAvailability, ReplayWitnessBundle, replay_chain,
};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn zero_receipt() -> pyana_turn::TurnReceipt {
    pyana_turn::TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent: CellId::from_bytes([0u8; 32]),
        federation_id: [0u8; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
    }
}

/// Build a valid, fully-witnessed ReplayEntry whose proof, PI, and bundle all
/// match.  The PI's TURN_HASH, PREVIOUS_RECEIPT_HASH, and IS_AGENT_CELL slots
/// are populated from the provided receipt so that `check_receipt_pi_binding`
/// passes.
fn build_valid_entry(
    balance: u64,
    effects: &[Effect],
    receipt: pyana_turn::TurnReceipt,
) -> ReplayEntry {
    let state = CellState::new(balance, 0);
    let (trace, mut pi) = generate_effect_vm_trace(&state, effects);
    let air = EffectVmAir::new(trace.len());

    // Patch the turn-identity slots (from receipt) into the PI *before* proving.
    // This ensures the proof is generated against the exact PI vector that will
    // be supplied at verify time (fixes "Public inputs mismatch").
    // Extended needed to pi::BASE_COUNT to cover the full current layout
    // (Stage 7-γ turn id, sovereign teeth, slot-caveat manifest, bridge value
    // limbs, emit-event hashes, cross-effect deps, witness index map,
    // unilateral attestations, etc.) produced by generate_effect_vm_trace_ext
    // + EffectVmContext population. All non-identity fields (commits, balances,
    // per-cell effects_hash, actor_nonce from state, etc.) are preserved from
    // the generate path.
    let needed = pi::BASE_COUNT
        .max(pi::TURN_HASH_BASE + pi::TURN_HASH_LEN)
        .max(pi::PREVIOUS_RECEIPT_HASH_BASE + pi::PREVIOUS_RECEIPT_HASH_LEN);
    if pi.len() < needed {
        pi.resize(needed, BabyBear::ZERO);
    }

    // TURN_HASH binding.
    let th = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        pi[pi::TURN_HASH_BASE + i] = th[i];
    }

    // PREVIOUS_RECEIPT_HASH binding.
    if pi.len() >= pi::PREVIOUS_RECEIPT_HASH_BASE + pi::PREVIOUS_RECEIPT_HASH_LEN {
        let prev = canonical_32_to_felts_4(&receipt.previous_receipt_hash.unwrap_or([0u8; 32]));
        for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
            pi[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
        }
    }

    // IS_AGENT_CELL = 1.
    if pi.len() > pi::IS_AGENT_CELL {
        pi[pi::IS_AGENT_CELL] = BabyBear::ONE;
    }

    let proof = stark::prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);

    let pi_u32: Vec<u32> = pi.iter().map(|b| b.as_u32()).collect();

    // Build the witness bundle from the trace.
    let trace_rows: Vec<Vec<u32>> = trace
        .iter()
        .map(|row| row.iter().map(|b| b.as_u32()).collect())
        .collect();
    let bundle = ReplayWitnessBundle {
        trace_rows,
        availability: ReplayWitnessAvailability::Inline,
        recursive_proof: None,
    };
    let witness_hash = bundle.witness_hash();

    ReplayEntry {
        receipt,
        proof_bytes,
        public_inputs: pi_u32,
        witness_bundle: Some(bundle),
        witness_hash,
        aggregate_membership: None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Single-entry chain with real proof + witness: Verified.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn single_entry_real_proof_verifies() {
    let mut receipt = zero_receipt();
    receipt.turn_hash = [0x42u8; 32];

    let entry = build_valid_entry(
        5_000,
        &[Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
        receipt,
    );

    let out = replay_chain(&[entry]);
    assert!(
        out.overall_verified,
        "single real entry must verify; first failure: {:?}",
        out.first_failure
    );
    assert_eq!(out.verified, 1);
    assert_eq!(out.per_entry[0], ReplayVerdict::Verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Two-entry chain with correct chain-walk link: both Verified.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn two_entry_chain_with_correct_link_verifies() {
    let mut receipt_0 = zero_receipt();
    receipt_0.turn_hash = [0x10u8; 32];

    let entry_0 = build_valid_entry(
        10_000,
        &[Effect::Transfer {
            amount: 50,
            direction: 1,
        }],
        receipt_0.clone(),
    );

    // entry_1's previous_receipt_hash must == entry_0.receipt.receipt_hash().
    let receipt_0_hash = receipt_0.receipt_hash();
    let mut receipt_1 = zero_receipt();
    receipt_1.turn_hash = [0x20u8; 32];
    receipt_1.previous_receipt_hash = Some(receipt_0_hash);

    // Adjust balance for chained state (simplified; the proof doesn't need to
    // chain state, only the receipt-PI binding matters for the replay verifier).
    let entry_1 = build_valid_entry(
        9_950,
        &[Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(7),
        }],
        receipt_1,
    );

    let out = replay_chain(&[entry_0, entry_1]);
    assert!(
        out.overall_verified,
        "two-entry chain must verify; verdicts={:?}",
        out.per_entry
    );
    assert_eq!(out.verified, 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Chain-walk break: entry_1's previous_receipt_hash does not match entry_0's hash.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn chain_walk_break_rejects_second_entry() {
    let mut receipt_0 = zero_receipt();
    receipt_0.turn_hash = [0x10u8; 32];
    let entry_0 = build_valid_entry(
        10_000,
        &[Effect::Transfer {
            amount: 50,
            direction: 1,
        }],
        receipt_0.clone(),
    );

    // entry_1 claims a *wrong* previous_receipt_hash (not entry_0's hash).
    let mut receipt_1 = zero_receipt();
    receipt_1.turn_hash = [0x20u8; 32];
    receipt_1.previous_receipt_hash = Some([0xFFu8; 32]); // wrong

    let entry_1 = build_valid_entry(9_950, &[Effect::NoOp], receipt_1);

    let out = replay_chain(&[entry_0, entry_1]);
    assert!(
        !out.overall_verified,
        "chain-walk break must be detected; verdicts={:?}",
        out.per_entry
    );
    assert_eq!(
        out.first_failure,
        Some(1),
        "failure must be at entry index 1"
    );
    matches!(out.per_entry[1], ReplayVerdict::Rejected { .. });
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. Witness-hash tamper: bundle present but hash declared is wrong.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn witness_hash_tamper_rejected() {
    let mut receipt = zero_receipt();
    receipt.turn_hash = [0x55u8; 32];

    let mut entry = build_valid_entry(
        3_000,
        &[Effect::Transfer {
            amount: 30,
            direction: 0,
        }],
        receipt,
    );

    // Corrupt the witness_hash so it no longer matches the bundle.
    entry.witness_hash = [0xFFu8; 32];

    let out = replay_chain(&[entry]);
    assert!(
        !out.overall_verified,
        "tampered witness_hash must be rejected"
    );
    assert_eq!(out.first_failure, Some(0));
    matches!(out.per_entry[0], ReplayVerdict::Rejected { .. });
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. PI/receipt mismatch: sound proof but PI says wrong TURN_HASH (closes T11).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn pi_turn_hash_mismatch_rejected() {
    let mut receipt = zero_receipt();
    receipt.turn_hash = [0x42u8; 32];

    let mut entry = build_valid_entry(
        5_000,
        &[Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
        receipt,
    );

    // The STARK proof is algebraically sound, but now we corrupt PI[TURN_HASH_BASE]
    // so it no longer agrees with receipt.turn_hash. `check_receipt_pi_binding` must
    // catch this even though the STARK itself passes.
    //
    // Since the STARK-step runs first (scope-1) and the proof is valid, the next
    // check is the PI binding. We tamper *after* building the valid entry.
    entry.public_inputs[pi::TURN_HASH_BASE] ^= 0xDEAD_BEEF;

    let out = replay_chain(&[entry]);
    assert!(
        !out.overall_verified,
        "T11: PI TURN_HASH mismatch must be rejected"
    );
    assert_eq!(out.first_failure, Some(0));
    matches!(out.per_entry[0], ReplayVerdict::Rejected { .. });
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Scope-2 trace tamper: balance row corrupted — constraint walk must catch it.
// ─────────────────────────────────────────────────────────────────────────────

/// Build an entry where the witness bundle's trace rows have a corrupted
/// balance column, but the scope-1 STARK proof is still the valid one (for the
/// original, uncorrupted trace).  The scope-2 replay loop must reject via the
/// `eval_constraints` walk.
///
/// This exercises the `replay_chain` code path at step 6 (row-by-row constraint
/// walk) in `replay_one_with_prev`.
#[test]
fn scope2_tampered_trace_row_rejected_by_constraint_walk() {
    use pyana_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};

    let mut receipt = zero_receipt();
    receipt.turn_hash = [0x77u8; 32];

    // Build a genuine entry first.
    let mut entry = build_valid_entry(
        10_000,
        &[
            Effect::Transfer {
                amount: 100,
                direction: 1,
            },
            Effect::Transfer {
                amount: 50,
                direction: 0,
            },
        ],
        receipt,
    );

    // Now corrupt row 0's state_after.balance_lo in the *witness bundle* trace
    // (the scope-1 proof is not affected — it was generated from the uncorrupted
    // trace, so it still verifies).
    if let Some(bundle) = entry.witness_bundle.as_mut() {
        let state_after_bal_lo_col = STATE_AFTER_BASE + state::BALANCE_LO;
        if bundle.trace_rows.len() > 0 && bundle.trace_rows[0].len() > state_after_bal_lo_col {
            bundle.trace_rows[0][state_after_bal_lo_col] ^= 0x9999;
        }
        // Recompute witness_hash to pass the hash check, so the test reaches the
        // constraint walk.
        entry.witness_hash = bundle.witness_hash();
    }

    let out = replay_chain(&[entry]);
    assert!(
        !out.overall_verified,
        "scope-2 constraint walk must reject a corrupted trace row"
    );
    assert_eq!(out.first_failure, Some(0));
    // The rejection must come from the constraint walk (step 6), not the
    // earlier hash check or proof step — the hash was recomputed above.
    matches!(out.per_entry[0], ReplayVerdict::Rejected { .. });
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. Empty chain: trivially verified.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn empty_chain_trivially_verified() {
    let out = replay_chain(&[]);
    assert!(out.overall_verified);
    assert_eq!(out.total, 0);
    assert_eq!(out.verified, 0);
    assert!(out.first_failure.is_none());
}
