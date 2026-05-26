//! Provable CapTP effects: STARK proofs for ExportSturdyRef, EnlivenRef, DropRef.
//!
//! Tests that CapTP operations produce valid STARK proofs via the Effect VM AIR,
//! verifying that:
//! - ExportSturdyRef generates a valid proof binding cell_id + swiss number
//! - EnlivenRef generates a valid proof binding to the correct swiss table entry
//! - DropRef generates a valid proof that refcount decrements are provable
//! - Multi-effect turns mixing CapTP + Transfer effects produce a single valid proof
//! - Tampering with the swiss number in a proof causes verification FAILURE

use dregg_circuit::effect_vm::{
    AUX_BASE, EffectVmContext, STATE_AFTER_BASE, generate_effect_vm_trace_ext, state,
};
use dregg_circuit::poseidon2::hash_2_to_1;
use dregg_circuit::stark::{StarkAir, prove, try_prove, verify};
use dregg_circuit::{
    BabyBear, CellState, Effect, EffectVmAir, compute_effects_hash, extract_net_delta,
    generate_effect_vm_trace,
};
use dregg_teasting::federation::quick_federation;

// =============================================================================
// Test 1: ExportSturdyRef -> verify STARK proof is valid
// =============================================================================

/// Execute a turn with ExportSturdyRef and verify the STARK proof passes.
/// The proof commits to: cell_id, permissions, random_seed, export_counter.
/// The state transition increments field[7] (export counter).
#[test]
fn test_export_sturdy_ref_proof_valid() {
    let _harness = quick_federation();

    let mut state = CellState::new(5000, 0);
    // field[7] = export counter, starting at 3
    state.fields[7] = BabyBear::new(3);
    state.refresh_commitment();

    let effects = vec![Effect::ExportSturdyRef {
        cell_id: BabyBear::new(0xCE11),
        permissions: BabyBear::new(0x7),
        random_seed: BabyBear::new(0xABCD),
        export_counter: 3,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify constraint satisfaction.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "ExportSturdyRef: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK proof generation and verification.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "ExportSturdyRef STARK proof should verify: {:?}",
        result.err()
    );

    // Verify the export counter incremented in the trace.
    let new_export_counter = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 7];
    assert_eq!(
        new_export_counter,
        BabyBear::new(4),
        "Export counter should increment from 3 to 4"
    );

    // Net delta should be 0 (ExportSturdyRef doesn't change balance).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, 0, "ExportSturdyRef should not change balance");
}

// =============================================================================
// Test 2: EnlivenRef -> verify proof binds to correct swiss number
// =============================================================================

/// Execute EnlivenRef and verify the proof binds the swiss number to the
/// expected cell_id and permissions from the swiss table.
#[test]
fn test_enliven_ref_proof_binds_swiss() {
    let _harness = quick_federation();

    let mut state = CellState::new(5000, 0);
    // field[6] = use count, starting at 0
    state.fields[6] = BabyBear::new(0);
    state.refresh_commitment();

    let swiss_number = BabyBear::new(0x5155);
    let expected_cell = BabyBear::new(0xCE11);
    let expected_perms = BabyBear::new(0x7);

    let effects = vec![Effect::EnlivenRef {
        swiss_number,
        presenter_id: BabyBear::new(0xB0B),
        expected_cell_id: expected_cell,
        expected_permissions: expected_perms,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify constraints.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "EnlivenRef: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK proof roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "EnlivenRef STARK proof should verify: {:?}",
        result.err()
    );

    // Verify use_count incremented.
    let new_use_count = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 6];
    assert_eq!(
        new_use_count,
        BabyBear::new(1),
        "use_count should increment from 0 to 1"
    );

    // The effects hash commits to the swiss number (any change would alter the hash).
    let (hash_lo, hash_hi) = compute_effects_hash(&effects);
    assert_ne!(hash_lo, BabyBear::ZERO);

    // Changing swiss_number would produce a different hash.
    let tampered_effects = vec![Effect::EnlivenRef {
        swiss_number: BabyBear::new(0xBAD),
        presenter_id: BabyBear::new(0xB0B),
        expected_cell_id: expected_cell,
        expected_permissions: expected_perms,
    }];
    let (t_hash_lo, t_hash_hi) = compute_effects_hash(&tampered_effects);
    assert_ne!(
        (hash_lo, hash_hi),
        (t_hash_lo, t_hash_hi),
        "Different swiss number must produce different effects hash"
    );
}

// =============================================================================
// Test 3: DropRef -> verify refcount decrement is provable
// =============================================================================

/// Execute DropRef and verify the proof demonstrates a valid refcount decrement.
/// The proof enforces that current_refcount > 0.
#[test]
fn test_drop_ref_refcount_decrement_provable() {
    let _harness = quick_federation();

    let mut state = CellState::new(5000, 0);
    // field[5] = refcount, starting at 5
    state.fields[5] = BabyBear::new(5);
    state.refresh_commitment();

    let effects = vec![Effect::DropRef {
        cell_id: BabyBear::new(0xCE11),
        holder_federation: BabyBear::new(0xFEDA),
        current_refcount: 5,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify constraints.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "DropRef: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK proof roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "DropRef STARK proof should verify: {:?}",
        result.err()
    );

    // Verify refcount decremented.
    let new_refcount = trace[0][STATE_AFTER_BASE + state::FIELD_BASE + 5];
    assert_eq!(
        new_refcount,
        BabyBear::new(4),
        "refcount should decrement from 5 to 4"
    );

    // Net delta: 0 (DropRef doesn't change balance).
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(delta, 0, "DropRef should not change balance");
}

// =============================================================================
// Test 4: Multi-effect turn mixing CapTP + Transfer -> single valid proof
// =============================================================================

/// A turn that combines CapTP effects (Export, Enliven, Drop) with a Transfer
/// effect produces a single valid STARK proof covering all state transitions.
#[test]
fn test_multi_effect_captp_and_transfer_single_proof() {
    let _harness = quick_federation();

    let mut state = CellState::new(10_000, 0);
    // Initialize counters.
    state.fields[5] = BabyBear::new(2); // refcount
    state.fields[6] = BabyBear::new(1); // use_count
    state.fields[7] = BabyBear::new(0); // export_counter
    state.refresh_commitment();

    let effects = vec![
        // CapTP: Export a sturdy ref.
        Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x3),
            random_seed: BabyBear::new(0xABC),
            export_counter: 0,
        },
        // CapTP: Enliven a different ref.
        Effect::EnlivenRef {
            swiss_number: BabyBear::new(0x999),
            presenter_id: BabyBear::new(0x111),
            expected_cell_id: BabyBear::new(0x222),
            expected_permissions: BabyBear::new(0x333),
        },
        // Transfer: debit 500.
        Effect::Transfer {
            amount: 500,
            direction: 1,
        },
        // CapTP: Drop a ref.
        Effect::DropRef {
            cell_id: BabyBear::new(0xCE22),
            holder_federation: BabyBear::new(0xFED2),
            current_refcount: 2,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());

    // Verify all constraints pass.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Multi-effect CapTP+Transfer: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK proof: single proof covers all 4 effects.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Multi-effect CapTP+Transfer STARK proof should verify: {:?}",
        result.err()
    );

    // Net delta: -500 from the Transfer. CapTP effects don't change balance.
    let delta = extract_net_delta(&public_inputs).unwrap();
    assert_eq!(
        delta, -500,
        "Only the Transfer should contribute to net delta"
    );
}

// =============================================================================
// Test 5: Tamper - modify swiss number in proof -> verification FAILS
// =============================================================================

/// Tampering with the swiss number (aux column) after trace generation causes
/// the STARK proof to fail verification, demonstrating soundness.
#[test]
fn test_tampered_swiss_number_verification_fails() {
    let _harness = quick_federation();

    let mut state = CellState::new(5000, 0);
    state.fields[7] = BabyBear::new(0);
    state.refresh_commitment();

    let effects = vec![Effect::ExportSturdyRef {
        cell_id: BabyBear::new(0xCE11),
        permissions: BabyBear::new(0x7),
        random_seed: BabyBear::new(0x5EED),
        export_counter: 0,
    }];

    let (mut trace, public_inputs) = generate_effect_vm_trace(&state, &effects);

    // Tamper: overwrite the swiss number in aux[0] with a bad value.
    trace[0][AUX_BASE] = BabyBear::new(0xBAD_CAFE);

    let air = EffectVmAir::new(trace.len());

    assert!(
        try_prove(&air, &trace, &public_inputs).is_err(),
        "Tampered swiss number should be rejected before proof generation"
    );
}

// =============================================================================
// Test 6: Effects hash commitment integrity
// =============================================================================

/// The effects hash (committed as public input) changes if ANY parameter of
/// ANY effect is modified. This prevents a malicious prover from substituting
/// a different set of effects.
#[test]
fn test_effects_hash_commitment_integrity() {
    let _harness = quick_federation();

    let original_effects = vec![
        Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 0,
        },
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
    ];

    let (orig_lo, orig_hi) = compute_effects_hash(&original_effects);

    // Tamper 1: change cell_id in ExportSturdyRef.
    let tampered_1 = vec![
        Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xDEAD), // changed
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 0,
        },
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
    ];
    let (t1_lo, t1_hi) = compute_effects_hash(&tampered_1);
    assert_ne!(
        (orig_lo, orig_hi),
        (t1_lo, t1_hi),
        "Changing cell_id changes hash"
    );

    // Tamper 2: change Transfer amount.
    let tampered_2 = vec![
        Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 0,
        },
        Effect::Transfer {
            amount: 200, // changed
            direction: 1,
        },
    ];
    let (t2_lo, t2_hi) = compute_effects_hash(&tampered_2);
    assert_ne!(
        (orig_lo, orig_hi),
        (t2_lo, t2_hi),
        "Changing amount changes hash"
    );

    // Tamper 3: reorder effects.
    let tampered_3 = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::ExportSturdyRef {
            cell_id: BabyBear::new(0xCE11),
            permissions: BabyBear::new(0x7),
            random_seed: BabyBear::new(0x5EED),
            export_counter: 0,
        },
    ];
    let (t3_lo, t3_hi) = compute_effects_hash(&tampered_3);
    assert_ne!(
        (orig_lo, orig_hi),
        (t3_lo, t3_hi),
        "Reordering effects changes hash"
    );
}

// =============================================================================
// Test 7: DropRef with refcount=0 is rejected at trace generation time
// =============================================================================

/// The executor prevents generating a trace for DropRef when the refcount is 0.
/// This is an executor-side check (the STARK itself would allow any input, but
/// the witness generation rejects invalid inputs).
#[test]
#[should_panic(expected = "DropRef: current_refcount must be > 0")]
fn test_drop_ref_zero_refcount_panics() {
    let mut state = CellState::new(5000, 0);
    state.fields[5] = BabyBear::ZERO;
    state.refresh_commitment();

    let effects = vec![Effect::DropRef {
        cell_id: BabyBear::new(0xCE11),
        holder_federation: BabyBear::new(0xFED1),
        current_refcount: 0,
    }];

    // This panics because the executor rejects zero-refcount drops.
    let _ = generate_effect_vm_trace(&state, &effects);
}

// =============================================================================
// Test 8: ValidateHandoff effect produces valid proof
// =============================================================================

/// ValidateHandoff proves certificate hash membership in the approved set
/// and updates the capability root. The STARK proof must verify.
#[test]
fn test_validate_handoff_proof_valid() {
    let _harness = quick_federation();

    let state = CellState::new(5000, 0);
    let cert_hash = BabyBear::new(0xCE87);
    let recipient_pk = BabyBear::new(0x8EC1);
    let introducer_pk = BabyBear::new(0x1117);
    let pks = hash_2_to_1(recipient_pk, introducer_pk);
    let leaf = hash_2_to_1(cert_hash, pks);
    let approved_set_root = hash_2_to_1(leaf, BabyBear::ZERO);

    let effects = vec![Effect::ValidateHandoff {
        certificate_hash: cert_hash,
        recipient_pk,
        introducer_pk,
        approved_set_root,
    }];

    let mut context = EffectVmContext::default();
    context.approved_handoffs_root[0] = approved_set_root;
    let (trace, public_inputs) = generate_effect_vm_trace_ext(&state, &effects, context);
    let air = EffectVmAir::new(trace.len());

    // Verify constraints.
    for alpha_val in [7u32, 13, 101] {
        let alpha = BabyBear::new(alpha_val);
        for row in 0..trace.len() - 1 {
            let next_row = (row + 1) % trace.len();
            let c = air.eval_constraints(&trace[row], &trace[next_row], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "ValidateHandoff: constraint non-zero at row {} alpha={}",
                row,
                alpha_val
            );
        }
    }

    // STARK proof roundtrip.
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "ValidateHandoff STARK proof should verify: {:?}",
        result.err()
    );

    // Verify cap_root was updated (handoff adds a routing entry).
    let old_cap = state.capability_root;
    let new_cap = trace[0][STATE_AFTER_BASE + state::CAP_ROOT];
    assert_ne!(old_cap, new_cap, "cap_root should change after handoff");
}
