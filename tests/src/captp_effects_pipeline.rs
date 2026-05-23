//! CapTP effects pipeline: full end-to-end tests proving CapTP operations
//! (ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff) via the Effect VM
//! with real STARK proofs.
//!
//! These tests verify:
//! - Each CapTP effect type produces a valid trace that passes constraint checking
//! - The STARK proof verifies correctly
//! - Tampered traces fail verification
//! - Multiple CapTP effects can be combined in a single turn/proof

use pyana_circuit::effect_vm::{
    self, CellState, Effect, EffectVmAir, compute_effects_hash, generate_effect_vm_trace,
};
use pyana_circuit::field::BabyBear;
use pyana_circuit::poseidon2::hash_2_to_1;
use pyana_circuit::stark::{self, StarkProof};

// =============================================================================
// Helper functions
// =============================================================================

/// Create a cell state with a given refcount (field[5]), use_count (field[6]),
/// and export_counter (field[7]).
fn captp_cell_state(balance: u64, refcount: u32, use_count: u32, export_counter: u32) -> CellState {
    let mut state = CellState::new(balance, 0);
    state.fields[5] = BabyBear::new(refcount);
    state.fields[6] = BabyBear::new(use_count);
    state.fields[7] = BabyBear::new(export_counter);
    state.refresh_commitment();
    state
}

/// Prove and verify a set of effects against an initial state. Returns the proof.
fn prove_and_verify_effects(initial_state: &CellState, effects: &[Effect]) -> StarkProof {
    let (trace, public_inputs) = generate_effect_vm_trace(initial_state, effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let result = stark::verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "STARK verification failed: {:?}",
        result.err()
    );
    proof
}

// =============================================================================
// Test 1: ExportSturdyRef
// =============================================================================

/// Create cell -> export as sturdy ref -> STARK proof -> verify.
/// The export effect:
///   - Computes swiss_number = hash(cell_id, hash(random_seed, export_counter))
///   - Increments field[7] (export counter)
///   - Leaves balance and other fields unchanged
#[test]
fn test_export_sturdy_ref_full_pipeline() {
    let initial_state = captp_cell_state(10_000, 3, 0, 0);

    let cell_id = BabyBear::new(0xCAFE);
    let permissions = BabyBear::new(0x07); // read+write+exec
    let random_seed = BabyBear::new(0xDEAD_BEEF);
    let export_counter = 0u32;

    let effects = vec![Effect::ExportSturdyRef {
        cell_id,
        permissions,
        random_seed,
        export_counter,
    }];

    // Generate trace and verify constraints.
    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify the trace captures the state transition correctly.
    // After export: field[7] should be 1 (was 0, incremented).
    let last_real_row = &trace[0];
    let new_f7 = last_real_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 7];
    assert_eq!(
        new_f7,
        BabyBear::ONE,
        "export_counter (field[7]) should increment to 1"
    );

    // The computed swiss number should be in aux[0].
    let inner_hash = hash_2_to_1(random_seed, BabyBear::new(export_counter));
    let expected_swiss = hash_2_to_1(cell_id, inner_hash);
    let aux_swiss = last_real_row[effect_vm::AUX_BASE + 0];
    assert_eq!(
        aux_swiss, expected_swiss,
        "aux[0] should contain the computed swiss number"
    );

    // Prove via real STARK.
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    assert!(proof.trace_len >= 2);
    assert!(!proof.query_proofs.is_empty());

    // Verify.
    let result = stark::verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Export proof should verify: {:?}",
        result.err()
    );

    // Tamper: flip a trace value in the proof -> verification fails.
    let mut tampered = proof.clone();
    if !tampered.query_proofs.is_empty() && !tampered.query_proofs[0].trace_values.is_empty() {
        tampered.query_proofs[0].trace_values[0] ^= 0xBEEF;
    }
    let tampered_result = stark::verify(&air, &tampered, &public_inputs);
    assert!(
        tampered_result.is_err(),
        "Tampered export proof should fail verification"
    );
}

// =============================================================================
// Test 2: EnlivenRef
// =============================================================================

/// Given a valid swiss number -> enliven -> proof binds correctly.
/// The enliven effect:
///   - Verifies hash(swiss, hash(cell_id, permissions)) matches table entry
///   - Increments field[6] (use_count)
///   - Leaves balance and other fields unchanged
#[test]
fn test_enliven_ref_full_pipeline() {
    let initial_state = captp_cell_state(5_000, 2, 0, 5);

    let cell_id = BabyBear::new(0x1234);
    let permissions = BabyBear::new(0x03); // read+write
    let presenter_id = BabyBear::new(0xAABB);

    // Compute the swiss number that would have been created by an export.
    // For enliven, we need a swiss number that resolves to (cell_id, permissions).
    let random_seed = BabyBear::new(0xFEED);
    let counter = BabyBear::new(42);
    let inner_export = hash_2_to_1(random_seed, counter);
    let swiss_number = hash_2_to_1(cell_id, inner_export);

    let effects = vec![Effect::EnlivenRef {
        swiss_number,
        presenter_id,
        expected_cell_id: cell_id,
        expected_permissions: permissions,
    }];

    let (trace, _public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify state transition: field[6] (use_count) incremented.
    let row = &trace[0];
    let new_f6 = row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 6];
    assert_eq!(
        new_f6,
        BabyBear::ONE,
        "use_count (field[6]) should increment to 1"
    );

    // Verify the entry hash in aux[0].
    let inner = hash_2_to_1(cell_id, permissions);
    let expected_entry_hash = hash_2_to_1(swiss_number, inner);
    let aux_entry = row[effect_vm::AUX_BASE + 0];
    assert_eq!(
        aux_entry, expected_entry_hash,
        "aux[0] should contain the entry hash binding swiss to (cell_id, permissions)"
    );

    // Prove and verify via STARK.
    let proof = prove_and_verify_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);
}

// =============================================================================
// Test 3: DropRef
// =============================================================================

/// Hold ref -> drop -> proof shows decrement -> verify.
/// The DropRef effect:
///   - Proves refcount > 0 (via inverse witness)
///   - Decrements field[5] (refcount)
///   - Leaves balance and other fields unchanged
#[test]
fn test_drop_ref_full_pipeline() {
    // Start with refcount = 3.
    let initial_state = captp_cell_state(8_000, 3, 1, 2);

    let cell_id = BabyBear::new(0x5678);
    let holder_federation = BabyBear::new(0xFED1);

    let effects = vec![Effect::DropRef {
        cell_id,
        holder_federation,
        current_refcount: 3, // Must match field[5].
    }];

    let (trace, _public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify state: field[5] decremented from 3 to 2.
    let row = &trace[0];
    let old_f5 = row[effect_vm::STATE_BEFORE_BASE + effect_vm::state::FIELD_BASE + 5];
    let new_f5 = row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 5];
    assert_eq!(old_f5, BabyBear::new(3), "old refcount should be 3");
    assert_eq!(new_f5, BabyBear::new(2), "new refcount should be 2");

    // Verify the non-zero proof: aux[0] = inverse(refcount).
    let rc_inv = row[effect_vm::AUX_BASE + 0];
    let rc_field = BabyBear::new(3);
    assert_eq!(
        rc_field * rc_inv,
        BabyBear::ONE,
        "aux[0] should be modular inverse of refcount (proves > 0)"
    );

    // Prove and verify via STARK.
    let proof = prove_and_verify_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);

    // Verify that a zero refcount would be rejected at trace generation time.
    let zero_rc_state = captp_cell_state(8_000, 0, 1, 2);
    let result = std::panic::catch_unwind(|| {
        generate_effect_vm_trace(
            &zero_rc_state,
            &[Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount: 0,
            }],
        );
    });
    assert!(
        result.is_err(),
        "DropRef with refcount=0 should panic at trace generation"
    );
}

// =============================================================================
// Test 4: ValidateHandoff
// =============================================================================

/// Create handoff cert -> validate -> proof shows membership.
/// The ValidateHandoff effect:
///   - Proves certificate_hash is in the approved set via hash(cert, approved_root)
///   - Updates cap_root with routing entry: hash(old_cap, hash(recipient_pk, cert_hash))
///   - Leaves balance and fields unchanged
#[test]
fn test_validate_handoff_full_pipeline() {
    let initial_state = captp_cell_state(12_000, 1, 0, 0);

    let certificate_hash = BabyBear::new(0xCE27);
    let recipient_pk = BabyBear::new(0xBBCC);
    let introducer_pk = BabyBear::new(0xDDEE);
    let approved_set_root = BabyBear::new(0xA55E);

    let effects = vec![Effect::ValidateHandoff {
        certificate_hash,
        recipient_pk,
        introducer_pk,
        approved_set_root,
    }];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify membership binding in aux[0].
    let row = &trace[0];
    let expected_membership = hash_2_to_1(certificate_hash, approved_set_root);
    let aux_membership = row[effect_vm::AUX_BASE + 0];
    assert_eq!(
        aux_membership, expected_membership,
        "aux[0] should bind cert to approved set"
    );

    // Verify cap_root update.
    let old_cap = row[effect_vm::STATE_BEFORE_BASE + effect_vm::state::CAP_ROOT];
    let new_cap = row[effect_vm::STATE_AFTER_BASE + effect_vm::state::CAP_ROOT];
    let routing_entry = hash_2_to_1(recipient_pk, certificate_hash);
    let expected_new_cap = hash_2_to_1(old_cap, routing_entry);
    assert_eq!(
        new_cap, expected_new_cap,
        "cap_root should incorporate the new routing entry"
    );

    // Prove and verify via STARK.
    let proof = prove_and_verify_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);

    // Tamper with the proof: change a constraint value -> fails.
    let air = EffectVmAir::new(proof.trace_len);
    let mut tampered = proof.clone();
    if !tampered.query_proofs.is_empty() {
        tampered.query_proofs[0].constraint_value ^= 0xDEAD;
    }
    let tampered_result = stark::verify(&air, &tampered, &public_inputs);
    assert!(
        tampered_result.is_err(),
        "Tampered handoff proof should fail verification"
    );
}

// =============================================================================
// Test 5: Multi-effect turn (Transfer + ExportSturdyRef + DropRef)
// =============================================================================

/// Transfer + ExportSturdyRef + DropRef in one turn -> single STARK proof covers all.
/// Proves the Effect VM can handle heterogeneous CapTP + non-CapTP effects in a
/// single proof with correct state threading between rows.
#[test]
fn test_multi_effect_captp_turn() {
    // Initial state: balance=50000, refcount=5, use_count=2, export_counter=3.
    let initial_state = captp_cell_state(50_000, 5, 2, 3);

    let cell_id_export = BabyBear::new(0xAAAA);
    let permissions_export = BabyBear::new(0x0F);
    let random_seed = BabyBear::new(0x1337);
    let export_counter = 3u32; // Must match field[7].

    let cell_id_drop = BabyBear::new(0xBBBB);
    let holder_fed = BabyBear::new(0xFED2);

    let effects = vec![
        // Effect 1: Transfer 1000 outgoing.
        Effect::Transfer {
            amount: 1000,
            direction: 1, // outgoing
        },
        // Effect 2: Export sturdy ref.
        Effect::ExportSturdyRef {
            cell_id: cell_id_export,
            permissions: permissions_export,
            random_seed,
            export_counter,
        },
        // Effect 3: Drop a reference (refcount = 5 initially).
        Effect::DropRef {
            cell_id: cell_id_drop,
            holder_federation: holder_fed,
            current_refcount: 5,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Trace should have 4 rows (3 effects padded to next power of 2).
    assert_eq!(trace.len(), 4, "3 effects should pad to 4 rows");

    // Verify state threading: after all effects...
    // - Balance: 50000 - 1000 = 49000
    // - field[5] (refcount): 5 - 1 = 4 (DropRef decrements)
    // - field[7] (export_counter): 3 + 1 = 4 (ExportSturdyRef increments)
    // Check the last real row (row 2, the DropRef row):
    let drop_row = &trace[2];
    let final_f5 = drop_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 5];
    assert_eq!(
        final_f5,
        BabyBear::new(4),
        "refcount should be 4 after drop"
    );

    // Check the export row (row 1):
    let export_row = &trace[1];
    let post_export_f7 = export_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 7];
    assert_eq!(
        post_export_f7,
        BabyBear::new(4),
        "export_counter should be 4 after export"
    );

    // Verify effects hash in public inputs matches.
    let (expected_hash_lo, expected_hash_hi) = compute_effects_hash(&effects);
    assert_eq!(
        public_inputs[4], expected_hash_lo,
        "effects_hash_lo should match"
    );
    assert_eq!(
        public_inputs[5], expected_hash_hi,
        "effects_hash_hi should match"
    );

    // Verify net delta: -1000 (only the transfer changes balance).
    let net_delta = effect_vm::extract_net_delta(&public_inputs);
    assert_eq!(net_delta, Some(-1000), "net delta should be -1000");

    // Prove the entire multi-effect turn with a SINGLE STARK proof.
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    assert!(
        !proof.query_proofs.is_empty(),
        "proof should have query proofs"
    );
    assert_eq!(proof.trace_len, 4);

    // Verify the single proof covers all three effects.
    let result = stark::verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "Multi-effect STARK proof should verify: {:?}",
        result.err()
    );

    // Verify state commitments bind the full transition.
    // public_inputs[0] = old_commitment, public_inputs[1] = new_commitment
    assert_eq!(
        public_inputs[0], initial_state.state_commitment,
        "old_commitment PI should match initial state"
    );
    // The new commitment should differ (state changed).
    assert_ne!(
        public_inputs[0], public_inputs[1],
        "state commitment should change after effects"
    );
}
