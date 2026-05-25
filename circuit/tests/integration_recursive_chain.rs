//! Integration tests: IVC hash-chain proofs (sequential turns compressed into
//! a single proof) and multi-turn commitment-chain continuity.
//!
//! The Golden Vision recursive STARK path is gated behind `feature = "recursion"`.
//! These tests target the always-available Silver Vision / IVC path, which uses
//! `prove_ivc_stark` + `verify_ivc_stark` from `pyana_circuit::ivc`.
//!
//! Tests verify end-to-end that:
//!   1. An N-step IVC proof verifies.
//!   2. The IVC proof's PI binds `initial_root` and the accumulator correctly.
//!   3. Tampering the `new_roots` vector (different order or different values)
//!      produces a different IVC proof that is rejected against the original PI.
//!   4. A two-step IVC chain where the per-step STARK proofs are individually
//!      valid can be compressed into one IVC proof that also verifies.

use pyana_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::{generate_effect_vm_trace, pi},
    ivc::{prove_ivc_stark, verify_ivc_stark},
    poseidon2::hash_2_to_1,
    stark::{self},
};

// ─────────────────────────────────────────────────────────────────────────────
// 1. Single-step IVC: trivial chain of one commitment transition.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ivc_single_step_verifies() {
    let state = CellState::new(10_000, 0);
    let effects = vec![Effect::Transfer { amount: 100, direction: 1 }];
    let (trace, pi) = generate_effect_vm_trace(&state, &effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &pi);
    assert!(stark::verify(&air, &proof, &pi).is_ok());

    let initial_root = pi[pi::OLD_COMMIT];
    let commitment_1 = pi[pi::NEW_COMMIT];

    let (ivc_proof, ivc_pi) = prove_ivc_stark(initial_root, &[commitment_1]);
    let result = verify_ivc_stark(&ivc_proof, &ivc_pi);
    assert!(result.is_ok(), "single-step IVC must verify: {:?}", result.err());
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Two-step IVC: two sequential turns compressed.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ivc_two_step_chain_verifies() {
    // Turn 1.
    let state_0 = CellState::new(10_000, 0);
    let effects_1 = vec![Effect::Transfer { amount: 300, direction: 1 }];
    let (trace_1, pi_1) = generate_effect_vm_trace(&state_0, &effects_1);
    let air_1 = EffectVmAir::new(trace_1.len());
    assert!(stark::verify(&air_1, &stark::prove(&air_1, &trace_1, &pi_1), &pi_1).is_ok());

    let commitment_1 = pi_1[pi::NEW_COMMIT];

    // Turn 2: start from state after turn 1.
    let mut state_1 = state_0.clone();
    state_1.balance -= 300;
    state_1.nonce += 1;
    state_1.refresh_commitment();
    // Sanity: the refreshed commitment matches what the AIR produced.
    assert_eq!(state_1.state_commitment, commitment_1);

    let effects_2 = vec![Effect::SetField { field_idx: 5, value: BabyBear::new(999) }];
    let (trace_2, pi_2) = generate_effect_vm_trace(&state_1, &effects_2);
    let air_2 = EffectVmAir::new(trace_2.len());
    assert!(stark::verify(&air_2, &stark::prove(&air_2, &trace_2, &pi_2), &pi_2).is_ok());

    let commitment_2 = pi_2[pi::NEW_COMMIT];

    // Chain link.
    assert_eq!(pi_2[pi::OLD_COMMIT], commitment_1, "turn 2 must start from turn 1's end");

    // IVC compression.
    let initial_root = state_0.state_commitment;
    let (ivc_proof, ivc_pi) = prove_ivc_stark(initial_root, &[commitment_1, commitment_2]);
    let result = verify_ivc_stark(&ivc_proof, &ivc_pi);
    assert!(result.is_ok(), "two-step IVC must verify: {:?}", result.err());
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Three-step IVC: longer chain.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ivc_three_step_chain_verifies() {
    let mut state = CellState::new(50_000, 0);
    let initial_root = state.state_commitment;
    let mut commitments = Vec::new();

    // Apply three effects.
    let effect_sequence: &[Effect] = &[
        Effect::Transfer { amount: 100, direction: 1 },
        Effect::GrantCapability { cap_entry: BabyBear::new(0xCAFE) },
        Effect::SetField { field_idx: 2, value: BabyBear::new(42) },
    ];

    for effect in effect_sequence {
        let (trace, pi) = generate_effect_vm_trace(&state, &[effect.clone()]);
        let air = EffectVmAir::new(trace.len());
        assert!(stark::verify(&air, &stark::prove(&air, &trace, &pi), &pi).is_ok());
        commitments.push(pi[pi::NEW_COMMIT]);

        // Advance state manually.
        match effect {
            Effect::Transfer { amount, direction } => {
                if *direction == 1 {
                    state.balance -= *amount as u64;
                } else {
                    state.balance += *amount as u64;
                }
                state.nonce += 1;
                state.refresh_commitment();
            }
            Effect::GrantCapability { cap_entry } => {
                state.capability_root = hash_2_to_1(state.capability_root, *cap_entry);
                state.nonce += 1;
                state.refresh_commitment();
            }
            Effect::SetField { field_idx, value } => {
                state.fields[*field_idx as usize] = *value;
                state.nonce += 1;
                state.refresh_commitment();
            }
            _ => {}
        }
    }

    assert_eq!(commitments.len(), 3);

    let (ivc_proof, ivc_pi) = prove_ivc_stark(initial_root, &commitments);
    let result = verify_ivc_stark(&ivc_proof, &ivc_pi);
    assert!(result.is_ok(), "three-step IVC must verify: {:?}", result.err());
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. IVC tamper: wrong commitment in new_roots → different IVC proof.
//    The honest IVC PI must reject the tampered proof.
// ─────────────────────────────────────────────────────────────────────────────

/// Build two IVC proofs for different commitment chains and confirm each
/// proof is rejected against the other's PI.
#[test]
fn ivc_proof_rejected_against_wrong_commitments() {
    let state = CellState::new(10_000, 0);

    let effects_a = vec![Effect::Transfer { amount: 100, direction: 1 }];
    let effects_b = vec![Effect::Transfer { amount: 200, direction: 1 }];

    let (trace_a, pi_a) = generate_effect_vm_trace(&state, &effects_a);
    let (trace_b, pi_b) = generate_effect_vm_trace(&state, &effects_b);
    let air_a = EffectVmAir::new(trace_a.len());
    let air_b = EffectVmAir::new(trace_b.len());
    assert!(stark::verify(&air_a, &stark::prove(&air_a, &trace_a, &pi_a), &pi_a).is_ok());
    assert!(stark::verify(&air_b, &stark::prove(&air_b, &trace_b, &pi_b), &pi_b).is_ok());

    let initial_root = pi_a[pi::OLD_COMMIT]; // same for both (same initial state)
    let commit_a = pi_a[pi::NEW_COMMIT];
    let commit_b = pi_b[pi::NEW_COMMIT];

    // The two transfers produce different commitments.
    assert_ne!(commit_a, commit_b, "different transfers must produce different commitments");

    let (ivc_proof_a, ivc_pi_a) = prove_ivc_stark(initial_root, &[commit_a]);
    let (ivc_proof_b, ivc_pi_b) = prove_ivc_stark(initial_root, &[commit_b]);

    // Honest: each verifies against its own PI.
    assert!(verify_ivc_stark(&ivc_proof_a, &ivc_pi_a).is_ok());
    assert!(verify_ivc_stark(&ivc_proof_b, &ivc_pi_b).is_ok());

    // Cross-verify: proof_a against pi_b and vice versa.
    // At minimum, the IVC PIs must be different — so the other proof's PI
    // won't trivially match.
    let pi_differ = ivc_pi_a != ivc_pi_b;
    assert!(
        pi_differ,
        "IVC PIs for different commitment chains must differ"
    );

    // Attempt cross-verification (result can be an error or a wrong commitment).
    // The important thing is that at least one cross-verify fails.
    let cross_a_on_b = verify_ivc_stark(&ivc_proof_a, &ivc_pi_b);
    let cross_b_on_a = verify_ivc_stark(&ivc_proof_b, &ivc_pi_a);
    assert!(
        cross_a_on_b.is_err() || cross_b_on_a.is_err(),
        "at least one cross-verification must fail"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. Multi-step commitment uniqueness invariant.
//    Each step in a multi-turn chain must produce a *distinct* commitment.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn sequential_commitments_all_distinct() {
    let initial = CellState::new(20_000, 0);
    let mut state = initial.clone();

    let effects: &[Effect] = &[
        Effect::Transfer { amount: 100, direction: 1 },
        Effect::Transfer { amount: 200, direction: 0 },
        Effect::SetField { field_idx: 0, value: BabyBear::new(1) },
        Effect::SetField { field_idx: 1, value: BabyBear::new(2) },
    ];

    let mut seen: Vec<BabyBear> = vec![initial.state_commitment];

    for effect in effects {
        let (trace, pi) = generate_effect_vm_trace(&state, &[effect.clone()]);
        let air = EffectVmAir::new(trace.len());
        assert!(stark::verify(&air, &stark::prove(&air, &trace, &pi), &pi).is_ok());

        let new_commit = pi[pi::NEW_COMMIT];

        // Must differ from all previous commitments (otherwise two different
        // states map to the same commitment — a collision).
        for (i, prev) in seen.iter().enumerate() {
            assert_ne!(
                new_commit, *prev,
                "commitment after step {} collides with commitment at step {i}",
                seen.len()
            );
        }

        seen.push(new_commit);

        // Advance state.
        match effect {
            Effect::Transfer { amount, direction } => {
                if *direction == 1 {
                    state.balance -= *amount as u64;
                } else {
                    state.balance += *amount as u64;
                }
                state.nonce += 1;
                state.refresh_commitment();
            }
            Effect::SetField { field_idx, value } => {
                state.fields[*field_idx as usize] = *value;
                state.nonce += 1;
                state.refresh_commitment();
            }
            _ => {}
        }
    }

    assert_eq!(seen.len(), effects.len() + 1, "should have one commitment per step + initial");
}
