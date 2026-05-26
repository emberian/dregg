//! Shared helpers for circuit integration tests.
//!
//! Extracted from `effect_vm/tests.rs` to avoid duplication across
//! `circuit/tests/integration_*.rs` files.  Keep this module light:
//! only types and functions that multiple integration test files share.

use pyana_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::{EffectVmContext, generate_effect_vm_trace, generate_effect_vm_trace_ext},
    stark::{self, StarkAir, proof_from_bytes, proof_to_bytes},
};

// ─────────────────────────────────────────────────────────────────────────────
// State builders
// ─────────────────────────────────────────────────────────────────────────────

pub fn make_state(balance: u64) -> CellState {
    CellState::new(balance, 0)
}

pub fn make_state_with_nonce(balance: u64, nonce: u32) -> CellState {
    CellState::new(balance, nonce)
}

// ─────────────────────────────────────────────────────────────────────────────
// Prove-then-verify helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Generate a valid proof for `effects` starting from `state`.
/// Returns `(proof_bytes, pi_u32)` in the serialised form the verifier crate consumes.
pub fn make_proof_bytes(state: &CellState, effects: &[Effect]) -> (Vec<u8>, Vec<u32>) {
    let (trace, pi) = generate_effect_vm_trace(state, effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);
    let pi_u32: Vec<u32> = pi.iter().map(|bb| bb.as_u32()).collect();
    (proof_bytes, pi_u32)
}

/// Generate proof with extended context (for effects that bind PI roots like
/// `ValidateHandoff`).
pub fn make_proof_bytes_ext(
    state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
) -> (Vec<u8>, Vec<u32>) {
    let (trace, pi) = generate_effect_vm_trace_ext(state, effects, context);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);
    let pi_u32: Vec<u32> = pi.iter().map(|bb| bb.as_u32()).collect();
    (proof_bytes, pi_u32)
}

/// Full round-trip: generate, prove, verify, return trace + pi.
/// Panics if the proof does not verify (hard failure, not an expected rejection).
pub fn assert_roundtrip(
    state: &CellState,
    effects: &[Effect],
    label: &str,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (trace, pi) = generate_effect_vm_trace(state, effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &pi);
    let result = stark::verify(&air, &proof, &pi);
    assert!(
        result.is_ok(),
        "{label}: proof must verify, got {:?}",
        result.err()
    );
    (trace, pi)
}

/// Full round-trip through serialised bytes (simulates prover-to-verifier hand-off).
pub fn assert_bytes_roundtrip(state: &CellState, effects: &[Effect], label: &str) {
    let (proof_bytes, pi_u32) = make_proof_bytes(state, effects);
    // Deserialise and verify to confirm the serialised form is sound.
    let proof = proof_from_bytes(&proof_bytes).expect("proof_from_bytes must succeed");
    let pi_bb: Vec<BabyBear> = pi_u32.iter().map(|&v| BabyBear::new_canonical(v)).collect();
    let trace_len = proof.trace_len;
    let air = EffectVmAir::new(trace_len);
    let result = stark::verify(&air, &proof, &pi_bb);
    assert!(
        result.is_ok(),
        "{label}: deserialized proof must verify, got {:?}",
        result.err()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Tamper helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Flip a byte at `offset` in `proof_bytes`. Panics if `offset` is out of range.
pub fn tamper_proof_byte(proof_bytes: &mut Vec<u8>, offset: usize) {
    let idx = offset.min(proof_bytes.len() - 1);
    proof_bytes[idx] ^= 0xFF;
}

/// XOR `mask` into `pi[slot]`.
pub fn tamper_pi(pi: &mut Vec<u32>, slot: usize, mask: u32) {
    assert!(
        slot < pi.len(),
        "tamper_pi: slot {slot} out of range (len={})",
        pi.len()
    );
    pi[slot] ^= mask;
}
