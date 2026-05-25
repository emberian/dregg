//! Sovereign-witness AIR-teeth tests (Phase 1, per SOVEREIGN-WITNESS-AIR-DESIGN.md).
//!
//! These are AIR-level adversarial tests: they exercise the boundary
//! constraints introduced at row 0 that pin the in-trace
//! `WITNESS_KEY_COMMIT[0..4]` and `WITNESS_SEQUENCE` aux columns to
//! `PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4]` and
//! `PI[SOVEREIGN_WITNESS_SEQUENCE]`.
//!
//! Pre-fix: no AIR teeth. The witness was a federation-side bookkeeping
//! handshake whose only binding was the pre-image relation between
//! `witness.cell_state.state_commitment()` and the federation's stored
//! commitment. A wire attacker could swap the witness for one signed
//! by a different key and the AIR happily proved the (forged) state
//! transition with no algebraic obstacle.
//!
//! Post-fix: row-0 boundary constraints catch any divergence between
//! the in-trace witness-identity aux columns and the PI slots the
//! verifier supplies. The verifier sources PI from the
//! signature-verified key (executor injection step); a malicious
//! executor that applies effects under a different key produces a
//! proof whose AIR-bound `WITNESS_KEY_COMMIT` disagrees with the
//! honest PI, and the verifier rejects.

use pyana_circuit::effect_vm::{
    self, CellState, Effect, EffectVmContext, generate_effect_vm_trace_ext,
};
use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{prove, verify};

fn initial_state() -> CellState {
    CellState::new(1_000_000, 0)
}

fn simple_effects() -> Vec<Effect> {
    // Single benign effect: a Transfer outflow, just enough to exercise
    // the trace's row-0 boundary alignment.
    vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }]
}

/// Hosted-cell path: PI slots and aux columns BOTH zero; boundary holds.
#[test]
fn hosted_cell_zero_sentinel_proof_verifies() {
    let state = initial_state();
    let effects = simple_effects();
    let ctx = EffectVmContext::default(); // is_sovereign_cell == false, limbs zero
    let (trace, pi) = generate_effect_vm_trace_ext(&state, &effects, ctx);
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_ok(),
        "hosted-cell path with zero sentinels must verify: {:?}",
        result.err()
    );
}

/// Sovereign-cell path: in-trace aux columns AND PI agree on a non-zero
/// witness key commit; boundary holds.
#[test]
fn sovereign_cell_honest_witness_proof_verifies() {
    let state = initial_state();
    let effects = simple_effects();
    let mut ctx = EffectVmContext::default();
    ctx.is_sovereign_cell = true;
    ctx.sovereign_witness_key_commit = [
        BabyBear::new(0x1111),
        BabyBear::new(0x2222),
        BabyBear::new(0x3333),
        BabyBear::new(0x4444),
    ];
    ctx.sovereign_witness_sequence = 7;

    let (trace, pi) = generate_effect_vm_trace_ext(&state, &effects, ctx);
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_ok(),
        "sovereign witness with self-consistent PI must verify: {:?}",
        result.err()
    );
}

/// Adversarial: PI's witness-key commit disagrees with the in-trace
/// aux column (the prover claims key K1, verifier supplies key K2).
/// The AIR boundary constraint rejects.
#[test]
fn sovereign_cell_tampered_pi_key_commit_rejects() {
    let state = initial_state();
    let effects = simple_effects();
    let mut ctx = EffectVmContext::default();
    ctx.is_sovereign_cell = true;
    let honest_key_commit = [
        BabyBear::new(0x1111),
        BabyBear::new(0x2222),
        BabyBear::new(0x3333),
        BabyBear::new(0x4444),
    ];
    ctx.sovereign_witness_key_commit = honest_key_commit;
    ctx.sovereign_witness_sequence = 7;

    let (trace, mut pi) = generate_effect_vm_trace_ext(&state, &effects, ctx);
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);

    // Tamper with PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE]: the verifier
    // expects key K2 but the trace was generated for K1.
    pi[effect_vm::pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE] = BabyBear::new(0xDEAD);
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_err(),
        "AIR boundary must reject when PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE] disagrees with the trace",
    );
}

/// Adversarial: PI sequence disagrees with the in-trace aux column.
#[test]
fn sovereign_cell_tampered_pi_sequence_rejects() {
    let state = initial_state();
    let effects = simple_effects();
    let mut ctx = EffectVmContext::default();
    ctx.is_sovereign_cell = true;
    ctx.sovereign_witness_key_commit = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
    ];
    ctx.sovereign_witness_sequence = 7;

    let (trace, mut pi) = generate_effect_vm_trace_ext(&state, &effects, ctx);
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);

    pi[effect_vm::pi::SOVEREIGN_WITNESS_SEQUENCE] = BabyBear::new(999);
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_err(),
        "AIR boundary must reject when PI[SOVEREIGN_WITNESS_SEQUENCE] disagrees with the trace",
    );
}

/// Adversarial: a hosted-cell proof whose PI claims sovereign status
/// (`IS_SOVEREIGN_CELL == 1`) but whose in-trace aux columns are zero.
/// Catching this is the verifier-side responsibility (it must read PI
/// against signature-verified key); at the AIR level this presents as
/// PI key commit non-zero but trace aux zero — boundary mismatches.
#[test]
fn hosted_proof_with_pi_claiming_sovereign_rejects() {
    let state = initial_state();
    let effects = simple_effects();
    // Generate as hosted (all zero sentinels in trace).
    let ctx = EffectVmContext::default();
    let (trace, mut pi) = generate_effect_vm_trace_ext(&state, &effects, ctx);
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);

    // Tamper PI to claim sovereign with a non-zero key commit (the
    // trace's aux columns are zero, so boundary fails).
    pi[effect_vm::pi::IS_SOVEREIGN_CELL] = BabyBear::ONE;
    pi[effect_vm::pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE] = BabyBear::new(0xC0DE);

    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_err(),
        "hosted-trace + sovereign-claiming PI must reject (boundary disagreement)",
    );
}
