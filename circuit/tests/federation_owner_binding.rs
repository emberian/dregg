//! γ.2 follow-up (#131 + #132) AIR-teeth tests: per-cell federation +
//! owner-cell-id binding.
//!
//! Pre-fix: each per-cell / bilateral / witnessed-receipt proof exposed its
//! turn identity (TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//! PREVIOUS_RECEIPT_HASH) and bilateral accumulator roots, but NOTHING that
//! named the federation the proof was minted under, nor the owner cell whose
//! transition it attests. A verifier handed a proof from federation A (or for
//! owner cell X) could not detect it being substituted for federation B (or
//! owner cell Y): the structural shape is identical.
//!
//! Post-fix: PI carries FEDERATION_ID[4] (#131) and OWNER_CELL_ID[4] (#132),
//! each a Poseidon2 compression of the respective 32-byte id. Row-0 boundary
//! constraints pin the in-trace aux columns to those PI slots, so a prover
//! cannot decouple the claimed federation/owner from what the trace
//! committed. The off-AIR verifier (turn::executor::proof_verify) recomputes
//! the expected commitments from the TRUSTED federation id + owner cell id;
//! a swapped proof fails the PI-match loop. These tests exercise the AIR
//! boundary directly: tamper the PI (simulating a verifier that expects a
//! DIFFERENT federation/owner than the one the proof was minted for) and
//! assert the STARK verifier rejects.

use dregg_circuit::effect_vm::{
    self, CellState, Effect, EffectVmContext, canonical_id_to_felts_4, generate_effect_vm_trace_ext,
};
use dregg_circuit::stark::{prove, verify};

fn initial_state() -> CellState {
    CellState::new(1_000_000, 0)
}

fn simple_effects() -> Vec<Effect> {
    vec![Effect::Transfer {
        amount: 100,
        direction: 1,
    }]
}

const FED_A: [u8; 32] = [0xA1u8; 32];
const FED_B: [u8; 32] = [0xB2u8; 32];
const OWNER_X: [u8; 32] = [0x11u8; 32];
const OWNER_Y: [u8; 32] = [0x22u8; 32];

fn ctx_for(federation_id: [u8; 32], owner_cell_id: [u8; 32]) -> EffectVmContext {
    EffectVmContext {
        federation_id,
        owner_cell_id,
        ..Default::default()
    }
}

/// Sanity: the PI slots carry the 4-felt commitment of the supplied
/// federation id + owner cell id, and distinct ids produce distinct
/// commitments (so a swap is detectable).
#[test]
fn federation_owner_binding_round_trip() {
    let state = initial_state();
    let effects = simple_effects();
    let (_trace, pi) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_A, OWNER_X));

    let expected_fed = canonical_id_to_felts_4(&FED_A);
    let expected_owner = canonical_id_to_felts_4(&OWNER_X);
    for i in 0..effect_vm::pi::FEDERATION_ID_LEN {
        assert_eq!(
            pi[effect_vm::pi::FEDERATION_ID_BASE + i],
            expected_fed[i],
            "FEDERATION_ID PI slot {i} must carry commit(FED_A)"
        );
    }
    for i in 0..effect_vm::pi::OWNER_CELL_ID_LEN {
        assert_eq!(
            pi[effect_vm::pi::OWNER_CELL_ID_BASE + i],
            expected_owner[i],
            "OWNER_CELL_ID PI slot {i} must carry commit(OWNER_X)"
        );
    }

    // Distinctness: a different federation / owner yields a different
    // commitment — without this, a swap wouldn't be detectable.
    assert_ne!(
        canonical_id_to_felts_4(&FED_A),
        canonical_id_to_felts_4(&FED_B),
        "distinct federations must commit to distinct felts"
    );
    assert_ne!(
        canonical_id_to_felts_4(&OWNER_X),
        canonical_id_to_felts_4(&OWNER_Y),
        "distinct owner cells must commit to distinct felts"
    );
}

/// Honest proof (federation A, owner X): PI and trace agree; verifies.
#[test]
fn federation_owner_honest_proof_verifies() {
    let state = initial_state();
    let effects = simple_effects();
    let (trace, pi) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_A, OWNER_X));
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_ok(),
        "honest federation+owner-bound proof must verify: {:?}",
        result.err()
    );
}

/// #131 ADVERSARIAL: a proof minted for federation A, when checked against a
/// verifier that expects federation B, MUST FAIL. We simulate the verifier's
/// expectation by overwriting PI[FEDERATION_ID] with commit(FED_B) (what the
/// off-AIR verifier reconstructs for federation B). The row-0 boundary
/// constraint binds the trace's federation aux columns (commit(FED_A)) to the
/// PI, so the mismatch is caught.
#[test]
fn proof_minted_for_federation_a_rejected_against_federation_b() {
    let state = initial_state();
    let effects = simple_effects();
    let (trace, mut pi) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_A, OWNER_X));
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);

    // Verifier expects federation B: PI[FEDERATION_ID] = commit(FED_B).
    let fed_b = canonical_id_to_felts_4(&FED_B);
    for i in 0..effect_vm::pi::FEDERATION_ID_LEN {
        pi[effect_vm::pi::FEDERATION_ID_BASE + i] = fed_b[i];
    }
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_err(),
        "proof minted under federation A must be rejected when verified against federation B",
    );
}

/// #132 ADVERSARIAL: a proof minted for owner cell X, checked against a
/// verifier expecting owner cell Y, MUST FAIL.
#[test]
fn proof_minted_for_owner_x_rejected_against_owner_y() {
    let state = initial_state();
    let effects = simple_effects();
    let (trace, mut pi) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_A, OWNER_X));
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi);

    // Verifier expects owner cell Y: PI[OWNER_CELL_ID] = commit(OWNER_Y).
    let owner_y = canonical_id_to_felts_4(&OWNER_Y);
    for i in 0..effect_vm::pi::OWNER_CELL_ID_LEN {
        pi[effect_vm::pi::OWNER_CELL_ID_BASE + i] = owner_y[i];
    }
    let result = verify(&air, &proof, &pi);
    assert!(
        result.is_err(),
        "proof minted for owner cell X must be rejected when verified against owner cell Y",
    );
}

/// Defense-in-depth: a prover cannot mint a trace committing to federation A
/// while presenting a PI that claims federation B (e.g. to satisfy a
/// federation-B verifier with a federation-A trace). The row-0 boundary
/// rejects the decoupling regardless of which side initiates it.
#[test]
fn prover_cannot_decouple_trace_federation_from_pi() {
    let state = initial_state();
    let effects = simple_effects();
    // Trace committed to federation A.
    let (trace, _pi_a) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_A, OWNER_X));
    // But the prover presents a PI built for federation B.
    let (_trace_b, pi_b) = generate_effect_vm_trace_ext(&state, &effects, ctx_for(FED_B, OWNER_X));
    let air = effect_vm::EffectVmAir::new(trace.len());
    let proof = prove(&air, &trace, &pi_b);
    let result = verify(&air, &proof, &pi_b);
    assert!(
        result.is_err(),
        "federation-A trace presented with federation-B PI must be rejected by the row-0 boundary",
    );
}
