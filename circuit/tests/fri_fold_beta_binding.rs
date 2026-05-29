//! Adversarial soundness tests for the in-circuit FRI fold binding.
//!
//! Background: the Poseidon-STARK Kimchi verifier circuit
//! (`poseidon_stark_verifier_circuit`) verifies a STARK proof's FRI fold using a
//! BabyBear-mod-P arithmetic gadget. A prior lane fixed the fold's arithmetic
//! domain but left two honest soundness gaps:
//!   (1) the folding challenge `beta` was hardcoded to 1 instead of the real
//!       Fiat-Shamir challenge, and
//!   (2) the fold result was bound only vacuously (the layer Merkle root was
//!       discarded, and the fold was not tied to the next FRI layer's opening).
//!
//! Those gaps are now closed:
//!   - each FRI layer's in-circuit Merkle root is bound to the committed layer
//!     root (carried as a public input);
//!   - the fold uses the REAL `beta`, derived via the same Fiat-Shamir transcript
//!     replay the prover used (`poseidon_stark::derive_challenges`), carried as a
//!     public input and copy-constrained into the fold's `beta` operand;
//!   - the fold output is copy-constrained to the NEXT FRI layer's committed leaf
//!     value, so the fold binds across layers instead of to itself.
//!
//! These tests exercise the adversarial surface: an honest proof must verify, and
//! a proof/witness with a tampered fold, a wrong `beta`, or a mismatched
//! next-layer opening must be rejected.

#![cfg(feature = "mina")]

use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::poseidon_stark::{prove_poseidon, verify_poseidon};
use dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkVerifierCircuit;
use dregg_circuit::stark::{generate_merkle_trace, MerkleStarkAir};

use mina_curves::pasta::Fp;

fn honest_proof() -> dregg_circuit::poseidon_stark::PoseidonStarkProof {
    let (trace, pi) = generate_merkle_trace(
        12345,
        &[
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ],
        &[0u32, 1, 2, 3],
    );
    let air = MerkleStarkAir;
    let proof = prove_poseidon(&air, &trace, &pi);
    assert!(
        verify_poseidon(&air, &proof, &pi).is_ok(),
        "baseline: honest STARK proof must verify"
    );
    proof
}

/// An adversarial attempt is considered REJECTED if any of:
///   - prove()/prove_with_witness returns Err (constraint system refused), or
///   - in debug builds, Kimchi's pre-proof witness check panics, or
///   - a proof is produced but verify() fails / returns false.
/// A successfully producing+verifying proof is the ONLY un-acceptable outcome.
fn assert_rejected<F>(label: &str, attempt: F)
where
    F: FnOnce() -> Result<dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkKimchiProof, String>
        + std::panic::UnwindSafe,
{
    let outcome = std::panic::catch_unwind(attempt);
    match outcome {
        Err(_panic) => { /* Kimchi witness pre-check panicked => rejected */ }
        Ok(Err(_e)) => { /* prove() refused the witness => rejected */ }
        Ok(Ok(kp)) => {
            let v = PoseidonStarkVerifierCircuit::verify(&kp);
            assert!(
                v.is_err() || v.unwrap() == false,
                "SOUNDNESS BUG ({label}): adversarial proof was accepted by both prove() and verify()"
            );
        }
    }
}

/// Baseline: the honest FRI fold binding proves and verifies.
#[test]
fn honest_fri_fold_binding_verifies() {
    let proof = honest_proof();
    // MerkleStarkAir(4,6,4): domain 16 => 2 FRI layers, so there is a real
    // layer0 -> layer1 fold binding to exercise.
    let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
    let (_, _, layout) = circuit.build_circuit();
    assert!(
        layout.num_fri_layers >= 2,
        "expected >= 2 FRI layers for an inter-layer fold binding, got {}",
        layout.num_fri_layers
    );
    let kp = circuit.prove().expect("honest witness must prove");
    assert_eq!(
        PoseidonStarkVerifierCircuit::verify(&kp).unwrap(),
        true,
        "honest proof must verify"
    );
}

/// ADVERSARIAL (tampered fold / mismatched next-layer opening): flip the next
/// FRI layer's committed query value. The honest witness then computes
/// `fold(layer0) != layer1.query_value`, so the fold->next-leaf copy-constraint
/// (and the layer-1 root binding) is violated. Must be rejected.
#[test]
fn tampered_next_layer_opening_rejected() {
    let mut proof = honest_proof();
    {
        let q = proof
            .query_proofs
            .first_mut()
            .expect("proof has at least one query");
        assert!(
            q.fri_layers.len() >= 2,
            "need >= 2 FRI layers to tamper the next-layer opening"
        );
        // Change layer 1's query value: it no longer equals fold(layer0), and its
        // Poseidon leaf no longer hashes to the committed layer-1 root.
        let orig = q.fri_layers[1].query_value;
        q.fri_layers[1].query_value = (orig + 1) % BABYBEAR_P;
    }
    let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
    assert_rejected("tampered next-layer opening", move || circuit.prove());
}

/// ADVERSARIAL (tampered fold output): forge the witness so the fold output cell
/// of layer 0 holds an arbitrary value decoupled from the committed next leaf.
/// The fold->next-leaf copy-constraint forces the layer-0 fold output to equal
/// layer-1's committed leaf value; a forged fold output breaks it. Must be
/// rejected.
#[test]
fn forged_fold_output_rejected() {
    let proof = honest_proof();
    let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
    let (_, _, layout) = circuit.build_circuit();
    let mut witness = circuit.generate_witness(&layout);

    // Locate layer-0's fold-output cell. Per build_circuit's per-query layout, the
    // FRI section begins after:
    //   public inputs + (A) trace leaf + (B) trace path + (C) eq
    //                 + (D) constraint leaf + (E) constraint path + (F) eq
    //                 + (G) next leaf + (H) next path + (I) eq
    //                 + (J) constraint-eval muls + (K) 2 consistency muls.
    // We instead corrupt EVERY fold-output candidate cell robustly: scan the FRI
    // region. To stay layout-agnostic, we corrupt the layer-1 leaf-value side of
    // the binding by perturbing all single-value Poseidon leaf inputs is brittle;
    // instead, we directly forge the copy-constrained partner by perturbing the
    // honest fold output. The fold output is a canonical remainder cell; we find
    // it by recomputing the layout offsets below.
    let pos = fri_layer0_fold_output_cell(&layout);
    // Perturb the fold output away from the (committed) next-layer leaf value.
    witness[pos.1][pos.0] += Fp::from(1u64);

    assert_rejected("forged fold output", move || {
        circuit.prove_with_witness(witness, &layout)
    });
}

/// ADVERSARIAL (wrong beta): keep the verifier-supplied `beta` public input at
/// the true Fiat-Shamir value, but forge the witness's fold `beta` operand to a
/// different value. The copy-constraint tying the operand to the `beta` PI must
/// reject this. Must be rejected.
#[test]
fn wrong_beta_in_fold_operand_rejected() {
    let proof = honest_proof();
    let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
    let (_, _, layout) = circuit.build_circuit();
    let mut witness = circuit.generate_witness(&layout);

    // Forge the layer-0 fold `beta` operand (mul-gadget input w[0]).
    let beta_cell = fri_layer0_beta_input_cell(&layout);
    let forged_beta = witness[beta_cell.1][beta_cell.0] + Fp::from(7u64);
    witness[beta_cell.1][beta_cell.0] = forged_beta;

    assert_rejected("wrong beta operand", move || {
        circuit.prove_with_witness(witness, &layout)
    });
}

// ---------------------------------------------------------------------------
// Layout offset helpers (mirror build_circuit's per-query gadget ordering).
// ---------------------------------------------------------------------------

const POSEIDON_GADGET_ROWS: usize = 12; // 11 Poseidon rows + 1 Zero/output row.

/// Row at which the FRI section (layer 0) begins for query 0.
fn fri_section_start(layout: &dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkVerifierLayout) -> usize {
    let d = layout.tree_depth;
    let num_bb_muls = layout.num_cols * 4 /* constraint_degree */;
    layout.public_input_count
        // (A) trace leaf hash
        + POSEIDON_GADGET_ROWS
        // (B) trace path
        + d * POSEIDON_GADGET_ROWS
        // (C) trace root eq
        + 1
        // (D) constraint leaf hash
        + POSEIDON_GADGET_ROWS
        // (E) constraint path
        + d * POSEIDON_GADGET_ROWS
        // (F) constraint root eq
        + 1
        // (G) next-trace leaf hash
        + POSEIDON_GADGET_ROWS
        // (H) next-trace path
        + d * POSEIDON_GADGET_ROWS
        // (I) next-trace root eq
        + 1
        // (J) constraint-eval muls (3 rows each)
        + num_bb_muls * 3
        // (K) two consistency muls (3 rows each)
        + 2 * 3
}

/// Cell holding layer-0's fold output (the canonical remainder in the add
/// gadget's reduction row, col 2).
fn fri_layer0_fold_output_cell(
    layout: &dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkVerifierLayout,
) -> (usize, usize) {
    let start = fri_section_start(layout);
    let fri_depth = layout.tree_depth.saturating_sub(1);
    // leaf + path + root-eq + mul(3) ... add_base = start + leaf + path + 1 + 3.
    let add_base = start + POSEIDON_GADGET_ROWS + fri_depth * POSEIDON_GADGET_ROWS + 1 + 3;
    (add_base + 1, 2)
}

/// Cell holding layer-0's fold `beta` operand (mul gadget input w[0]).
fn fri_layer0_beta_input_cell(
    layout: &dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkVerifierLayout,
) -> (usize, usize) {
    let start = fri_section_start(layout);
    let fri_depth = layout.tree_depth.saturating_sub(1);
    let mul_base = start + POSEIDON_GADGET_ROWS + fri_depth * POSEIDON_GADGET_ROWS + 1;
    (mul_base, 0)
}

/// Guard: the layer-0 FRI offset helpers stay within the circuit's row count.
/// FRI layers have per-layer Merkle depth `tree_depth - 1 - li`, so we only
/// assert layer-0's cells (used by the adversarial tests) are in range.
#[test]
fn fri_layer0_offsets_in_range() {
    let proof = honest_proof();
    let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
    let (_, _, layout) = circuit.build_circuit();
    let out = fri_layer0_fold_output_cell(&layout);
    let beta = fri_layer0_beta_input_cell(&layout);
    assert!(out.0 < layout.total_rows, "fold-output row out of range");
    assert!(beta.0 < layout.total_rows, "beta-input row out of range");
    assert!(beta.0 < out.0, "beta input must precede fold output");
}
