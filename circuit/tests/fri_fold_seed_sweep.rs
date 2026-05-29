//! BUG 2 reproduction harness: wide seed sweep of the Poseidon STARK verifier circuit's
//! FRI folding witness (prove + verify), plus a direct check of the fold arithmetic at the
//! FRI fold gate (row ~314 for the standard MerkleStarkAir layout).
//!
//! This test is feature-gated on `mina` (the Kimchi/Pasta stack) like the in-module tests.

#![cfg(feature = "mina")]

use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::poseidon_stark::{prove_poseidon, verify_poseidon};
use dregg_circuit::poseidon_stark_verifier_circuit::PoseidonStarkVerifierCircuit;
use dregg_circuit::stark::{MerkleStarkAir, generate_merkle_trace};

/// Sweep many seeds (far more than the in-module 10) through the full
/// prove() -> verify() pipeline. If BUG 2's seed-dependent FRI fold failure
/// still reproduces, some seed here will fail prove() or verify().
#[test]
fn fri_fold_wide_seed_sweep_prove_verify() {
    let leaves = [[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]];
    let positions = [0u32, 1, 2, 3];

    let mut failures: Vec<(u32, String)> = Vec::new();

    // A spread of seeds including ones that historically put the query in the
    // upper half of the FRI domain (query_pos > sibling_pos => even/odd swap).
    // Kept modest because each prove() drives a full Kimchi proof (~25s).
    for seed in [
        0u32,
        1,
        2,
        3,
        7,
        13,
        42,
        100,
        12345,
        99999,
        54321,
        31337,
        314159,
        0xDEADBEEF,
        0xFFFF_FFFF,
    ] {
        let (trace, pi) = generate_merkle_trace(seed, &leaves, &positions);
        let air = MerkleStarkAir;
        let proof = prove_poseidon(&air, &trace, &pi);

        if verify_poseidon(&air, &proof, &pi).is_err() {
            failures.push((seed, "native STARK verify failed".to_string()));
            continue;
        }

        let circuit = PoseidonStarkVerifierCircuit::new_minimal(proof);
        match circuit.prove() {
            Err(e) => failures.push((seed, format!("kimchi prove failed: {e}"))),
            Ok(kp) => {
                if let Err(e) = PoseidonStarkVerifierCircuit::verify(&kp) {
                    failures.push((seed, format!("kimchi verify failed: {e}")));
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "FRI fold seed sweep produced {} failures (BUG 2 reproduces): {:?}",
        failures.len(),
        &failures[..failures.len().min(8)]
    );
}

/// Direct soundness probe of the FRI fold arithmetic.
///
/// The reference FRI fold (poseidon_stark.rs::fri_commit_poseidon) computes
/// `folded = even + beta * odd` in BabyBear (mod P). The verifier circuit's fold
/// witness must therefore commit a *canonical BabyBear* fold value, i.e. a value in
/// `[0, P)`. This test scans seeds and reports any FRI layer opening whose
/// (query_value, sibling_value) pair would sum to >= P, which is exactly the regime
/// where computing the fold in native Fp (instead of mod P) diverges from the
/// reference — the root cause of the historical row-314 mismatch.
#[test]
fn fri_fold_values_are_canonical_babybear() {
    let leaves = [[10u32, 20, 30], [40, 50, 60], [70, 80, 90], [100, 110, 120]];
    let positions = [0u32, 1, 2, 3];

    for seed in 0u32..64 {
        let (trace, pi) = generate_merkle_trace(seed, &leaves, &positions);
        let air = MerkleStarkAir;
        let proof = prove_poseidon(&air, &trace, &pi);

        for q in &proof.query_proofs {
            for layer in &q.fri_layers {
                // Every committed FRI value must be a canonical BabyBear element.
                assert!(
                    layer.query_value < BABYBEAR_P,
                    "seed {seed}: non-canonical FRI query_value {}",
                    layer.query_value
                );
                assert!(
                    layer.sibling_value < BABYBEAR_P,
                    "seed {seed}: non-canonical FRI sibling_value {}",
                    layer.sibling_value
                );
            }
        }
    }
}
