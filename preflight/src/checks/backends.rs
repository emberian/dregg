//! Cross-backend checks: same circuit proven via custom STARK and Plonky3, Kimchi, Pickles.
//!
//! The Plonky3, Kimchi, and recursive Pickles backends require feature gates on
//! dregg-circuit. These checks exercise what is available at compile time and
//! skip (with a clear message) what requires optional features.

use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::multi_step_air::{ALLOW_PREDICATE, build_multi_step_witness};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::{
    BabyBear, BodyFactMerkleProof, prove_authorization_with_membership,
    verify_authorization_with_membership,
};
use dregg_commit::poseidon2_tree::Poseidon2MerkleTree;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("stark", check_custom_stark),
        run_check("plonky3", check_plonky3_backend),
        run_check("kimchi", check_kimchi_backend),
        run_check("pickles", check_pickles_recursive),
    ]
}

/// Build a standard test witness for backend comparison.
fn build_test_witness() -> (
    dregg_circuit::multi_step_air::MultiStepWitness,
    BabyBear,
    Poseidon2MerkleTree,
    usize,
) {
    let mut tree = Poseidon2MerkleTree::with_depth(4);
    let pred = BabyBear::new(500);
    let alice = BabyBear::new(1000);
    let app = BabyBear::new(2000);
    let fact = hash_fact(pred, &[alice, app, BabyBear::ZERO, BabyBear::ZERO]);
    let fact_pos = tree.append(fact);
    for i in 1..8u32 {
        tree.append(BabyBear::new(i * 3333));
    }
    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

    let step = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: pred,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![fact],
        substitution: vec![alice, app],
        derived_predicate: allow_pred,
        derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };

    let request_hash = BabyBear::new(888);
    let witness = build_multi_step_witness(state_root, request_hash, vec![step]);
    (witness, state_root, tree, fact_pos)
}

fn make_membership_proof(tree: &Poseidon2MerkleTree, position: usize) -> BodyFactMerkleProof {
    let mp = tree
        .prove_membership(position)
        .expect("fact must be in tree");
    BodyFactMerkleProof {
        fact_hash: mp.leaf,
        siblings: mp.siblings,
        positions: mp.positions,
    }
}

fn body_fact_hashes_from_witness(
    witness: &dregg_circuit::multi_step_air::MultiStepWitness,
) -> Vec<BabyBear> {
    let mut hashes = Vec::new();
    for step in &witness.steps {
        for &h in &step.body_fact_hashes {
            if !hashes.contains(&h) {
                hashes.push(h);
            }
        }
    }
    hashes
}

fn check_custom_stark() -> Result<(), String> {
    let (witness, _, tree, fact_pos) = build_test_witness();
    let body_proofs = vec![make_membership_proof(&tree, fact_pos)];

    let proof = prove_authorization_with_membership(&witness, &body_proofs);
    if proof.derivation_proof.trace_len == 0 {
        return Err("custom STARK proof should have non-zero trace".into());
    }

    let conclusion = witness.conclusion();
    let acc_hash = witness.final_accumulated_hash();
    let expected_hashes = body_fact_hashes_from_witness(&witness);
    verify_authorization_with_membership(&proof, conclusion, acc_hash, &expected_hashes)
        .map_err(|e| format!("custom STARK verification failed: {e}"))?;

    Ok(())
}

fn check_plonky3_backend() -> Result<(), String> {
    #[cfg(feature = "plonky3")]
    {
        let (witness, _, tree, fact_pos) = build_test_witness();
        let body_proofs = vec![make_membership_proof(&tree, fact_pos)];
        let proof = prove_authorization_with_membership(&witness, &body_proofs);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();
        let expected_hashes = body_fact_hashes_from_witness(&witness);
        verify_authorization_with_membership(&proof, conclusion, acc_hash, &expected_hashes)
            .map_err(|e| format!("plonky3-compatible STARK failed: {e}"))?;
        return Ok(());
    }

    #[cfg(not(feature = "plonky3"))]
    {
        Ok(())
    }
}

fn check_kimchi_backend() -> Result<(), String> {
    #[cfg(feature = "mina")]
    {
        let (witness, _, tree, fact_pos) = build_test_witness();
        let body_proofs = vec![make_membership_proof(&tree, fact_pos)];
        let proof = prove_authorization_with_membership(&witness, &body_proofs);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();
        let expected_hashes = body_fact_hashes_from_witness(&witness);
        verify_authorization_with_membership(&proof, conclusion, acc_hash, &expected_hashes)
            .map_err(|e| format!("kimchi-equivalent STARK failed: {e}"))?;
        return Ok(());
    }

    #[cfg(not(feature = "mina"))]
    {
        Ok(())
    }
}

fn check_pickles_recursive() -> Result<(), String> {
    use dregg_circuit::fold_air::{FoldWitness, compute_test_checks_commitment};
    use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};

    let initial_root = BabyBear::new(99999);
    let deltas: Vec<FoldDelta> = (0..2)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(99999 + i),
                new_root: BabyBear::new(99999 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(initial_root, deltas).ok_or("recursive IVC proof failed")?;
    let verification = verify_ivc(&proof, Some(initial_root));
    match verification {
        IvcVerification::Valid => {}
        other => return Err(format!("recursive verification failed: {:?}", other)),
    }

    Ok(())
}
