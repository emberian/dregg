//! Proof composition checks: AND composition, IVC chaining, aggregation.

use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use dregg_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
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
        run_check("and_compose", check_and_composition),
        run_check("chain", check_ivc_chain),
        run_check("aggregate", check_proof_aggregation),
    ]
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

fn check_and_composition() -> Result<(), String> {
    let mut tree = Poseidon2MerkleTree::with_depth(4);

    let pred_a = BabyBear::new(200);
    let pred_b = BabyBear::new(201);
    let alice = BabyBear::new(1000);
    let app = BabyBear::new(2000);
    let perm = BabyBear::new(3000);

    let fact_a = hash_fact(pred_a, &[alice, app, perm, BabyBear::ZERO]);
    let fact_b = hash_fact(pred_b, &[alice, app, BabyBear::new(4000), BabyBear::ZERO]);
    let pos_a = tree.append(fact_a);
    let pos_b = tree.append(fact_b);

    for i in 2..8u32 {
        tree.append(BabyBear::new(i * 7777));
    }

    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);
    let request_hash = BabyBear::new(99);

    let step1 = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: BabyBear::new(300),
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: pred_a,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![fact_a],
        substitution: vec![alice, app, perm],
        derived_predicate: BabyBear::new(300),
        derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };

    let step2 = DerivationWitness {
        rule: CircuitRule {
            id: 2,
            num_body_atoms: 1,
            num_variables: 3,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![BodyAtomPattern {
                predicate: pred_b,
                terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (true, BabyBear::new(2)),
                ],
            }],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root,
        body_fact_hashes: vec![fact_b],
        substitution: vec![alice, app, BabyBear::new(4000)],
        derived_predicate: allow_pred,
        derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };

    let witness = build_multi_step_witness(state_root, request_hash, vec![step1, step2]);
    if witness.conclusion() != BabyBear::ONE {
        return Err("AND composition should conclude ALLOW".into());
    }

    let body_proofs = vec![
        make_membership_proof(&tree, pos_a),
        make_membership_proof(&tree, pos_b),
    ];
    let proof = prove_authorization_with_membership(&witness, &body_proofs);
    let conclusion = witness.conclusion();
    let acc_hash = witness.final_accumulated_hash();
    let body_hashes = body_fact_hashes_from_witness(&witness);

    verify_authorization_with_membership(&proof, conclusion, acc_hash, &body_hashes)
        .map_err(|e| format!("AND-composed proof verification failed: {e}"))?;

    Ok(())
}

fn check_ivc_chain() -> Result<(), String> {
    use dregg_circuit::fold_air::{FoldWitness, compute_test_checks_commitment};

    let initial_root = BabyBear::new(50000);

    let deltas: Vec<FoldDelta> = (0..3)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(50000 + i),
                new_root: BabyBear::new(50000 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(initial_root, deltas).ok_or("IVC chain proof failed")?;

    if proof.step_count != 3 {
        return Err(format!("expected 3 steps, got {}", proof.step_count));
    }

    let verification = verify_ivc(&proof, Some(initial_root));
    match verification {
        IvcVerification::Valid => {}
        other => return Err(format!("IVC chain verification failed: {:?}", other)),
    }

    if proof.final_root != BabyBear::new(50003) {
        return Err(format!(
            "expected final_root=50003, got {:?}",
            proof.final_root
        ));
    }

    Ok(())
}

fn check_proof_aggregation() -> Result<(), String> {
    let mut tree = Poseidon2MerkleTree::with_depth(4);
    let preds: Vec<BabyBear> = (0..4).map(|i| BabyBear::new(400 + i)).collect();
    let alice = BabyBear::new(1000);
    let mut fact_positions = Vec::new();

    for i in 0..4u32 {
        let fact = hash_fact(
            preds[i as usize],
            &[
                alice,
                BabyBear::new(i + 2000),
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        );
        fact_positions.push(tree.append(fact));
    }
    for i in 4..8u32 {
        tree.append(BabyBear::new(i * 5555));
    }

    let mut tree_for_root = tree.clone();
    let state_root = tree_for_root.root();
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

    let mut all_valid = true;
    for i in 0..4u32 {
        let fact = hash_fact(
            preds[i as usize],
            &[
                alice,
                BabyBear::new(i + 2000),
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        );
        let step = DerivationWitness {
            rule: CircuitRule {
                id: i + 1,
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
                    predicate: preds[i as usize],
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
            substitution: vec![alice, BabyBear::new(i + 2000)],
            derived_predicate: allow_pred,
            derived_terms: [
                alice,
                BabyBear::new(i + 2000),
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        let witness = build_multi_step_witness(state_root, BabyBear::new(i + 1000), vec![step]);
        let body_proofs = vec![make_membership_proof(&tree, fact_positions[i as usize])];
        let proof = prove_authorization_with_membership(&witness, &body_proofs);
        let result = verify_authorization_with_membership(
            &proof,
            witness.conclusion(),
            witness.final_accumulated_hash(),
            &body_fact_hashes_from_witness(&witness),
        );
        if result.is_err() {
            all_valid = false;
        }
    }

    if !all_valid {
        return Err("not all 4 aggregated proofs verified".into());
    }

    Ok(())
}
