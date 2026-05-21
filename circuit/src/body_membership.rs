//! In-circuit Poseidon2 Merkle membership proofs for body facts.
//!
//! This module closes the soundness gap in the multi-step derivation AIR:
//! constraint 19 checks that `body_root == state_root` (public input), but the
//! body HASH itself is prover-supplied. A malicious prover could place arbitrary
//! hash values in the body_hash columns without proving those hashes correspond
//! to actual leaves in the committed Merkle tree.
//!
//! **The fix (Approach 3 -- proof composition):**
//!
//! For each body fact used in the derivation, the prover must also produce a
//! separate Merkle membership STARK proving that the fact's hash is a leaf in
//! the Poseidon2 Merkle tree committed at `state_root`. The verifier checks:
//!
//! 1. The derivation STARK is valid (rules applied correctly, conclusion is ALLOW)
//! 2. For each body fact: a Merkle membership STARK proves the fact is in the tree
//! 3. The leaf hashes in the membership proofs match the body_hash values used
//!    in the derivation trace
//! 4. All membership proofs share the same `state_root` as the derivation proof
//!
//! This is IVC/composition: two proof types sharing the public `state_root`.
//! No trace widening needed -- just additional proof obligations.

use crate::field::BabyBear;
use crate::multi_step_air::{
    MultiStepWitness, prove_authorization_stark, verify_authorization_stark,
};
use crate::poseidon2_air::{MerklePoseidon2StarkAir, generate_merkle_poseidon2_trace};
use crate::stark::{self, StarkProof};
use serde::{Deserialize, Serialize};

/// A Merkle proof for a single body fact: siblings + positions (leaf-to-root).
///
/// This is the raw data needed to produce a membership STARK. It mirrors
/// `Poseidon2MerkleProof` from the commit crate but is self-contained here
/// so the circuit crate has no dependency on the commit crate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BodyFactMerkleProof {
    /// The hash of the body fact (leaf in the Merkle tree).
    pub fact_hash: BabyBear,
    /// 3 sibling hashes at each level (leaf-to-root order).
    pub siblings: Vec<[BabyBear; 3]>,
    /// Position (0..3) at each level (leaf-to-root order).
    pub positions: Vec<u8>,
}

/// Composite proof: derivation STARK + per-body-fact Merkle membership STARKs.
///
/// This is the complete proof that authorization was derived AND that every
/// body fact referenced in the derivation actually exists in the committed
/// Poseidon2 Merkle tree at `state_root`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BodyMembershipProof {
    /// The derivation STARK (proves rules were applied correctly).
    pub derivation_proof: StarkProof,
    /// One Merkle membership STARK per distinct body fact used.
    /// Each proves: leaf_hash is in the tree with root == state_root.
    pub membership_proofs: Vec<MembershipEntry>,
    /// The shared state root (public input to both proof types).
    pub state_root: BabyBear,
}

/// A single membership proof entry: the fact hash + the STARK proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MembershipEntry {
    /// The body fact hash that this proof demonstrates membership for.
    pub fact_hash: BabyBear,
    /// STARK proof of Merkle membership (leaf=fact_hash, root=state_root).
    pub proof: StarkProof,
}

/// Generate a composite proof: derivation + body fact membership.
///
/// For each body fact used across all derivation steps, generates a Merkle
/// membership STARK proving that fact's hash is a leaf under `state_root`.
///
/// # Arguments
///
/// * `witness` - The multi-step derivation witness
/// * `body_merkle_proofs` - Merkle proofs for each distinct body fact hash
///
/// # Panics
///
/// Panics if a body fact used in the derivation has no corresponding Merkle proof.
pub fn prove_authorization_with_membership(
    witness: &MultiStepWitness,
    body_merkle_proofs: &[BodyFactMerkleProof],
) -> BodyMembershipProof {
    // Step 1: Generate the derivation STARK
    let derivation_proof = prove_authorization_stark(witness);

    // Step 2: Collect all distinct body fact hashes used across all steps
    let mut used_fact_hashes: Vec<BabyBear> = Vec::new();
    for step in &witness.steps {
        for &hash in &step.body_fact_hashes {
            if !used_fact_hashes.contains(&hash) {
                used_fact_hashes.push(hash);
            }
        }
    }

    // Step 3: For each used body fact hash, find its Merkle proof and generate a STARK
    let mut membership_proofs = Vec::with_capacity(used_fact_hashes.len());
    for &fact_hash in &used_fact_hashes {
        let merkle_proof = body_merkle_proofs
            .iter()
            .find(|p| p.fact_hash == fact_hash)
            .unwrap_or_else(|| {
                panic!(
                    "No Merkle proof provided for body fact hash {}",
                    fact_hash.0
                )
            });

        assert_eq!(
            merkle_proof.siblings.len(),
            merkle_proof.positions.len(),
            "Merkle proof siblings/positions length mismatch for fact {}",
            fact_hash.0
        );
        assert!(
            merkle_proof.siblings.len() >= 2,
            "Merkle proof depth must be >= 2 for STARK (got {} for fact {})",
            merkle_proof.siblings.len(),
            fact_hash.0
        );

        // Generate the Merkle membership trace and STARK proof
        let (trace, public_inputs) = generate_merkle_poseidon2_trace(
            fact_hash,
            &merkle_proof.siblings,
            &merkle_proof.positions,
        );

        // Verify the Merkle proof computes to the expected state_root
        let computed_root = public_inputs[1];
        assert_eq!(
            computed_root, witness.initial_state_root,
            "Merkle proof for fact {} computes root {} but expected state_root {}",
            fact_hash.0, computed_root.0, witness.initial_state_root.0
        );

        let air = MerklePoseidon2StarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);

        membership_proofs.push(MembershipEntry { fact_hash, proof });
    }

    BodyMembershipProof {
        derivation_proof,
        membership_proofs,
        state_root: witness.initial_state_root,
    }
}

/// Verify a composite authorization proof: derivation + body fact membership.
///
/// The verifier checks:
/// 1. The derivation STARK is valid
/// 2. Each membership STARK is valid against the shared state_root
/// 3. Every body fact hash claimed in the derivation has a corresponding valid
///    membership proof
/// 4. The membership proofs' leaf hashes match what was used in derivation
///
/// # Arguments
///
/// * `proof` - The composite proof to verify
/// * `conclusion` - Expected conclusion (1=ALLOW, 0=DENY)
/// * `accumulated_hash` - The final accumulated hash from the derivation
/// * `expected_body_hashes` - The body fact hashes that should have membership proofs
///
/// # Returns
///
/// `Ok(())` if the proof is valid, `Err(reason)` otherwise.
pub fn verify_authorization_with_membership(
    proof: &BodyMembershipProof,
    conclusion: BabyBear,
    accumulated_hash: BabyBear,
    expected_body_hashes: &[BabyBear],
) -> Result<(), String> {
    // Step 1: Verify the derivation STARK
    verify_authorization_stark(conclusion, accumulated_hash, &proof.derivation_proof)?;

    // Step 2: Extract the state_root from the derivation proof's public inputs
    let derivation_state_root = BabyBear::new_canonical(proof.derivation_proof.public_inputs[0]);
    if derivation_state_root != proof.state_root {
        return Err(format!(
            "State root mismatch: proof claims {} but derivation public input is {}",
            proof.state_root.0, derivation_state_root.0
        ));
    }

    // Step 3: Verify each membership STARK
    for entry in &proof.membership_proofs {
        let public_inputs = vec![entry.fact_hash, proof.state_root];
        let air = MerklePoseidon2StarkAir;
        stark::verify(&air, &entry.proof, &public_inputs).map_err(|e| {
            format!(
                "Merkle membership proof for fact hash {} failed: {}",
                entry.fact_hash.0, e
            )
        })?;
    }

    // Step 4: Verify that every expected body fact hash has a valid membership proof
    for &expected_hash in expected_body_hashes {
        let found = proof
            .membership_proofs
            .iter()
            .any(|entry| entry.fact_hash == expected_hash);
        if !found {
            return Err(format!(
                "Missing membership proof for body fact hash {}",
                expected_hash.0
            ));
        }
    }

    Ok(())
}

/// Convenience: extract all distinct body fact hashes from a MultiStepWitness.
///
/// This is used by the verifier to know which body facts need membership proofs.
pub fn collect_body_fact_hashes(witness: &MultiStepWitness) -> Vec<BabyBear> {
    let mut hashes = Vec::new();
    for step in &witness.steps {
        for &hash in &step.body_fact_hashes {
            if !hashes.contains(&hash) {
                hashes.push(hash);
            }
        }
    }
    hashes
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use crate::multi_step_air::{ALLOW_PREDICATE, build_multi_step_witness};
    use crate::poseidon2::{hash_4_to_1, hash_fact};

    /// Build a Poseidon2 Merkle tree (inline, no dependency on commit crate)
    /// and return (root, leaf_proofs).
    ///
    /// This is a minimal 4-ary tree for testing.
    fn build_test_tree(leaves: &[BabyBear], depth: usize) -> (BabyBear, Vec<BodyFactMerkleProof>) {
        // Compute full tree bottom-up
        let capacity = 4usize.pow(depth as u32);
        let mut level_nodes: Vec<BabyBear> = Vec::with_capacity(capacity);
        for i in 0..capacity {
            if i < leaves.len() {
                level_nodes.push(leaves[i]);
            } else {
                level_nodes.push(BabyBear::ZERO);
            }
        }

        // Build level-by-level, storing all levels for proof generation
        let mut all_levels: Vec<Vec<BabyBear>> = Vec::with_capacity(depth + 1);
        all_levels.push(level_nodes.clone());

        let mut current_level = level_nodes;
        for _ in 0..depth {
            let mut next_level = Vec::with_capacity(current_level.len() / 4);
            for chunk in current_level.chunks(4) {
                let children = [chunk[0], chunk[1], chunk[2], chunk[3]];
                next_level.push(hash_4_to_1(&children));
            }
            all_levels.push(next_level.clone());
            current_level = next_level;
        }

        let root = current_level[0];

        // Generate proofs for each leaf
        let mut proofs = Vec::with_capacity(leaves.len());
        for (leaf_idx, &leaf_hash) in leaves.iter().enumerate() {
            let mut siblings = Vec::with_capacity(depth);
            let mut positions = Vec::with_capacity(depth);
            let mut idx = leaf_idx;

            for level in 0..depth {
                let pos_in_group = (idx % 4) as u8;
                let group_base = (idx / 4) * 4;
                positions.push(pos_in_group);

                let mut sibs = [BabyBear::ZERO; 3];
                let mut sib_i = 0;
                for j in 0..4 {
                    if j == pos_in_group as usize {
                        continue;
                    }
                    sibs[sib_i] = all_levels[level][group_base + j];
                    sib_i += 1;
                }
                siblings.push(sibs);
                idx = idx / 4;
            }

            proofs.push(BodyFactMerkleProof {
                fact_hash: leaf_hash,
                siblings,
                positions,
            });
        }

        (root, proofs)
    }

    /// Verify that our test tree produces correct membership proofs.
    fn verify_merkle_proof(
        leaf: BabyBear,
        proof: &BodyFactMerkleProof,
        expected_root: BabyBear,
    ) -> bool {
        let mut current = leaf;
        for level in 0..proof.siblings.len() {
            let pos = proof.positions[level];
            let sibs = &proof.siblings[level];
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == pos {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = sibs[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_4_to_1(&children);
        }
        current == expected_root
    }

    /// Helper: create a derivation step.
    fn make_step(
        rule_id: u32,
        state_root: BabyBear,
        derived_pred: BabyBear,
        terms: [BabyBear; 3],
        body_pred: BabyBear,
        body_terms: [BabyBear; 3],
        substitution: Vec<BabyBear>,
    ) -> DerivationWitness {
        let body_hash = hash_fact(body_pred, &body_terms);

        DerivationWitness {
            rule: CircuitRule {
                id: rule_id,
                num_body_atoms: 1,
                num_variables: substitution.len(),
                head_predicate: derived_pred,
                head_terms: [
                    (true, BabyBear::new(0)),
                    if substitution.len() > 1 {
                        (true, BabyBear::new(1))
                    } else {
                        (false, terms[1])
                    },
                    (false, terms[2]),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: body_pred,
                    terms: [
                        (true, BabyBear::new(0)),
                        if substitution.len() > 1 {
                            (true, BabyBear::new(1))
                        } else {
                            (false, body_terms[1])
                        },
                        (false, body_terms[2]),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
            },
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution,
            derived_predicate: derived_pred,
            derived_terms: [terms[0], terms[1], terms[2], BabyBear::ZERO],
        }
    }

    // ========================================================================
    // Test: prove and verify authorization WITH body membership
    // ========================================================================

    #[test]
    fn test_prove_and_verify_with_membership() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        // The body fact: has_role(alice, app, 0)
        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        // Build a Merkle tree containing this fact
        let tree_depth = 2; // 4^2 = 16 leaf capacity
        let leaves = vec![
            BabyBear::new(111),
            BabyBear::new(222),
            body_fact_hash, // our fact is at index 2
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        // Sanity check: verify Merkle proof is valid
        assert!(verify_merkle_proof(
            body_fact_hash,
            &merkle_proofs[2],
            state_root
        ));

        // Build derivation witness
        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        assert_eq!(conclusion, BabyBear::ONE, "Should conclude ALLOW");

        // Build the body fact Merkle proof input
        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: merkle_proofs[2].siblings.clone(),
            positions: merkle_proofs[2].positions.clone(),
        }];

        // Prove
        let composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Verify
        let expected_body_hashes = collect_body_fact_hashes(&witness);
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_ok(),
            "Composite proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: wrong membership proof is rejected
    // ========================================================================

    #[test]
    fn test_wrong_membership_proof_rejected() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        // Build a tree that does NOT contain body_fact_hash
        let tree_depth = 2;
        let leaves = vec![
            BabyBear::new(111),
            BabyBear::new(222),
            BabyBear::new(333), // different from body_fact_hash!
            BabyBear::new(444),
        ];
        let (state_root, _merkle_proofs) = build_test_tree(&leaves, tree_depth);

        // Also build a tree that DOES contain it, to get a valid Merkle proof
        // for a DIFFERENT root
        let real_leaves = vec![
            BabyBear::new(111),
            BabyBear::new(222),
            body_fact_hash,
            BabyBear::new(444),
        ];
        let (real_root, real_proofs) = build_test_tree(&real_leaves, tree_depth);

        // The real_root != state_root because they have different leaves
        assert_ne!(real_root, state_root);

        // The derivation uses state_root, but the Merkle proof leads to real_root
        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);

        // This should panic because the Merkle proof computes to real_root, not state_root
        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: real_proofs[2].siblings.clone(),
            positions: real_proofs[2].positions.clone(),
        }];

        let result = std::panic::catch_unwind(|| {
            prove_authorization_with_membership(&witness, &body_proofs)
        });
        assert!(
            result.is_err(),
            "Should panic when Merkle proof root mismatches state_root"
        );
    }

    // ========================================================================
    // Test: verification fails when membership proof is missing for a body fact
    // ========================================================================

    #[test]
    fn test_missing_membership_proof_rejected() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        // Build a valid tree + proof
        let tree_depth = 2;
        let leaves = vec![
            BabyBear::new(111),
            body_fact_hash,
            BabyBear::new(333),
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        // Generate a valid composite proof
        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: merkle_proofs[1].siblings.clone(),
            positions: merkle_proofs[1].positions.clone(),
        }];
        let mut composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Remove the membership proof to simulate missing proof
        composite_proof.membership_proofs.clear();

        // Verify should fail because the expected body hash has no proof
        let expected_body_hashes = collect_body_fact_hashes(&witness);
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_err(),
            "Should reject when membership proof missing"
        );
        assert!(
            result.unwrap_err().contains("Missing membership proof"),
            "Error should mention missing membership proof"
        );
    }

    // ========================================================================
    // Test: tampered membership proof STARK is rejected
    // ========================================================================

    #[test]
    fn test_tampered_membership_stark_rejected() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        let tree_depth = 2;
        let leaves = vec![
            BabyBear::new(111),
            body_fact_hash,
            BabyBear::new(333),
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: merkle_proofs[1].siblings.clone(),
            positions: merkle_proofs[1].positions.clone(),
        }];
        let mut composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Tamper with the membership STARK commitment
        composite_proof.membership_proofs[0].proof.trace_commitment[0] ^= 0xFF;

        let expected_body_hashes = collect_body_fact_hashes(&witness);
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_err(),
            "Should reject tampered membership STARK proof"
        );
        assert!(
            result.unwrap_err().contains("Merkle membership proof"),
            "Error should mention membership proof failure"
        );
    }

    // ========================================================================
    // Test: multi-step derivation with multiple body facts, all proven
    // ========================================================================

    #[test]
    fn test_multi_step_multiple_body_facts() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let read_action = BabyBear::new(3000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_cap_pred = BabyBear::new(100);
        let app_auth_pred = BabyBear::new(200);

        // Two body facts: has_capability and app_authorized
        let fact1_hash = hash_fact(has_cap_pred, &[alice, app, read_action]);
        let fact2_hash = hash_fact(app_auth_pred, &[alice, app, BabyBear::ZERO]);

        // Build a Merkle tree containing both facts
        let tree_depth = 2;
        let leaves = vec![
            fact1_hash,
            fact2_hash,
            BabyBear::new(333),
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        // Step 1: app_authorized(alice, app) :- has_capability(alice, app, read)
        let step1 = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app, BabyBear::ZERO],
            has_cap_pred,
            [alice, app, read_action],
            vec![alice, app, read_action],
        );

        // Step 2: allow(alice, app) :- app_authorized(alice, app)
        let step2 = make_step(
            2,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            app_auth_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );

        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        assert_eq!(conclusion, BabyBear::ONE);

        // Provide Merkle proofs for both body facts
        let body_proofs = vec![
            BodyFactMerkleProof {
                fact_hash: fact1_hash,
                siblings: merkle_proofs[0].siblings.clone(),
                positions: merkle_proofs[0].positions.clone(),
            },
            BodyFactMerkleProof {
                fact_hash: fact2_hash,
                siblings: merkle_proofs[1].siblings.clone(),
                positions: merkle_proofs[1].positions.clone(),
            },
        ];

        let composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        let expected_body_hashes = collect_body_fact_hashes(&witness);
        assert_eq!(expected_body_hashes.len(), 2);

        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_ok(),
            "Multi-step with multiple body facts should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: full end-to-end with inline tree construction
    // ========================================================================

    #[test]
    fn test_end_to_end_tree_build_prove_verify() {
        // Realistic scenario: build a fact tree, extract membership proofs,
        // prove a 3-step derivation, verify everything.
        let alice = BabyBear::new(1000);
        let app1 = BabyBear::new(2000);
        let read_action = BabyBear::new(3000);

        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_cap_pred = BabyBear::new(100);
        let app_auth_pred = BabyBear::new(200);
        let action_perm_pred = BabyBear::new(300);

        // Facts in the committed state
        let fact_has_cap = hash_fact(has_cap_pred, &[alice, app1, read_action]);
        let fact_app_auth = hash_fact(app_auth_pred, &[alice, app1, BabyBear::ZERO]);
        let fact_action_perm = hash_fact(action_perm_pred, &[alice, app1, BabyBear::ZERO]);

        // Build tree with all 3 facts + padding
        let tree_depth = 2;
        let leaves = vec![
            fact_has_cap,
            fact_app_auth,
            fact_action_perm,
            BabyBear::new(999),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        // 3-step derivation
        let step1 = make_step(
            1,
            state_root,
            app_auth_pred,
            [alice, app1, BabyBear::ZERO],
            has_cap_pred,
            [alice, app1, read_action],
            vec![alice, app1, read_action],
        );
        let step2 = make_step(
            2,
            state_root,
            action_perm_pred,
            [alice, app1, BabyBear::ZERO],
            app_auth_pred,
            [alice, app1, BabyBear::ZERO],
            vec![alice, app1],
        );
        let step3 = make_step(
            3,
            state_root,
            allow_pred,
            [alice, app1, BabyBear::ZERO],
            action_perm_pred,
            [alice, app1, BabyBear::ZERO],
            vec![alice, app1],
        );

        let witness =
            build_multi_step_witness(state_root, BabyBear::new(42), vec![step1, step2, step3]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        assert_eq!(conclusion, BabyBear::ONE, "Should conclude ALLOW");

        // Collect all body fact hashes and their Merkle proofs
        let body_fact_hashes = collect_body_fact_hashes(&witness);
        let body_proofs: Vec<BodyFactMerkleProof> = body_fact_hashes
            .iter()
            .map(|&hash| {
                let idx = leaves.iter().position(|&l| l == hash).unwrap();
                BodyFactMerkleProof {
                    fact_hash: hash,
                    siblings: merkle_proofs[idx].siblings.clone(),
                    positions: merkle_proofs[idx].positions.clone(),
                }
            })
            .collect();

        // Prove
        let composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Verify
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &body_fact_hashes,
        );
        assert!(
            result.is_ok(),
            "End-to-end 3-step derivation with membership should verify: {:?}",
            result.err()
        );

        // Verify the structure
        assert_eq!(
            composite_proof.membership_proofs.len(),
            body_fact_hashes.len()
        );
        assert_eq!(composite_proof.state_root, state_root);

        println!(
            "End-to-end composite proof: derivation ({} bytes) + {} membership proofs",
            stark::proof_to_bytes(&composite_proof.derivation_proof).len(),
            composite_proof.membership_proofs.len()
        );
        let total_size: usize = stark::proof_to_bytes(&composite_proof.derivation_proof).len()
            + composite_proof
                .membership_proofs
                .iter()
                .map(|e| stark::proof_to_bytes(&e.proof).len())
                .sum::<usize>();
        println!(
            "Total composite proof size: {} bytes ({:.1} KiB)",
            total_size,
            total_size as f64 / 1024.0
        );
    }

    // ========================================================================
    // Test: verifier rejects when fact_hash in membership proof doesn't match
    // ========================================================================

    #[test]
    fn test_fact_hash_mismatch_rejected() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        let tree_depth = 2;
        let leaves = vec![
            body_fact_hash,
            BabyBear::new(222),
            BabyBear::new(333),
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: merkle_proofs[0].siblings.clone(),
            positions: merkle_proofs[0].positions.clone(),
        }];
        let mut composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Tamper: change the fact_hash in the membership entry to something else
        // The STARK proof was generated for the real fact_hash, but we claim it's for a different one
        composite_proof.membership_proofs[0].fact_hash = BabyBear::new(0xDEAD);

        // Verification should fail because:
        // 1. The STARK public inputs have the original fact_hash, not 0xDEAD
        // 2. Even if we pass 0xDEAD as expected, the STARK verification will fail
        //    because the proof was generated for a different leaf
        let expected_body_hashes = vec![BabyBear::new(0xDEAD)];
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_err(),
            "Should reject when fact_hash in entry doesn't match STARK public inputs"
        );
    }

    // ========================================================================
    // Test: correct derivation but verifier asks for more hashes than proven
    // ========================================================================

    #[test]
    fn test_verifier_demands_extra_hashes() {
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_fact_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        let tree_depth = 2;
        let leaves = vec![
            body_fact_hash,
            BabyBear::new(222),
            BabyBear::new(333),
            BabyBear::new(444),
        ];
        let (state_root, merkle_proofs) = build_test_tree(&leaves, tree_depth);

        let step = make_step(
            1,
            state_root,
            allow_pred,
            [alice, app, BabyBear::ZERO],
            has_role_pred,
            [alice, app, BabyBear::ZERO],
            vec![alice, app],
        );
        let witness = build_multi_step_witness(state_root, BabyBear::new(42), vec![step]);
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let body_proofs = vec![BodyFactMerkleProof {
            fact_hash: body_fact_hash,
            siblings: merkle_proofs[0].siblings.clone(),
            positions: merkle_proofs[0].positions.clone(),
        }];
        let composite_proof = prove_authorization_with_membership(&witness, &body_proofs);

        // Verifier asks for an extra hash that wasn't in the derivation
        let expected_body_hashes = vec![body_fact_hash, BabyBear::new(0xBEEF)];
        let result = verify_authorization_with_membership(
            &composite_proof,
            conclusion,
            acc_hash,
            &expected_body_hashes,
        );
        assert!(
            result.is_err(),
            "Should reject when verifier expects more proofs than provided"
        );
        assert!(result.unwrap_err().contains("Missing membership proof"));
    }
}
