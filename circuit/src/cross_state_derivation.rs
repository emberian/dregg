//! Cross-state derivation: composition-based proofs combining facts from multiple sources.
//!
//! When an authorization decision depends on facts from multiple independent state roots
//! (e.g., different organizations), a single derivation STARK is insufficient because
//! each STARK binds to exactly one `state_root`. This module solves that by composing
//! per-source derivation proofs with a final composition proof under a merged root.
//!
//! # Architecture
//!
//! ```text
//! Source 1 (root R_1)        Source 2 (root R_2)        ... Source N (root R_N)
//!   │                           │                             │
//!   ▼                           ▼                             ▼
//! DerivationSTARK            DerivationSTARK              DerivationSTARK
//! "under R_1, derived F_1"   "under R_2, derived F_2"    "under R_N, derived F_N"
//!   │                           │                             │
//!   └───────────────────────────┼─────────────────────────────┘
//!                               │
//!                               ▼
//!                     composition_root = Poseidon2 tree of [F_1, F_2, ..., F_N]
//!                               │
//!                               ▼
//!                     Final DerivationSTARK
//!                     "under composition_root, derived final_fact"
//! ```
//!
//! The composition root is a Poseidon2 4-ary Merkle tree root built over the
//! intermediate derived fact hashes. The final derivation STARK treats this root as
//! its state root, and the intermediate fact hashes as body facts.
//!
//! # Security Properties
//!
//! 1. Each source derivation is independently sound (STARK proof under source root).
//! 2. The composition root cryptographically commits to exactly the intermediate facts.
//! 3. The final derivation is sound under the composition root (the combining rule is valid).
//! 4. A verifier checks all sub-proofs, recomputes the composition root, and verifies
//!    the final proof against it.

use crate::body_membership::MembershipEntry;
use crate::derivation_air::{BodyAtomPattern, CircuitRule, DerivationStarkAir, DerivationWitness};
use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;
use crate::stark::{self, StarkProof};
use serde::{Deserialize, Serialize};

// ============================================================================
// Data structures
// ============================================================================

/// A cross-state derivation proof bundling per-source derivation STARKs and a
/// composition proof that combines their intermediate derived facts.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrossStateDerivationProof {
    /// Per-source derivation: each proves "under root R_i, I derived fact F_i".
    pub source_derivations: Vec<SourceDerivation>,
    /// The composition: proves the final derivation under a merged root
    /// that commits only to the derived intermediate facts.
    pub final_derivation: StarkProof,
    /// The merged/composition root (public input to final_derivation).
    pub composition_root: BabyBear,
    /// Source roots (one per source_derivations entry).
    pub source_roots: Vec<BabyBear>,
    /// The final derived fact hash.
    pub final_derived_hash: BabyBear,
}

/// A single source's derivation contribution to the cross-state proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceDerivation {
    /// The state root this derivation operates under.
    pub source_root: BabyBear,
    /// STARK proof of derivation under `source_root`.
    pub proof: StarkProof,
    /// The derived fact hash (output of this derivation).
    pub derived_fact_hash: BabyBear,
    /// Optional: Merkle membership proofs for body facts used in this derivation.
    pub membership_proofs: Vec<MembershipEntry>,
}

/// Input for a single source derivation in the cross-state proof.
#[derive(Clone, Debug)]
pub struct SourceInput {
    /// State root for this source.
    pub source_root: BabyBear,
    /// The derivation witness (rule application under source_root).
    pub witness: DerivationWitness,
    /// Optional membership proofs (body fact Merkle proofs for this source).
    pub membership_proofs: Vec<MembershipEntry>,
}

/// The combining rule specification: how intermediate facts combine into a final fact.
#[derive(Clone, Debug)]
pub struct CombiningRule {
    /// Rule ID for the combining derivation.
    pub rule_id: u32,
    /// The final derived predicate.
    pub head_predicate: BabyBear,
    /// Head term patterns: (is_variable, value_or_var_index).
    pub head_terms: [(bool, BabyBear); 4],
    /// Substitution values for the combining rule.
    pub substitution: Vec<BabyBear>,
    /// The final derived terms (result of applying the combining rule).
    pub derived_terms: [BabyBear; 4],
}

// ============================================================================
// Composition root computation
// ============================================================================

/// Build a Poseidon2 4-ary Merkle tree root from a set of fact hashes.
///
/// This is the composition root: it commits to exactly the intermediate derived
/// facts from all source derivations. The tree is padded with zeros if the number
/// of facts is not a power of 4.
///
/// `depth` controls the tree depth. Capacity = 4^depth leaves.
fn build_composition_root(fact_hashes: &[BabyBear], depth: usize) -> BabyBear {
    let capacity = 4usize.pow(depth as u32);
    assert!(
        fact_hashes.len() <= capacity,
        "Too many facts ({}) for tree depth {} (capacity {})",
        fact_hashes.len(),
        depth,
        capacity
    );

    let mut level: Vec<BabyBear> = Vec::with_capacity(capacity);
    for i in 0..capacity {
        if i < fact_hashes.len() {
            level.push(fact_hashes[i]);
        } else {
            level.push(BabyBear::ZERO);
        }
    }

    for _ in 0..depth {
        let mut next = Vec::with_capacity(level.len() / 4);
        for chunk in level.chunks(4) {
            next.push(hash_4_to_1(&[chunk[0], chunk[1], chunk[2], chunk[3]]));
        }
        level = next;
    }

    level[0]
}

/// Default composition tree depth. Depth 2 = 16 leaf capacity (supports up to 16 sources).
const DEFAULT_COMPOSITION_DEPTH: usize = 2;

// ============================================================================
// Proving
// ============================================================================

/// Prove a cross-state derivation combining facts from multiple sources.
///
/// # Arguments
///
/// * `sources` - Per-source derivation inputs (root, witness, membership proofs).
/// * `combining_rule` - How the intermediate facts combine into the final derived fact.
///
/// # Returns
///
/// A `CrossStateDerivationProof` containing all sub-proofs and the composition proof.
///
/// # Panics
///
/// Panics if `sources` is empty or if a source derivation fails to produce a valid STARK.
pub fn prove_cross_state_derivation(
    sources: &[SourceInput],
    combining_rule: &CombiningRule,
) -> CrossStateDerivationProof {
    prove_cross_state_derivation_with_depth(sources, combining_rule, DEFAULT_COMPOSITION_DEPTH)
}

/// Like `prove_cross_state_derivation` but with configurable composition tree depth.
pub fn prove_cross_state_derivation_with_depth(
    sources: &[SourceInput],
    combining_rule: &CombiningRule,
    composition_depth: usize,
) -> CrossStateDerivationProof {
    assert!(!sources.is_empty(), "Must have at least one source");

    // Step 1: Prove each source derivation independently.
    let mut source_derivations = Vec::with_capacity(sources.len());
    let mut intermediate_fact_hashes = Vec::with_capacity(sources.len());
    let mut source_roots = Vec::with_capacity(sources.len());

    for source in sources {
        let derived_hash = source.witness.derived_hash();

        // Generate the STARK proof for this source derivation.
        let proof = prove_source_derivation_stark(&source.witness);

        source_roots.push(source.source_root);
        intermediate_fact_hashes.push(derived_hash);
        source_derivations.push(SourceDerivation {
            source_root: source.source_root,
            proof,
            derived_fact_hash: derived_hash,
            membership_proofs: source.membership_proofs.clone(),
        });
    }

    // Step 2: Compute the composition root from intermediate fact hashes.
    let composition_root = build_composition_root(&intermediate_fact_hashes, composition_depth);

    // Step 3: Build and prove the final derivation under the composition root.
    // The body facts are the intermediate derived fact hashes.
    let final_witness =
        build_final_derivation_witness(composition_root, &intermediate_fact_hashes, combining_rule);
    let final_derived_hash = final_witness.derived_hash();
    let final_proof = prove_source_derivation_stark(&final_witness);

    CrossStateDerivationProof {
        source_derivations,
        final_derivation: final_proof,
        composition_root,
        source_roots,
        final_derived_hash,
    }
}

/// Generate a STARK proof for a single derivation witness.
fn prove_source_derivation_stark(witness: &DerivationWitness) -> StarkProof {
    use crate::constraint_prover::Air;
    use crate::derivation_air::DerivationAir;

    let air = DerivationStarkAir::new(witness.clone());
    let derivation_air = DerivationAir::new(witness.clone());

    // Generate trace and public inputs.
    let (trace, public_inputs) = derivation_air.generate_trace();

    // Pad to at least 2 rows (power-of-two requirement for STARK).
    let padded_len = trace.len().next_power_of_two().max(2);
    let mut padded_trace = trace;
    while padded_trace.len() < padded_len {
        padded_trace.push(padded_trace.last().unwrap().clone());
    }

    stark::prove(&air, &padded_trace, &public_inputs)
}

/// Build the final combining derivation witness.
///
/// The final derivation uses the composition root as its state root, and
/// the intermediate derived fact hashes as its body facts.
fn build_final_derivation_witness(
    composition_root: BabyBear,
    intermediate_facts: &[BabyBear],
    combining_rule: &CombiningRule,
) -> DerivationWitness {
    // Build body atom patterns: one per intermediate fact.
    // Each body atom uses a unique predicate that matches via the fact hash.
    // In the circuit, the body_fact_hashes directly provide the membership evidence.
    let num_body = intermediate_facts.len();
    let body_atoms: Vec<BodyAtomPattern> = (0..num_body)
        .map(|_| BodyAtomPattern {
            predicate: BabyBear::ZERO, // placeholder; body hash is what matters
            terms: [
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
        })
        .collect();

    let rule = CircuitRule {
        id: combining_rule.rule_id,
        num_body_atoms: num_body,
        num_variables: combining_rule.substitution.len(),
        head_predicate: combining_rule.head_predicate,
        head_terms: combining_rule.head_terms,
        body_atoms,
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: None,
        lt_check: None,
    };

    DerivationWitness {
        rule,
        state_root: composition_root,
        body_fact_hashes: intermediate_facts.to_vec(),
        substitution: combining_rule.substitution.clone(),
        derived_predicate: combining_rule.head_predicate,
        derived_terms: combining_rule.derived_terms,
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}

// ============================================================================
// Verification
// ============================================================================

/// Verify a cross-state derivation proof.
///
/// The verifier checks:
/// 1. Each source derivation STARK is valid (proves derivation under its source root).
/// 2. The composition root is correctly computed from the intermediate fact hashes.
/// 3. The final derivation STARK is valid under the composition root.
/// 4. The final derived fact hash matches the proof's claim.
/// 5. Source roots in the proof match those embedded in the sub-proofs.
///
/// # Arguments
///
/// * `proof` - The cross-state derivation proof to verify.
/// * `expected_source_roots` - Expected source roots (must match proof.source_roots).
/// * `expected_final_hash` - Expected final derived fact hash.
///
/// # Returns
///
/// `Ok(())` if valid, `Err(reason)` otherwise.
pub fn verify_cross_state_derivation(
    proof: &CrossStateDerivationProof,
    expected_source_roots: &[BabyBear],
    expected_final_hash: BabyBear,
) -> Result<(), String> {
    verify_cross_state_derivation_with_depth(
        proof,
        expected_source_roots,
        expected_final_hash,
        DEFAULT_COMPOSITION_DEPTH,
    )
}

/// Like `verify_cross_state_derivation` but with configurable composition tree depth.
pub fn verify_cross_state_derivation_with_depth(
    proof: &CrossStateDerivationProof,
    expected_source_roots: &[BabyBear],
    expected_final_hash: BabyBear,
    composition_depth: usize,
) -> Result<(), String> {
    // Check structural consistency.
    if proof.source_derivations.is_empty() {
        return Err("No source derivations".to_string());
    }
    if proof.source_roots.len() != proof.source_derivations.len() {
        return Err(format!(
            "Source roots count ({}) != source derivations count ({})",
            proof.source_roots.len(),
            proof.source_derivations.len()
        ));
    }
    if expected_source_roots.len() != proof.source_roots.len() {
        return Err(format!(
            "Expected {} source roots but proof has {}",
            expected_source_roots.len(),
            proof.source_roots.len()
        ));
    }

    // Check 1: Source roots match expectations.
    for (i, (&expected, &actual)) in expected_source_roots
        .iter()
        .zip(proof.source_roots.iter())
        .enumerate()
    {
        if expected != actual {
            return Err(format!(
                "Source root {} mismatch: expected {}, got {}",
                i, expected.0, actual.0
            ));
        }
    }

    // Check 2: Verify each source derivation STARK.
    let mut intermediate_facts = Vec::with_capacity(proof.source_derivations.len());
    for (i, source) in proof.source_derivations.iter().enumerate() {
        // Verify the source root matches.
        if source.source_root != proof.source_roots[i] {
            return Err(format!(
                "Source derivation {} root ({}) != declared source root ({})",
                i, source.source_root.0, proof.source_roots[i].0
            ));
        }

        // Verify the STARK proof. Public inputs are [state_root, derived_fact_hash, 0, 0, 0].
        let public_inputs = vec![
            source.source_root,
            source.derived_fact_hash,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        crate::derivation_air::verify_derivation_stark(&source.proof, &public_inputs)
            .map_err(|e| format!("Source derivation {} STARK verification failed: {}", i, e))?;

        intermediate_facts.push(source.derived_fact_hash);
    }

    // Check 3: Recompute composition root and verify it matches.
    let recomputed_root = build_composition_root(&intermediate_facts, composition_depth);
    if recomputed_root != proof.composition_root {
        return Err(format!(
            "Composition root mismatch: recomputed {}, proof claims {}",
            recomputed_root.0, proof.composition_root.0
        ));
    }

    // Check 4: Verify the final derivation STARK under the composition root.
    let final_public_inputs = vec![
        proof.composition_root,
        proof.final_derived_hash,
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];
    crate::derivation_air::verify_derivation_stark(&proof.final_derivation, &final_public_inputs)
        .map_err(|e| format!("Final derivation STARK verification failed: {}", e))?;

    // Check 5: Final derived hash matches expectation.
    if proof.final_derived_hash != expected_final_hash {
        return Err(format!(
            "Final derived hash mismatch: expected {}, got {}",
            expected_final_hash.0, proof.final_derived_hash.0
        ));
    }

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_fact;

    /// Helper: build a simple derivation witness for a source.
    /// Derives `derived_pred(term0, term1, 0, 0)` from `body_pred(term0, term1, 0)`.
    fn make_source_witness(
        source_root: BabyBear,
        rule_id: u32,
        derived_pred: BabyBear,
        body_pred: BabyBear,
        term0: BabyBear,
        term1: BabyBear,
    ) -> DerivationWitness {
        let body_hash = hash_fact(body_pred, &[term0, term1, BabyBear::ZERO]);

        DerivationWitness {
            rule: CircuitRule {
                id: rule_id,
                num_body_atoms: 1,
                num_variables: 2,
                head_predicate: derived_pred,
                head_terms: [
                    (true, BabyBear::new(0)), // var X
                    (true, BabyBear::new(1)), // var Y
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: body_pred,
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
            state_root: source_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![term0, term1],
            derived_predicate: derived_pred,
            derived_terms: [term0, term1, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        }
    }

    // ========================================================================
    // Test: 2-source cross-state derivation, prove and verify
    // ========================================================================

    #[test]
    fn test_cross_state_two_sources_prove_verify() {
        // Source 1: Org A's state. Has fact: has_role(alice, admin)
        // Derivation under R_1: has_role(alice, admin) -> org_a_cleared(alice, admin)
        let root_a = BabyBear::new(11111);
        let alice = BabyBear::new(1000);
        let admin = BabyBear::new(2000);
        let has_role_pred = BabyBear::new(100);
        let org_a_cleared_pred = BabyBear::new(200);

        let witness_a =
            make_source_witness(root_a, 1, org_a_cleared_pred, has_role_pred, alice, admin);

        // Source 2: Org B's state. Has fact: resource_available(alice, file)
        // Derivation under R_2: resource_available(alice, file) -> org_b_grants(alice, file)
        let root_b = BabyBear::new(22222);
        let file = BabyBear::new(3000);
        let resource_pred = BabyBear::new(300);
        let org_b_grants_pred = BabyBear::new(400);

        let witness_b =
            make_source_witness(root_b, 2, org_b_grants_pred, resource_pred, alice, file);

        // Build source inputs.
        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a.clone(),
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b.clone(),
                membership_proofs: vec![],
            },
        ];

        // Combining rule: from org_a_cleared(alice, admin) + org_b_grants(alice, file)
        // derive: cross_authorized(alice, admin, 0, 0)
        // The combining rule uses the intermediate fact hashes as body facts.
        let cross_auth_pred = BabyBear::new(500);
        let combining_rule = CombiningRule {
            rule_id: 99,
            head_predicate: cross_auth_pred,
            head_terms: [
                (true, BabyBear::new(0)), // var 0 = alice
                (true, BabyBear::new(1)), // var 1 = admin
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice, admin],
            derived_terms: [alice, admin, BabyBear::ZERO, BabyBear::ZERO],
        };

        // Prove.
        let proof = prove_cross_state_derivation(&sources, &combining_rule);

        // Verify structure.
        assert_eq!(proof.source_derivations.len(), 2);
        assert_eq!(proof.source_roots.len(), 2);
        assert_eq!(proof.source_roots[0], root_a);
        assert_eq!(proof.source_roots[1], root_b);

        // Compute expected final hash.
        let expected_final_hash = hash_fact(
            cross_auth_pred,
            &[alice, admin, BabyBear::ZERO, BabyBear::ZERO],
        );
        assert_eq!(proof.final_derived_hash, expected_final_hash);

        // Verify.
        let result = verify_cross_state_derivation(&proof, &[root_a, root_b], expected_final_hash);
        assert!(
            result.is_ok(),
            "Cross-state 2-source proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: 3-source cross-state derivation
    // ========================================================================

    #[test]
    fn test_cross_state_three_sources() {
        let root_a = BabyBear::new(11111);
        let root_b = BabyBear::new(22222);
        let root_c = BabyBear::new(33333);
        let alice = BabyBear::new(1000);
        let val_a = BabyBear::new(2000);
        let val_b = BabyBear::new(3000);
        let val_c = BabyBear::new(4000);

        let pred_a = BabyBear::new(100);
        let pred_b = BabyBear::new(200);
        let pred_c = BabyBear::new(300);
        let derived_a = BabyBear::new(101);
        let derived_b = BabyBear::new(201);
        let derived_c = BabyBear::new(301);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val_a);
        let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val_b);
        let witness_c = make_source_witness(root_c, 3, derived_c, pred_c, alice, val_c);

        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_c,
                witness: witness_c,
                membership_proofs: vec![],
            },
        ];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let proof = prove_cross_state_derivation(&sources, &combining_rule);

        assert_eq!(proof.source_derivations.len(), 3);
        assert_eq!(proof.source_roots, vec![root_a, root_b, root_c]);

        let expected_final = hash_fact(
            final_pred,
            &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );

        let result =
            verify_cross_state_derivation(&proof, &[root_a, root_b, root_c], expected_final);
        assert!(
            result.is_ok(),
            "3-source cross-state proof should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: wrong source root is rejected
    // ========================================================================

    #[test]
    fn test_cross_state_wrong_source_root_rejected() {
        let root_a = BabyBear::new(11111);
        let root_b = BabyBear::new(22222);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);

        let pred_a = BabyBear::new(100);
        let pred_b = BabyBear::new(200);
        let derived_a = BabyBear::new(101);
        let derived_b = BabyBear::new(201);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);
        let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val);

        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b,
                membership_proofs: vec![],
            },
        ];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let proof = prove_cross_state_derivation(&sources, &combining_rule);
        let expected_final = hash_fact(
            final_pred,
            &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );

        // Verify with wrong expected source roots.
        let result = verify_cross_state_derivation(
            &proof,
            &[BabyBear::new(99999), root_b], // wrong root_a
            expected_final,
        );
        assert!(result.is_err(), "Wrong source root should be rejected");
        assert!(
            result.unwrap_err().contains("Source root 0 mismatch"),
            "Should identify which root is wrong"
        );
    }

    // ========================================================================
    // Test: tampered source STARK is rejected
    // ========================================================================

    #[test]
    fn test_cross_state_tampered_source_stark_rejected() {
        let root_a = BabyBear::new(11111);
        let root_b = BabyBear::new(22222);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);

        let pred_a = BabyBear::new(100);
        let pred_b = BabyBear::new(200);
        let derived_a = BabyBear::new(101);
        let derived_b = BabyBear::new(201);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);
        let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val);

        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b,
                membership_proofs: vec![],
            },
        ];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let mut proof = prove_cross_state_derivation(&sources, &combining_rule);
        let expected_final = hash_fact(
            final_pred,
            &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );

        // Tamper with source derivation 0's STARK.
        proof.source_derivations[0].proof.trace_commitment[0] ^= 0xFF;

        let result = verify_cross_state_derivation(&proof, &[root_a, root_b], expected_final);
        assert!(result.is_err(), "Tampered STARK should be rejected");
        assert!(
            result
                .unwrap_err()
                .contains("Source derivation 0 STARK verification failed"),
        );
    }

    // ========================================================================
    // Test: tampered final derivation STARK is rejected
    // ========================================================================

    #[test]
    fn test_cross_state_tampered_final_stark_rejected() {
        let root_a = BabyBear::new(11111);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);
        let pred_a = BabyBear::new(100);
        let derived_a = BabyBear::new(101);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);

        let sources = vec![SourceInput {
            source_root: root_a,
            witness: witness_a,
            membership_proofs: vec![],
        }];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let mut proof = prove_cross_state_derivation(&sources, &combining_rule);
        let expected_final = hash_fact(
            final_pred,
            &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );

        // Tamper with the final derivation STARK.
        proof.final_derivation.trace_commitment[0] ^= 0xFF;

        let result = verify_cross_state_derivation(&proof, &[root_a], expected_final);
        assert!(result.is_err(), "Tampered final STARK should be rejected");
        assert!(
            result
                .unwrap_err()
                .contains("Final derivation STARK verification failed"),
        );
    }

    // ========================================================================
    // Test: wrong final hash is rejected
    // ========================================================================

    #[test]
    fn test_cross_state_wrong_final_hash_rejected() {
        let root_a = BabyBear::new(11111);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);
        let pred_a = BabyBear::new(100);
        let derived_a = BabyBear::new(101);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);

        let sources = vec![SourceInput {
            source_root: root_a,
            witness: witness_a,
            membership_proofs: vec![],
        }];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let proof = prove_cross_state_derivation(&sources, &combining_rule);

        // Verify with wrong expected final hash.
        let result = verify_cross_state_derivation(
            &proof,
            &[root_a],
            BabyBear::new(0xDEAD), // wrong expected hash
        );
        assert!(result.is_err(), "Wrong final hash should be rejected");
        assert!(result.unwrap_err().contains("Final derived hash mismatch"),);
    }

    // ========================================================================
    // Test: composition root correctness (verifier recomputes it)
    // ========================================================================

    #[test]
    fn test_cross_state_composition_root_tampered() {
        let root_a = BabyBear::new(11111);
        let root_b = BabyBear::new(22222);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);
        let pred_a = BabyBear::new(100);
        let pred_b = BabyBear::new(200);
        let derived_a = BabyBear::new(101);
        let derived_b = BabyBear::new(201);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);
        let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val);

        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b,
                membership_proofs: vec![],
            },
        ];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let mut proof = prove_cross_state_derivation(&sources, &combining_rule);
        let expected_final = hash_fact(
            final_pred,
            &[alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );

        // Tamper with composition root (will cause recomputation mismatch).
        proof.composition_root = BabyBear::new(0xBAD);

        let result = verify_cross_state_derivation(&proof, &[root_a, root_b], expected_final);
        assert!(
            result.is_err(),
            "Tampered composition root should be rejected"
        );
        assert!(result.unwrap_err().contains("Composition root mismatch"),);
    }

    // ========================================================================
    // Test: composition root is a proper Poseidon2 Merkle tree
    // ========================================================================

    #[test]
    fn test_composition_root_deterministic() {
        let facts = vec![BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)];

        let root1 = build_composition_root(&facts, 2);
        let root2 = build_composition_root(&facts, 2);
        assert_eq!(root1, root2, "Composition root should be deterministic");

        // Different facts -> different root.
        let facts2 = vec![
            BabyBear::new(111),
            BabyBear::new(222),
            BabyBear::new(444), // different
        ];
        let root3 = build_composition_root(&facts2, 2);
        assert_ne!(root1, root3, "Different facts should give different root");
    }

    // ========================================================================
    // Test: single source also works (degenerate case)
    // ========================================================================

    #[test]
    fn test_cross_state_single_source() {
        let root = BabyBear::new(55555);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);
        let body_pred = BabyBear::new(100);
        let intermediate_pred = BabyBear::new(200);

        let witness = make_source_witness(root, 1, intermediate_pred, body_pred, alice, val);

        let sources = vec![SourceInput {
            source_root: root,
            witness,
            membership_proofs: vec![],
        }];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 1,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice, val],
            derived_terms: [alice, val, BabyBear::ZERO, BabyBear::ZERO],
        };

        let proof = prove_cross_state_derivation(&sources, &combining_rule);
        let expected_final = hash_fact(final_pred, &[alice, val, BabyBear::ZERO, BabyBear::ZERO]);

        let result = verify_cross_state_derivation(&proof, &[root], expected_final);
        assert!(
            result.is_ok(),
            "Single-source cross-state should verify: {:?}",
            result.err()
        );
    }

    // ========================================================================
    // Test: proof size reporting
    // ========================================================================

    #[test]
    fn test_cross_state_proof_size() {
        let root_a = BabyBear::new(11111);
        let root_b = BabyBear::new(22222);
        let alice = BabyBear::new(1000);
        let val = BabyBear::new(2000);
        let pred_a = BabyBear::new(100);
        let pred_b = BabyBear::new(200);
        let derived_a = BabyBear::new(101);
        let derived_b = BabyBear::new(201);

        let witness_a = make_source_witness(root_a, 1, derived_a, pred_a, alice, val);
        let witness_b = make_source_witness(root_b, 2, derived_b, pred_b, alice, val);

        let sources = vec![
            SourceInput {
                source_root: root_a,
                witness: witness_a,
                membership_proofs: vec![],
            },
            SourceInput {
                source_root: root_b,
                witness: witness_b,
                membership_proofs: vec![],
            },
        ];

        let final_pred = BabyBear::new(999);
        let combining_rule = CombiningRule {
            rule_id: 50,
            head_predicate: final_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            substitution: vec![alice],
            derived_terms: [alice, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        };

        let proof = prove_cross_state_derivation(&sources, &combining_rule);

        // Report sizes.
        let source_sizes: Vec<usize> = proof
            .source_derivations
            .iter()
            .map(|s| stark::proof_to_bytes(&s.proof).len())
            .collect();
        let final_size = stark::proof_to_bytes(&proof.final_derivation).len();
        let total: usize = source_sizes.iter().sum::<usize>() + final_size;

        println!(
            "Cross-state proof (2 sources): source STARKs = {:?} bytes, final = {} bytes, total = {} bytes ({:.1} KiB)",
            source_sizes,
            final_size,
            total,
            total as f64 / 1024.0
        );

        // Sanity: total should be reasonable (each STARK is ~20-60 KiB for derivation AIR).
        assert!(total > 0, "Proof should have non-zero size");
    }
}
