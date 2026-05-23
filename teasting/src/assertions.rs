//! Custom assertion helpers for distributed state verification.
//!
//! These go beyond simple `assert_eq!` to provide domain-specific failure messages
//! that make debugging integration test failures tractable.

use pyana_bridge::BridgePresentationProof;
#[allow(deprecated)] // test helpers intentionally use the simpler legacy verification API
use pyana_bridge::present::verify_presentation;
use pyana_circuit::BabyBear;
use pyana_circuit::predicate_air::PredicateProof;

/// Assert that a presentation proof is structurally valid (all sub-proofs present and consistent).
pub fn assert_proof_valid(proof: &BridgePresentationProof) {
    assert!(
        proof.is_valid(),
        "Presentation proof failed validity check: constraint_checked={}, fold_count={}",
        proof.is_constraint_checked(),
        proof.chain_length,
    );
}

/// Assert that a presentation proof verifies against a given federation root.
#[allow(deprecated)]
pub fn assert_proof_verifies(proof: &BridgePresentationProof, federation_root: &[u8; 32]) {
    assert!(
        verify_presentation(proof, federation_root),
        "Presentation proof failed verification against federation root {:?}",
        &federation_root[..8],
    );
}

/// Assert that a presentation proof does NOT verify (expected failure case).
#[allow(deprecated)]
pub fn assert_proof_rejects(proof: &BridgePresentationProof, federation_root: &[u8; 32]) {
    assert!(
        !verify_presentation(proof, federation_root),
        "Presentation proof SHOULD have been rejected but was accepted",
    );
}

/// Assert that a predicate proof verifies against expected public inputs.
pub fn assert_predicate_verifies(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) {
    use pyana_circuit::predicate_air::verify_predicate;
    assert!(
        verify_predicate(proof, threshold, fact_commitment),
        "Predicate proof failed verification: threshold={:?}, fact_commitment={:?}",
        threshold,
        fact_commitment,
    );
}

/// Assert that a predicate proof does NOT verify (forge detection).
pub fn assert_predicate_rejects(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) {
    use pyana_circuit::predicate_air::verify_predicate;
    assert!(
        !verify_predicate(proof, threshold, fact_commitment),
        "Predicate proof SHOULD have been rejected but passed verification",
    );
}

/// Assert that two byte slices are NOT equal (unlinkability check).
pub fn assert_unlinkable(a: &[u8], b: &[u8], context: &str) {
    assert_ne!(
        a, b,
        "Unlinkability violation in {}: two values that should differ are identical",
        context,
    );
}

/// Assert that all nodes in a federation agree on state.
pub fn assert_federation_consistent(
    harness: &mut crate::harness::SimulationHarness,
    fed_idx: usize,
) {
    harness.assert_all_nodes_agree(fed_idx);
}
