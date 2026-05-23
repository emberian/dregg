//! Negation proof integration tests: non-membership and temporal absence.
//!
//! NOTE: temporal_absence_air module has been removed. Tests that depend on
//! the old AIR-based API (build_timeline_tree, TimelineEntry, etc.) are disabled
//! until reimplemented against the DSL temporal_absence API.

use pyana_circuit::field::BabyBear;
use pyana_circuit::non_membership::{
    NonMembershipProver, SetIdentifier, verify_non_membership_proof,
};
use pyana_circuit::poseidon2::hash_many;

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Derive a hash for a user ID.
fn user_hash(user_id: u32) -> BabyBear {
    hash_many(&[BabyBear::new(user_id), BabyBear::new(0xFACE)])
}

// ─── Non-membership tests ────────────────────────────────────────────────────

/// Happy path: prove user NOT in suspended set, then add user, prove again fails.
#[test]
fn test_non_membership_prove_then_add_user_fails() {
    let suspended_set: Vec<BabyBear> = (1..=5).map(|i| user_hash(i * 100)).collect();
    let set_id = SetIdentifier::new("suspended_users");

    // User 42 is NOT in the suspended set.
    let user_42 = user_hash(42);
    assert!(!suspended_set.contains(&user_42));

    // Phase 1: prove non-membership successfully.
    let prover = NonMembershipProver::with_set_id(&suspended_set, set_id.clone());
    let proof = prover
        .prove_non_membership(&[user_42])
        .expect("User 42 is NOT suspended, proof should succeed");
    assert!(
        prover.verify_non_membership(&proof).is_ok(),
        "Non-membership proof should verify"
    );

    // Phase 2: add user 42 to the suspended set.
    let mut updated_set = suspended_set.clone();
    updated_set.push(user_42);

    // Phase 3: attempt to prove non-membership again — MUST fail.
    let prover_updated = NonMembershipProver::with_set_id(&updated_set, set_id);
    let result = prover_updated.prove_non_membership(&[user_42]);
    assert!(
        result.is_none(),
        "Should NOT be able to prove non-membership for a user that was added to the set"
    );
}

/// Adversarial: tamper with the proof accumulator → verification fails.
#[test]
fn test_non_membership_tampered_proof_rejected() {
    let suspended_set: Vec<BabyBear> = (1..=10).map(|i| user_hash(i * 50)).collect();
    let prover =
        NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("tamper_test"));

    let user = user_hash(9999);
    let mut proof = prover
        .prove_non_membership(&[user])
        .expect("Should produce proof for non-member");

    // Tamper with the accumulator value.
    proof.accumulator.0[0] = BabyBear::new(0xDEAD);
    proof.accumulator.0[1] = BabyBear::new(0xBEEF);

    // Verification with tampered proof should fail.
    let result = verify_non_membership_proof(&proof);
    assert!(
        result.is_err(),
        "Tampered accumulator should cause verification failure"
    );
}

/// Adversarial: cross-set replay — proof from set A does not verify against set B.
#[test]
fn test_non_membership_cross_set_replay_rejected() {
    let set_a: Vec<BabyBear> = (1..=5).map(|i| user_hash(i * 10)).collect();
    let set_b: Vec<BabyBear> = (100..=105).map(|i| user_hash(i * 10)).collect();

    let prover_a = NonMembershipProver::with_set_id(&set_a, SetIdentifier::new("set_alpha"));
    let prover_b = NonMembershipProver::with_set_id(&set_b, SetIdentifier::new("set_beta"));

    let user = user_hash(9999);

    // Generate proof from set A.
    let proof_from_a = prover_a
        .prove_non_membership(&[user])
        .expect("Should prove non-membership in set A");

    // This proof is valid for set A's prover.
    assert!(prover_a.verify_non_membership(&proof_from_a).is_ok());

    // But it should NOT verify against set B (different accumulator/alpha).
    let result = prover_b.verify_non_membership(&proof_from_a);
    assert!(
        result.is_err(),
        "Cross-set replay should be rejected: proof from set A must not verify under set B"
    );
}

/// Multiple users: prove several users are NOT in the set at once.
#[test]
fn test_non_membership_batch_prove() {
    let blacklist: Vec<BabyBear> = (1..=20).map(|i| user_hash(i)).collect();
    let prover = NonMembershipProver::with_set_id(&blacklist, SetIdentifier::new("blacklist"));

    // Multiple users not in the blacklist.
    let users: Vec<BabyBear> = (100..=104).map(|i| user_hash(i)).collect();
    for u in &users {
        assert!(!blacklist.contains(u));
    }

    let proof = prover
        .prove_non_membership(&users)
        .expect("Should prove batch non-membership");
    assert!(prover.verify_non_membership(&proof).is_ok());
}

/// Edge case: empty set — any user trivially has non-membership.
#[test]
fn test_non_membership_empty_set() {
    let empty_set: Vec<BabyBear> = vec![];
    let prover = NonMembershipProver::with_set_id(&empty_set, SetIdentifier::new("empty"));

    let user = user_hash(42);
    let proof = prover
        .prove_non_membership(&[user])
        .expect("Non-membership in empty set should always succeed");
    assert!(prover.verify_non_membership(&proof).is_ok());
}

// ─── Temporal absence tests (disabled: temporal_absence_air removed) ─────────

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_valid_gap_proof() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_non_adjacent_fails() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_wrong_params_rejected() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_entry_before_after_t1_fails() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_exact_boundaries() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_dsl_valid_gap() {}

#[test]
#[ignore = "temporal_absence_air module was removed; needs DSL rewrite"]
fn test_temporal_absence_dsl_wrong_params_rejected() {}
