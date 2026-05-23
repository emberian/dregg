//! Predicate soundness integration test: forge attempts MUST fail.
//!
//! This is the adversarial test suite. It verifies that:
//! 1. Honest provers succeed when their claims are true.
//! 2. Dishonest provers cannot produce proofs for false claims.
//! 3. Forged proofs (valid proof structure but wrong public inputs) are rejected.
//! 4. Proof manipulation (bit flips, truncation) causes verification failure.

use pyana_circuit::BabyBear;
use pyana_circuit::poseidon2::hash_fact;
use pyana_circuit::predicate_air::{
    PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment, prove_in_range,
    prove_predicate, verify_in_range, verify_predicate,
};
use pyana_teasting::assertions::{assert_predicate_rejects, assert_predicate_verifies};

/// Helper: create a fact commitment for a given value.
fn test_fact_commitment(value: u32) -> BabyBear {
    let fact_hash = hash_fact(
        BabyBear::new(100),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    let state_root = BabyBear::new(99999);
    compute_fact_commitment(fact_hash, state_root)
}

// =============================================================================
// Honest prover: true statements prove and verify
// =============================================================================

#[test]
fn test_honest_gte_proves_and_verifies() {
    let value = 25u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("25 >= 18 should prove");
    assert_predicate_verifies(&proof, BabyBear::new(threshold), fc);
}

#[test]
fn test_honest_lte_proves_and_verifies() {
    let value = 10u32;
    let threshold = 50u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Lte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("10 <= 50 should prove");
    assert_predicate_verifies(&proof, BabyBear::new(threshold), fc);
}

#[test]
fn test_honest_neq_proves_and_verifies() {
    let value = 42u32;
    let threshold = 99u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Neq,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("42 != 99 should prove");
    assert_predicate_verifies(&proof, BabyBear::new(threshold), fc);
}

#[test]
fn test_honest_in_range_proves_and_verifies() {
    let value = 50u32;
    let low = 10u32;
    let high = 100u32;
    let fc = test_fact_commitment(value);

    let (low_proof, high_proof) = prove_in_range(
        BabyBear::new(value),
        BabyBear::new(low),
        BabyBear::new(high),
        fc,
    )
    .expect("50 in [10, 100] should prove");

    assert!(verify_in_range(
        &low_proof,
        &high_proof,
        BabyBear::new(low),
        BabyBear::new(high),
        fc,
    ));
}

// =============================================================================
// Dishonest prover: false statements MUST NOT produce valid proofs
// =============================================================================

#[test]
fn test_dishonest_gte_cannot_prove() {
    // Trying to prove 15 >= 18 — this is FALSE.
    let value = 15u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let result = prove_predicate(witness);
    assert!(
        result.is_none(),
        "Proof generation for a false GTE claim MUST return None (15 >= 18 is not satisfiable)"
    );
}

#[test]
fn test_dishonest_lte_cannot_prove() {
    // Trying to prove 100 <= 50 — FALSE.
    let value = 100u32;
    let threshold = 50u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Lte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    assert!(prove_predicate(witness).is_none());
}

#[test]
fn test_dishonest_gt_boundary() {
    // Trying to prove 18 > 18 — FALSE (it's equal, not greater).
    let value = 18u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gt,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    assert!(prove_predicate(witness).is_none());
}

#[test]
fn test_dishonest_neq_equal_values() {
    // Trying to prove 42 != 42 — FALSE.
    let value = 42u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(value),
        predicate_type: PredicateType::Neq,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    assert!(prove_predicate(witness).is_none());
}

#[test]
fn test_dishonest_in_range_below() {
    // value=5, range=[10, 100] — 5 < 10, should fail.
    let value = 5u32;
    let low = 10u32;
    let high = 100u32;
    let fc = test_fact_commitment(value);

    let result = prove_in_range(
        BabyBear::new(value),
        BabyBear::new(low),
        BabyBear::new(high),
        fc,
    );
    assert!(result.is_err(), "5 not in [10, 100] — proof must fail");
}

#[test]
fn test_dishonest_in_range_above() {
    // value=200, range=[10, 100] — 200 > 100, should fail.
    let value = 200u32;
    let low = 10u32;
    let high = 100u32;
    let fc = test_fact_commitment(value);

    let result = prove_in_range(
        BabyBear::new(value),
        BabyBear::new(low),
        BabyBear::new(high),
        fc,
    );
    assert!(result.is_err(), "200 not in [10, 100] — proof must fail");
}

// =============================================================================
// Forged proofs: valid structure but wrong public inputs
// =============================================================================

#[test]
fn test_forged_proof_wrong_threshold() {
    // Generate a valid proof for value=25, threshold=18.
    let value = 25u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let proof = prove_predicate(witness).unwrap();

    // Verify with the CORRECT threshold: passes.
    assert!(verify_predicate(&proof, BabyBear::new(18), fc).is_ok());

    // Try to verify with a DIFFERENT threshold (forging the claim to "25 >= 30"):
    // This MUST fail — the proof commits to threshold=18 in public inputs.
    assert_predicate_rejects(&proof, BabyBear::new(30), fc);
}

#[test]
fn test_forged_proof_wrong_fact_commitment() {
    // Generate a valid proof.
    let value = 25u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let proof = prove_predicate(witness).unwrap();

    // Verify with correct fact commitment: passes.
    assert!(verify_predicate(&proof, BabyBear::new(threshold), fc).is_ok());

    // Verify with a DIFFERENT fact commitment (trying to claim this proof
    // applies to a different token state): MUST fail.
    let wrong_fc = compute_fact_commitment(
        hash_fact(
            BabyBear::new(999),
            &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
        ),
        BabyBear::new(99999),
    );
    assert_predicate_rejects(&proof, BabyBear::new(threshold), wrong_fc);
}

#[test]
fn test_forged_proof_replay_with_different_predicate_type() {
    // Generate a valid GTE proof (25 >= 18).
    let value = 25u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let gte_proof = prove_predicate(witness).unwrap();

    // The proof was generated for GTE. Manually change the predicate_type to LTE
    // in an attempt to claim "25 <= 18" using the same proof data.
    let mut forged = gte_proof.clone();
    forged.op = PredicateType::Lte;

    // The constraint proof's trace was generated for GTE (diff = value - threshold).
    // For LTE, the verifier expects diff = threshold - value.
    // Since the trace is committed, the constraints won't match.
    // However, the verify_predicate function checks predicate_type from the proof struct —
    // the actual soundness comes from the constraint proof's public inputs matching.
    // In this case, threshold and fc still match, so we need to check whether
    // the constraint_proof rejects the mismatch.
    //
    // NOTE: If this test passes (forged proof is rejected), the system is sound.
    // If it fails (forged proof is accepted), that's a bug we need to fix.
    let result = verify_predicate(&forged, BabyBear::new(threshold), fc);

    // The trace digest in the ConstraintProof encodes the actual computation.
    // If the verifier doesn't re-derive which constraints to check from predicate_type,
    // this might pass. Document the current behavior:
    if result.is_ok() {
        // This would indicate the predicate_type is not bound into the proof —
        // a soundness gap that should be fixed.
        panic!(
            "SOUNDNESS BUG: Forged proof with swapped predicate_type was accepted. \
             The predicate type must be bound into the constraint proof's public inputs."
        );
    }
    // If we reach here, the forged proof was correctly rejected.
}

// =============================================================================
// Manipulation attacks: bit flips, truncation
// =============================================================================

#[test]
fn test_manipulated_proof_bit_flip() {
    let value = 50u32;
    let threshold = 25u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let proof = prove_predicate(witness).unwrap();

    // Serialize, flip a byte, deserialize, verify.
    let mut bytes = postcard::to_allocvec(&proof).unwrap();
    if bytes.len() > 10 {
        bytes[10] ^= 0xFF; // flip all bits of one byte
    }

    // Deserialization might fail (which is fine — corrupted data).
    // If it succeeds, verification must fail.
    if let Ok(corrupted) = postcard::from_bytes::<PredicateProof>(&bytes) {
        let result = verify_predicate(&corrupted, BabyBear::new(threshold), fc);
        assert!(result.is_err(), "Bit-flipped proof MUST NOT verify");
    }
    // If deserialization fails, that's also correct behavior (caught corruption).
}

#[test]
fn test_manipulated_proof_truncation() {
    let value = 50u32;
    let threshold = 25u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let proof = prove_predicate(witness).unwrap();

    let bytes = postcard::to_allocvec(&proof).unwrap();

    // Truncate to half length.
    let truncated = &bytes[..bytes.len() / 2];

    // Deserialization of truncated data must fail.
    let result = postcard::from_bytes::<PredicateProof>(truncated);
    assert!(
        result.is_err(),
        "Truncated proof bytes must fail deserialization"
    );
}

// =============================================================================
// Boundary conditions
// =============================================================================

#[test]
fn test_boundary_gte_equal_values() {
    // 18 >= 18 is TRUE — should prove and verify.
    let value = 18u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("18 >= 18 should prove");
    assert_predicate_verifies(&proof, BabyBear::new(threshold), fc);
}

#[test]
fn test_boundary_gt_off_by_one() {
    // 19 > 18 is TRUE.
    let value = 19u32;
    let threshold = 18u32;
    let fc = test_fact_commitment(value);

    let witness = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gt,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("19 > 18 should prove");
    assert_predicate_verifies(&proof, BabyBear::new(threshold), fc);
}

#[test]
fn test_boundary_zero_values() {
    // 0 >= 0 is TRUE.
    let fc = test_fact_commitment(0);

    let witness = PredicateWitness {
        private_value: BabyBear::ZERO,
        threshold: BabyBear::ZERO,
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).expect("0 >= 0 should prove");
    assert_predicate_verifies(&proof, BabyBear::ZERO, fc);
}
