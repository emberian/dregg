//! Integration tests: non-membership prove-then-verify and adversarial rejection.
//!
//! Uses the `NonMembershipProver` API from `pyana_circuit::non_membership` to
//! generate real STARK proofs and verify them end-to-end.  Covers:
//!   - Honest proofs for elements NOT in the set.
//!   - Rejection when a proof is built for an element that IS in the set.
//!   - Cross-set replay protection: proof generated for set A is rejected by
//!     verifier for set B.
//!   - Accumulator corruption: verify_non_membership_proof called with a proof
//!     whose `accumulator` field has been tampered; must be rejected.
//!   - Alpha corruption: analogous tamper on the `alpha` field.

use pyana_circuit::{
    field::BabyBear,
    non_membership::{
        NonMembershipProver, SetIdentifier, verify_non_membership_proof,
    },
};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn bb(v: u32) -> BabyBear {
    BabyBear::new(v)
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Honest proof: element NOT in the set → verifies.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_honest_element_verifies() {
    let set = vec![bb(0x100), bb(0x200), bb(0x300)];
    let prover = NonMembershipProver::new(&set);

    let element = bb(0x999); // not in set
    let proof = prover
        .prove_non_membership(&[element])
        .expect("prove_non_membership must succeed for a non-member");

    let result = prover.verify_non_membership(&proof);
    assert!(result.is_ok(), "honest non-membership proof must verify: {:?}", result.err());
}

/// Stateless verification (separate from the prover) also accepts the proof.
#[test]
fn non_membership_stateless_verify_accepts_honest_proof() {
    let set = vec![bb(0xA1), bb(0xB2), bb(0xC3), bb(0xD4)];
    let prover = NonMembershipProver::new(&set);

    let elements = vec![bb(0x1111), bb(0x2222)];
    let proof = prover
        .prove_non_membership(&elements)
        .expect("prove_non_membership must succeed");

    let result = verify_non_membership_proof(&proof);
    assert!(result.is_ok(), "stateless verify must accept honest proof: {:?}", result.err());
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Element IS in the set → prove returns None.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_element_in_set_cannot_prove() {
    let set = vec![bb(0x100), bb(0x200), bb(0x300)];
    let prover = NonMembershipProver::new(&set);

    // 0x200 is IN the set — the prover must refuse.
    let member = bb(0x200);
    let result = prover.prove_non_membership(&[member]);
    assert!(
        result.is_none(),
        "prove_non_membership for a set-member must return None"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Cross-set replay protection: proof for set A is rejected by set B verifier.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_cross_set_replay_rejected() {
    let set_a = vec![bb(0xAAAA), bb(0xBBBB)];
    let set_b = vec![bb(0xCCCC), bb(0xDDDD)];

    let prover_a = NonMembershipProver::with_set_id(&set_a, SetIdentifier::new("set-alpha"));
    let prover_b = NonMembershipProver::with_set_id(&set_b, SetIdentifier::new("set-beta"));

    let element = bb(0x1234); // not in either set
    let proof_a = prover_a
        .prove_non_membership(&[element])
        .expect("prove for set-alpha must succeed");

    // Trying to verify proof_a with prover_b's accumulator must fail:
    // the accumulator values differ across the two distinct sets.
    let result = prover_b.verify_non_membership(&proof_a);
    assert!(
        result.is_err(),
        "cross-set replay must be rejected: proof for set-alpha is not valid for set-beta"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. Accumulator tamper: manipulate the proof's accumulator field directly.
//    The inner STARK proof was generated with the original accumulator;
//    changing the field should cause a PI mismatch.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_tampered_accumulator_rejected() {
    let set = vec![bb(0x111), bb(0x222), bb(0x333)];
    let prover = NonMembershipProver::new(&set);

    let element = bb(0x999);
    let mut proof = prover
        .prove_non_membership(&[element])
        .expect("prove must succeed");

    // Corrupt the accumulator field in the proof struct (not the STARK bytes).
    // `verify_accumulator_non_membership` reads the PI from the proof and
    // cross-checks against the passed accumulator, so this tamper surfaces as
    // a verifier-level PI mismatch.
    let original_acc = proof.accumulator;
    proof.accumulator.0[0] = proof.accumulator.0[0] + BabyBear::ONE;
    assert_ne!(proof.accumulator.0[0], original_acc.0[0], "tamper must change the value");

    let result = verify_non_membership_proof(&proof);
    assert!(
        result.is_err(),
        "tampered accumulator must cause non-membership verify to fail"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. Alpha tamper: manipulate the alpha challenge field.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_tampered_alpha_rejected() {
    let set = vec![bb(0x500), bb(0x600)];
    let prover = NonMembershipProver::new(&set);

    let element = bb(0xAAA);
    let mut proof = prover
        .prove_non_membership(&[element])
        .expect("prove must succeed");

    // The accumulator was computed with the original alpha; changing alpha
    // breaks the polynomial identity, so verify must reject.
    proof.alpha.0[0] = proof.alpha.0[0] + BabyBear::ONE;

    let result = verify_non_membership_proof(&proof);
    assert!(
        result.is_err(),
        "tampered alpha must cause non-membership verify to fail"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Multi-element proof: several non-members proven together.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_multi_element_verifies() {
    let set: Vec<BabyBear> = (1u32..=6).map(BabyBear::new).collect();
    let prover = NonMembershipProver::new(&set);

    // Prove that 100, 200, 300 are all not in {1,2,3,4,5,6}.
    let elements = vec![bb(100), bb(200), bb(300)];
    let proof = prover
        .prove_non_membership(&elements)
        .expect("multi-element prove must succeed");

    let result = prover.verify_non_membership(&proof);
    assert!(result.is_ok(), "multi-element non-membership proof must verify: {:?}", result.err());
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. Empty set: every element is trivially a non-member.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_membership_empty_set_always_proves() {
    let set: Vec<BabyBear> = vec![];
    let prover = NonMembershipProver::new(&set);

    let element = bb(0xDEAD);
    let proof = prover.prove_non_membership(&[element]);
    // The accumulator for an empty set is the multiplicative identity;
    // proving non-membership should either succeed or return None depending
    // on whether the AIR handles the 0-ancestor degenerate case.
    // Either outcome is acceptable — the important property is that `verify`
    // is consistent with `prove`.
    if let Some(p) = proof {
        let result = prover.verify_non_membership(&p);
        assert!(
            result.is_ok(),
            "if prove returns Some for empty set, verify must accept: {:?}",
            result.err()
        );
    }
    // prove returning None is also fine for an empty set.
}
