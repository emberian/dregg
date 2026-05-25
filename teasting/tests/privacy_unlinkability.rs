//! Privacy unlinkability integration test: multiple presentations of the same token
//! must not be correlatable by a colluding set of verifiers.
//!
//! The privacy model requires:
//! 1. presentation_tag differs per presentation (fresh randomness each time).
//! 2. fact_commitments differ when blinding is used.
//! 3. The issuer membership proof uses blinded ring mode (different blinded_leaf each time).
//! 4. No fixed identifier leaks through public inputs.

use pyana_circuit::BabyBear;
use pyana_circuit::poseidon2::hash_fact;
use pyana_circuit::predicate_air::{
    PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
};
use pyana_sdk::{AgentCipherclerk, AuthRequest};
use pyana_teasting::agent::{SimAgent, shared_root_key};
use pyana_teasting::assertions::assert_unlinkable;

/// Same token, same request, two presentations: presentation tags must differ.
#[test]
fn test_presentation_tags_differ_across_presentations() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("privacy-svc");
    let root_token = alice.mint_token_with_key(&root_key, "privacy");

    let request = AuthRequest {
        service: Some("privacy".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof1 = alice.prove_authorization(&root_token, &request).unwrap();
    let proof2 = alice.prove_authorization(&root_token, &request).unwrap();

    // Both proofs should be valid.
    assert!(proof1.is_valid());
    assert!(proof2.is_valid());

    // The presentation tags (public output) MUST differ between presentations.
    // This is what prevents verifiers from correlating "same token presented twice."
    let tag1 = proof1.circuit_proof.public_inputs.presentation_tag;
    let tag2 = proof2.circuit_proof.public_inputs.presentation_tag;
    assert_ne!(
        tag1, tag2,
        "Presentation tags must differ between independent presentations of the same token"
    );
}

/// Blinded predicate proofs: same fact, same predicate, different blinding → different commitments.
#[test]
fn test_blinded_predicate_proofs_unlinkable() {
    let value = 100u32;
    let threshold = 50u32;

    // Compute the raw fact_hash and state_root.
    let fh = hash_fact(
        BabyBear::new(42),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    let sr = BabyBear::new(99999);

    // Without blinding: deterministic commitment.
    let fc_unblinded = compute_fact_commitment(fh, sr);

    // With blinding factor 1:
    let blinding1 = BabyBear::new(12345);
    let fc_blinded1 = pyana_circuit::poseidon2::hash_4_to_1(&[fh, sr, blinding1, BabyBear::ZERO]);

    // With blinding factor 2:
    let blinding2 = BabyBear::new(67890);
    let fc_blinded2 = pyana_circuit::poseidon2::hash_4_to_1(&[fh, sr, blinding2, BabyBear::ZERO]);

    // Blinded commitments must differ from each other and from unblinded.
    assert_ne!(
        fc_blinded1, fc_blinded2,
        "Different blinding → different commitments"
    );
    assert_ne!(
        fc_blinded1, fc_unblinded,
        "Blinded must differ from unblinded"
    );
    assert_ne!(
        fc_blinded2, fc_unblinded,
        "Blinded must differ from unblinded"
    );

    // Both blinded proofs should still verify (the verifier uses the blinded commitment
    // as the expected public input, received out-of-band from the prover).
    let witness1 = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc_blinded1,
        blinding: Some(blinding1),
        fact_hash: Some(fh),
        state_root: Some(sr),
    };
    let witness2 = PredicateWitness {
        private_value: BabyBear::new(value),
        threshold: BabyBear::new(threshold),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc_blinded2,
        blinding: Some(blinding2),
        fact_hash: Some(fh),
        state_root: Some(sr),
    };

    let proof1 = prove_predicate(witness1).expect("blinded proof 1 should succeed");
    let proof2 = prove_predicate(witness2).expect("blinded proof 2 should succeed");

    // Both verify against their respective (different) fact_commitments.
    use pyana_circuit::predicate_air::verify_predicate;
    assert!(verify_predicate(&proof1, BabyBear::new(threshold), fc_blinded1).is_ok());
    assert!(verify_predicate(&proof2, BabyBear::new(threshold), fc_blinded2).is_ok());
}

/// Multiple delegations from the same token: delegated presentations must not
/// reveal that they share a common ancestor token.
#[test]
#[ignore = "TODO: implement delegation-chain unlinkability verification"]
fn test_delegation_presentations_unlinkable() {
    // TODO: Steps to implement:
    // 1. Alice mints root token.
    // 2. Alice delegates to Bob (with restrictions A).
    // 3. Alice delegates to Carol (with restrictions B).
    // 4. Bob presents to Verifier1, Carol presents to Verifier2.
    // 5. Verify that Verifier1 and Verifier2 cannot determine that Bob and Carol
    //    hold tokens derived from the same root (no common presentation_tag,
    //    no common issuer_key_hash in public inputs due to ring blinding).
}

/// Timing side-channel: proof generation time should not depend on the private value.
#[test]
#[ignore = "TODO: implement timing side-channel resistance test (statistical)"]
fn test_proof_generation_constant_time() {
    // TODO: Steps to implement:
    // 1. Generate 100 proofs with value=1 (near-zero diff).
    // 2. Generate 100 proofs with value=536870000 (near-max diff for 30-bit range).
    // 3. Compare mean generation times — they should be within 2x of each other
    //    (proving that the bit decomposition doesn't short-circuit on leading zeros).
    //
    // Note: This is a statistical test and may be flaky in CI. Consider marking
    // it with a longer timeout and running only in nightly.
}
