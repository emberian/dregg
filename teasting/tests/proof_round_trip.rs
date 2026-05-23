//! Proof round-trip integration test: prove → serialize → transmit → deserialize → verify.
//!
//! Tests that proofs survive serialization boundaries — this catches wire protocol
//! binding mismatches and format disagreements between prover and verifier.

use pyana_circuit::BabyBear;
use pyana_circuit::poseidon2::hash_fact;
use pyana_circuit::predicate_air::{
    PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
    verify_predicate,
};
use pyana_circuit::stark::{proof_from_bytes, proof_to_bytes};
use pyana_sdk::AuthRequest;
use pyana_teasting::agent::{SimAgent, shared_root_key};

/// Predicate proof: generate → serialize (postcard) → deserialize → verify.
#[test]
fn test_predicate_proof_serialization_round_trip() {
    // Build a predicate witness: value=25, threshold=18, GTE.
    let fact_hash = hash_fact(
        BabyBear::new(42),
        &[BabyBear::new(25), BabyBear::ZERO, BabyBear::ZERO],
    );
    let state_root = BabyBear::new(99999);
    let fact_commitment = compute_fact_commitment(fact_hash, state_root);

    let witness = PredicateWitness {
        private_value: BabyBear::new(25),
        threshold: BabyBear::new(18),
        predicate_type: PredicateType::Gte,
        fact_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    // Generate the proof.
    let proof = prove_predicate(witness).expect("honest predicate should prove");

    // Serialize to bytes (simulates wire transmission).
    let bytes = postcard::to_allocvec(&proof).expect("proof serializes");

    // Deserialize (simulates receiver parsing).
    let recovered: PredicateProof = postcard::from_bytes(&bytes).expect("proof deserializes");

    // Verify the recovered proof.
    assert!(
        verify_predicate(&recovered, BabyBear::new(18), fact_commitment),
        "Deserialized predicate proof should verify"
    );
}

/// Predicate proof: different predicate types all round-trip correctly.
#[test]
fn test_all_predicate_types_round_trip() {
    let fact_hash = hash_fact(
        BabyBear::new(1),
        &[BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO],
    );
    let state_root = BabyBear::new(77777);
    let fc = compute_fact_commitment(fact_hash, state_root);

    let cases: Vec<(PredicateType, u32, u32)> = vec![
        (PredicateType::Gte, 50, 30), // 50 >= 30
        (PredicateType::Lte, 50, 80), // 50 <= 80
        (PredicateType::Gt, 50, 30),  // 50 > 30
        (PredicateType::Lt, 50, 80),  // 50 < 80
        (PredicateType::Neq, 50, 30), // 50 != 30
    ];

    for (pred_type, value, threshold) in cases {
        let witness = PredicateWitness {
            private_value: BabyBear::new(value),
            threshold: BabyBear::new(threshold),
            predicate_type: pred_type,
            fact_commitment: fc,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };

        let proof = prove_predicate(witness).unwrap_or_else(|| {
            panic!(
                "{:?}({}, {}) should be provable",
                pred_type, value, threshold
            )
        });

        let bytes = postcard::to_allocvec(&proof).unwrap();
        let recovered: PredicateProof = postcard::from_bytes(&bytes).unwrap();

        assert!(
            verify_predicate(&recovered, BabyBear::new(threshold), fc),
            "{:?} proof failed verification after round-trip",
            pred_type,
        );
    }
}

/// STARK proof bytes: prove → to_bytes → from_bytes → verify.
///
/// Builds a Poseidon2-compatible Merkle witness (real hashing), generates a STARK proof,
/// serializes/deserializes it, then verifies the deserialized proof.
#[test]
fn test_stark_proof_bytes_round_trip() {
    use pyana_circuit::merkle_air::{MerkleLevelWitness, MerkleWitness};
    use pyana_circuit::poseidon2;
    use pyana_circuit::presentation::generate_merkle_poseidon2_stark_proof;
    use pyana_circuit::stark::verify;
    use pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit;

    // Build a Poseidon2-compatible Merkle witness (depth 4).
    let leaf_hash = BabyBear::new(12345);
    let depth = 4;
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 7 + 100) as u32),
            BabyBear::new((i * 7 + 200) as u32),
            BabyBear::new((i * 7 + 300) as u32),
        ];

        // Place current node at its position, siblings elsewhere (Poseidon2 hashing).
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        let parent = poseidon2::hash_4_to_1(&children);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    let witness = MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    };

    // Generate a STARK proof.
    let proof = generate_merkle_poseidon2_stark_proof(&witness)
        .expect("STARK proof generation should succeed with Poseidon2-compatible witness");

    // Serialize to bytes.
    let bytes = proof_to_bytes(&proof);
    assert!(!bytes.is_empty(), "Serialized proof should be non-empty");

    // Deserialize from bytes.
    let recovered = proof_from_bytes(&bytes).expect("STARK proof should deserialize");

    // Verify the recovered proof using the same public inputs.
    let public_inputs = vec![witness.leaf_hash, witness.expected_root];
    let circuit = merkle_poseidon2_circuit();
    let result = verify(&circuit, &recovered, &public_inputs);
    assert!(
        result.is_ok(),
        "Deserialized STARK proof should verify: {:?}",
        result.err()
    );
}

/// Presentation proof: full bridge proof survives postcard serialization.
///
/// NOTE: This test documents a known serialization gap: the WirePresentationProof
/// may fail to round-trip via postcard due to nested StarkProof field layout.
/// If this test fails with DeserializeUnexpectedEnd, that's a real wire protocol bug
/// that needs fixing (the prover and verifier disagree on the binary format).
#[test]
fn test_presentation_proof_round_trip() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("roundtrip-svc");
    let root_token = alice.mint_token_with_key(&root_key, "roundtrip");

    let request = AuthRequest {
        service: Some("roundtrip".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    // Generate a full presentation proof.
    let proof = alice.prove_authorization(&root_token, &request).unwrap();
    assert!(proof.is_valid());

    // Convert to wire format (this is what gets transmitted over the network).
    let wire_proof = proof.into_wire_proof();

    // Serialize the wire proof.
    let bytes = postcard::to_allocvec(&wire_proof).expect("wire proof serializes");

    // Deserialize the wire proof.
    let recovered: pyana_bridge::WirePresentationProof =
        postcard::from_bytes(&bytes).expect("wire proof deserializes");

    // Verify the recovered proof's STARK issuer membership proof.
    let real_stark = recovered
        .real_stark_proof
        .as_ref()
        .expect("recovered proof should have real STARK proof");
    assert_eq!(
        real_stark.verify(),
        pyana_circuit::PresentationVerification::Valid,
        "Recovered STARK proof should verify after round-trip"
    );
}

/// Test that proof size is bounded (no accidental blowup from serialization).
#[test]
fn test_proof_size_bounded() {
    let fact_hash = hash_fact(
        BabyBear::new(1),
        &[BabyBear::new(100), BabyBear::ZERO, BabyBear::ZERO],
    );
    let state_root = BabyBear::new(55555);
    let fc = compute_fact_commitment(fact_hash, state_root);

    let witness = PredicateWitness {
        private_value: BabyBear::new(100),
        threshold: BabyBear::new(50),
        predicate_type: PredicateType::Gte,
        fact_commitment: fc,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let proof = prove_predicate(witness).unwrap();
    let bytes = postcard::to_allocvec(&proof).unwrap();

    // The constraint prover stores the full trace (35 columns * ~1024 rows * 4 bytes each),
    // so a single predicate proof is ~50KB in the mock/constraint prover mode.
    // In production (real STARK), this would be ~24KB. Either way, verify it's bounded
    // to prevent accidental blowup from serialization (e.g., < 100KB).
    assert!(
        bytes.len() < 100_000,
        "Predicate proof is {} bytes, expected < 100KB",
        bytes.len()
    );
}
