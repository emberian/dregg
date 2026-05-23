//! Integration test for the SovereignTransitionAir (Phase 2).
//!
//! Tests the STARK proof generation and verification for sovereign cell
//! state transitions (balance transfers).

use pyana_circuit::field::BabyBear;
use pyana_circuit::sovereign_transition_air::{
    SovereignTransitionAir, SOVEREIGN_PUBLIC_INPUTS, bytes32_to_babybear,
    generate_sovereign_transition_trace,
};
use pyana_circuit::stark::{StarkAir, proof_from_bytes, proof_to_bytes, prove, verify};

#[test]
fn sovereign_transition_outgoing_prove_verify() {
    let old_balance = 1000u64;
    let transfer_amount = 100u64;
    let direction = 1u32; // outgoing

    let old_commitment = [1u8; 32];
    let new_commitment = [2u8; 32];
    let effects_hash = [3u8; 32];
    let cell_id_hash = [4u8; 32];

    let (trace, public_inputs) = generate_sovereign_transition_trace(
        old_balance,
        transfer_amount,
        direction,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        &cell_id_hash,
    );

    assert_eq!(public_inputs.len(), SOVEREIGN_PUBLIC_INPUTS);
    assert_eq!(trace.len(), 2); // power-of-two minimum
    assert_eq!(trace[0].len(), SovereignTransitionAir.width());

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn sovereign_transition_incoming_prove_verify() {
    let old_balance = 500u64;
    let transfer_amount = 200u64;
    let direction = 0u32; // incoming

    let old_commitment = [10u8; 32];
    let new_commitment = [11u8; 32];
    let effects_hash = [12u8; 32];
    let cell_id_hash = [13u8; 32];

    let (trace, public_inputs) = generate_sovereign_transition_trace(
        old_balance,
        transfer_amount,
        direction,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        &cell_id_hash,
    );

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_ok(), "Verification failed: {:?}", result.err());
}

#[test]
fn sovereign_transition_invalid_trace_rejected() {
    let old_commitment = [5u8; 32];
    let new_commitment = [6u8; 32];
    let effects_hash = [7u8; 32];
    let cell_id_hash = [8u8; 32];

    let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
    public_inputs.extend(bytes32_to_babybear(&old_commitment));
    public_inputs.extend(bytes32_to_babybear(&new_commitment));
    public_inputs.extend(bytes32_to_babybear(&effects_hash));
    public_inputs.extend(bytes32_to_babybear(&cell_id_hash));

    // Invalid trace: old=1000, amount=100, direction=1 (outgoing)
    // but new_balance=1000 (should be 900).
    let trace = vec![
        vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(1000), // WRONG: should be 900
            BabyBear::ONE,            // direction = outgoing
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
        vec![
            BabyBear::from_u64(1000),
            BabyBear::from_u64(100),
            BabyBear::from_u64(1000), // WRONG
            BabyBear::ONE,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    ];

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);
    let result = verify(&air, &proof, &public_inputs);
    assert!(result.is_err(), "Invalid trace should not verify");
}

#[test]
fn sovereign_transition_proof_serialization_roundtrip() {
    let old_balance = 5000u64;
    let transfer_amount = 42u64;
    let direction = 1u32;

    let old_commitment = [20u8; 32];
    let new_commitment = [21u8; 32];
    let effects_hash = [22u8; 32];
    let cell_id_hash = [23u8; 32];

    let (trace, public_inputs) = generate_sovereign_transition_trace(
        old_balance,
        transfer_amount,
        direction,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        &cell_id_hash,
    );

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);

    // Serialize and deserialize.
    let bytes = proof_to_bytes(&proof);
    let recovered = proof_from_bytes(&bytes).expect("deserialization should succeed");

    // Verify the deserialized proof.
    let result = verify(&air, &recovered, &public_inputs);
    assert!(
        result.is_ok(),
        "Roundtripped proof failed: {:?}",
        result.err()
    );
}

#[test]
fn sovereign_transition_wrong_public_inputs_rejected() {
    let old_balance = 1000u64;
    let transfer_amount = 100u64;
    let direction = 1u32;

    let old_commitment = [30u8; 32];
    let new_commitment = [31u8; 32];
    let effects_hash = [32u8; 32];
    let cell_id_hash = [33u8; 32];

    let (trace, public_inputs) = generate_sovereign_transition_trace(
        old_balance,
        transfer_amount,
        direction,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        &cell_id_hash,
    );

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);

    // Try verifying with DIFFERENT public inputs (tampered commitment).
    let tampered_commitment = [99u8; 32];
    let mut tampered_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
    tampered_inputs.extend(bytes32_to_babybear(&tampered_commitment)); // wrong old
    tampered_inputs.extend(bytes32_to_babybear(&new_commitment));
    tampered_inputs.extend(bytes32_to_babybear(&effects_hash));
    tampered_inputs.extend(bytes32_to_babybear(&cell_id_hash));

    let result = verify(&air, &proof, &tampered_inputs);
    assert!(
        result.is_err(),
        "Proof should not verify with wrong public inputs"
    );
}
