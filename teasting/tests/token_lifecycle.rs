//! Token lifecycle integration test: mint → attenuate → delegate → present → verify.
//!
//! DESIGN NOTE: In pyana's macaroon model, HMAC verification requires the root key.
//! The `attenuate()` method deliberately zeroes the root key on derived tokens
//! (security: prevents forging). This means:
//!
//! - `verify_token()` only works on ROOT tokens (minted with the key).
//! - Attenuated tokens must be verified via STARK proofs (`prove_authorization()`).
//! - The root holder generates proofs using `prove_with_chain()`.
//!
//! These tests exercise: minting, STARK proof generation for root tokens,
//! chain proofs for attenuation sequences, and delegation flows.

use pyana_sdk::{Attenuation, AuthRequest};
use pyana_teasting::agent::{SimAgent, shared_root_key};

/// Root token: mint and verify locally (root holder has the key).
#[test]
fn test_mint_and_verify_root_token() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("storage-service");
    let root_token = alice.mint_token_with_key(&root_key, "storage");

    // Root token verifies for any action on its service.
    let read_request = AuthRequest {
        service: Some("storage".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    assert!(
        alice.verify_token(&root_token, &read_request),
        "Root token should authorize any request on its service"
    );

    let write_request = AuthRequest {
        service: Some("storage".into()),
        action: Some("w".into()),
        ..Default::default()
    };
    assert!(
        alice.verify_token(&root_token, &write_request),
        "Root token is unrestricted"
    );
}

/// Prove authorization: root holder generates a STARK proof for the root token.
#[test]
fn test_prove_authorization_stark() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("compute-service");
    let root_token = alice.mint_token_with_key(&root_key, "compute");

    let request = AuthRequest {
        service: Some("compute".into()),
        action: Some("exec".into()),
        ..Default::default()
    };

    let proof = alice.prove_authorization(&root_token, &request).unwrap();
    assert!(proof.is_valid(), "STARK proof should be valid");
    assert!(
        proof.is_constraint_checked(),
        "Constraints should be satisfied"
    );
}

/// Chain proof: root token + explicit attenuation steps → STARK proof.
///
/// This is the primary mechanism for verifying attenuated tokens: the root holder
/// generates a proof that covers the entire attenuation chain.
#[test]
fn test_prove_with_single_attenuation() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("dns-service");
    let root_token = alice.mint_token_with_key(&root_key, "dns");

    let att = Attenuation {
        services: vec![("dns".into(), "r".into())],
        ..Default::default()
    };

    let request = AuthRequest {
        service: Some("dns".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof = alice
        .prove_with_chain(&root_token, &[att], &request)
        .unwrap();

    assert!(proof.is_valid());
    assert!(
        proof.chain_length >= 1,
        "Should have at least 1 fold step for the attenuation"
    );
}

/// Chain proof with multiple attenuations: each adds a fold step.
#[test]
fn test_prove_with_multiple_attenuations() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("api-service");
    let root_token = alice.mint_token_with_key(&root_key, "api");

    let att1 = Attenuation {
        services: vec![("api".into(), "r".into())],
        ..Default::default()
    };
    let att2 = Attenuation {
        features: vec!["users".into()],
        ..Default::default()
    };

    let request = AuthRequest {
        service: Some("api".into()),
        action: Some("r".into()),
        features: vec!["users".into()],
        ..Default::default()
    };

    let proof = alice
        .prove_with_chain(&root_token, &[att1, att2], &request)
        .unwrap();

    assert!(proof.is_valid());
    assert!(
        proof.chain_length >= 2,
        "Should have at least 2 fold steps for 2 attenuations"
    );
}

/// Delegation flow: Alice mints, delegates to Bob, Bob receives the token.
/// Verification is done by Alice (root holder) via chain proofs.
#[test]
fn test_delegation_and_chain_proof() {
    let mut alice = SimAgent::new("Alice");
    let mut bob = SimAgent::new("Bob");

    let root_key = shared_root_key("storage-service");
    let root_token = alice.mint_token_with_key(&root_key, "storage");

    // Alice delegates to Bob with read-only restriction.
    let restrictions = Attenuation {
        services: vec![("storage".into(), "r".into())],
        ..Default::default()
    };
    let delegated = alice.delegate(&root_token, &bob, &restrictions).unwrap();

    // Bob receives the delegation.
    bob.receive_delegation(delegated).unwrap();

    // Bob now has a token in his wallet (but can't locally verify — no root key).
    let bob_token = bob.wallet.find_token("attenuated:storage");
    assert!(bob_token.is_some(), "Bob should have the delegated token");

    // Alice can prove the chain is valid (she holds the root key).
    let request = AuthRequest {
        service: Some("storage".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof = alice
        .prove_with_chain(&root_token, &[restrictions.clone()], &request)
        .unwrap();
    assert!(proof.is_valid());
}

/// Multiple delegations: Alice → Bob → Carol requires chain proofs from root.
#[test]
fn test_multi_level_delegation() {
    let mut alice = SimAgent::new("Alice");
    let mut bob = SimAgent::new("Bob");
    let mut carol = SimAgent::new("Carol");

    let root_key = shared_root_key("api-service");
    let root_token = alice.mint_token_with_key(&root_key, "api");

    // Alice → Bob: read+write.
    let bob_att = Attenuation {
        services: vec![("api".into(), "rw".into())],
        ..Default::default()
    };
    let delegated_to_bob = alice.delegate(&root_token, &bob, &bob_att).unwrap();
    bob.receive_delegation(delegated_to_bob).unwrap();

    // Bob → Carol: read only (further restriction).
    let bob_token = bob.wallet.find_token("attenuated:api").unwrap().clone();
    let carol_att = Attenuation {
        services: vec![("api".into(), "r".into())],
        ..Default::default()
    };
    let delegated_to_carol = bob.delegate(&bob_token, &carol, &carol_att).unwrap();
    carol.receive_delegation(delegated_to_carol).unwrap();

    // Carol has a token but can't locally verify.
    assert!(carol.wallet.find_token("attenuated:api").is_some());

    // Alice proves the full chain: root → rw → r for a read request.
    let request = AuthRequest {
        service: Some("api".into()),
        action: Some("r".into()),
        ..Default::default()
    };

    let proof = alice
        .prove_with_chain(&root_token, &[bob_att, carol_att], &request)
        .unwrap();
    assert!(proof.is_valid());
    assert!(
        proof.chain_length >= 2,
        "Two attenuation steps should produce at least 2 fold steps"
    );
}
