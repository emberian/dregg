//! Integration test: mint -> attenuate -> prove -> execute_turn -> verify
//!
//! This test exercises the full end-to-end pipeline connecting the token/bridge
//! system (System B) to the turn execution system (System A) via STARK proofs.

use pyana_bridge::StarkProofVerifier;
use pyana_bridge::present::{bytes_to_babybear, hash_index};
use pyana_cell::{AuthRequired, Ledger, Permissions, VerificationKey, cell::Cell};
use pyana_circuit::BabyBear;
use pyana_circuit::stark::{self, MerkleStarkAir, generate_merkle_trace, proof_to_bytes};
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use pyana_turn::{ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("pyana-integration-test:{name}").as_bytes()).as_bytes()
}

fn test_token_id() -> [u8; 32] {
    *blake3::hash(b"pyana-integration-test:domain").as_bytes()
}

/// Generate a STARK proof of federation membership for a given issuer key.
/// Returns (proof_bytes, federation_root_babybear_value).
fn generate_membership_proof(issuer_key: &[u8; 32]) -> (Vec<u8>, BabyBear) {
    let leaf_hash = bytes_to_babybear(issuer_key);
    let siblings: Vec<[u32; 3]> = (0..4u32)
        .map(|i| {
            [
                hash_index(i as usize, 0, issuer_key),
                hash_index(i as usize, 1, issuer_key),
                hash_index(i as usize, 2, issuer_key),
            ]
        })
        .collect();
    let positions: Vec<u32> = vec![0, 1, 2, 3];

    let (trace, public_inputs) = generate_merkle_trace(leaf_hash.0, &siblings, &positions);
    let air = MerkleStarkAir;
    let proof = stark::prove(&air, &trace, &public_inputs);
    let proof_bytes = proof_to_bytes(&proof);

    (proof_bytes, public_inputs[1]) // (proof_bytes, federation_root)
}

/// Full end-to-end integration test: mint -> attenuate -> prove -> execute_turn -> verify.
#[test]
fn test_mint_attenuate_prove_execute_verify() {
    // --- Phase 1: Token minting and attenuation ---
    let issuer_key = test_key("issuer");
    let root_token = MacaroonToken::mint(issuer_key, b"test-kid", "test.pyana.dev");

    let attenuation = Attenuation {
        services: vec![("compute".into(), "rw".into())],
        not_after: Some(2000000000),
        ..Default::default()
    };
    let attenuated = root_token.attenuate(&attenuation).unwrap();

    // Verify the attenuated token works for the intended request
    let request = AuthRequest {
        service: Some("compute".into()),
        action: Some("rw".into()),
        now: Some(1700000000),
        ..Default::default()
    };
    assert!(
        attenuated.verify(&request).is_ok(),
        "attenuated token should verify"
    );

    // --- Phase 2: Generate STARK proof ---
    let (proof_bytes, federation_root) = generate_membership_proof(&issuer_key);
    assert!(!proof_bytes.is_empty(), "proof should be non-empty");

    // Verify the STARK proof independently
    let deserialized = stark::proof_from_bytes(&proof_bytes).unwrap();
    let pi: Vec<BabyBear> = deserialized
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new(v))
        .collect();
    assert!(stark::verify(&MerkleStarkAir, &deserialized, &pi).is_ok());

    // --- Phase 3: Set up ledger with cells ---
    let token_id = test_token_id();
    let mut ledger = Ledger::new();

    // Agent cell
    let agent_key = test_key("agent");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 100_000);
    agent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    // Target cell requiring PROOF authorization
    let target_key = test_key("target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 50_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::Proof,
        receive: AuthRequired::None,
        set_state: AuthRequired::Proof,
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::Proof,
        delegate: AuthRequired::Proof,
        access: AuthRequired::Proof,
    };
    // Set the verification key to the federation root
    let mut vk_bytes = [0u8; 32];
    vk_bytes[..4].copy_from_slice(&federation_root.0.to_le_bytes());
    target_cell.verification_key = Some(VerificationKey::from_parts(
        *blake3::hash(&vk_bytes).as_bytes(),
        vk_bytes.to_vec(),
    ));
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    // Grant agent capability to access target
    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    // --- Phase 4: Execute turn with STARK proof ---
    let verifier = StarkProofVerifier::new();
    let executor =
        TurnExecutor::with_proof_verifier(ComputronCosts::default_costs(), Box::new(verifier));

    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(50000);
    {
        let action = turn_builder.action(target_id, "compute");
        action.delegation(DelegationMode::None);
        action.authorize_proof(proof_bytes.clone(), "", "");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"result:42").as_bytes(),
        });
    }
    let turn = turn_builder.build();

    let result = executor.execute(&turn, &mut ledger);
    match &result {
        TurnResult::Committed {
            receipt,
            computrons_used,
            ..
        } => {
            assert!(*computrons_used > 0);
            assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Turn should have committed but was rejected: {reason}");
        }
        _ => panic!("unexpected turn result"),
    }

    // Verify state was actually modified
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(
        target.state.fields[0],
        *blake3::hash(b"result:42").as_bytes()
    );

    // --- Phase 5: Verify rejection with tampered proof ---
    let mut bad_proof = proof_bytes.clone();
    bad_proof[20] ^= 0xFF;

    let mut bad_turn_builder = TurnBuilder::new(agent_id, 1);
    bad_turn_builder.set_fee(50000);
    {
        let action = bad_turn_builder.action(target_id, "evil");
        action.delegation(DelegationMode::None);
        action.authorize_proof(bad_proof, "", "");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: [0xEE; 32],
        });
    }
    let bad_turn = bad_turn_builder.build();
    let bad_result = executor.execute(&bad_turn, &mut ledger);
    assert!(
        matches!(bad_result, TurnResult::Rejected { .. }),
        "Tampered proof should be rejected"
    );

    // State unchanged
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(
        target.state.fields[1], [0u8; 32],
        "state should be unchanged after rejection"
    );
}

/// Test that the verifier rejects when no verifier is configured (fail-closed).
#[test]
fn test_fail_closed_no_verifier() {
    let issuer_key = test_key("issuer-failclosed");
    let (proof_bytes, federation_root) = generate_membership_proof(&issuer_key);

    let token_id = test_token_id();
    let mut ledger = Ledger::new();

    let agent_key = test_key("agent-failclosed");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 100_000);
    agent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    let target_key = test_key("target-failclosed");
    let mut target_cell = Cell::with_balance(target_key, token_id, 50_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::Proof,
        receive: AuthRequired::None,
        set_state: AuthRequired::Proof,
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::Proof,
        delegate: AuthRequired::Proof,
        access: AuthRequired::Proof,
    };
    let mut vk_bytes = [0u8; 32];
    vk_bytes[..4].copy_from_slice(&federation_root.0.to_le_bytes());
    target_cell.verification_key = Some(VerificationKey::from_parts(
        *blake3::hash(&vk_bytes).as_bytes(),
        vk_bytes.to_vec(),
    ));
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    // NO proof verifier configured - should fail closed
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(50000);
    {
        let action = turn_builder.action(target_id, "compute");
        action.delegation(DelegationMode::None);
        action.authorize_proof(proof_bytes, "", "");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xAA; 32],
        });
    }
    let turn = turn_builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Should reject when no proof verifier is configured (fail-closed)"
    );
}

/// Test that a proof for the WRONG federation root is rejected.
#[test]
fn test_wrong_federation_root_rejected() {
    let issuer_key = test_key("issuer-wrong-root");
    let (proof_bytes, _federation_root) = generate_membership_proof(&issuer_key);

    let token_id = test_token_id();
    let mut ledger = Ledger::new();

    let agent_key = test_key("agent-wrong-root");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 100_000);
    agent_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    let target_key = test_key("target-wrong-root");
    let mut target_cell = Cell::with_balance(target_key, token_id, 50_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::Proof,
        receive: AuthRequired::None,
        set_state: AuthRequired::Proof,
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::Proof,
        delegate: AuthRequired::Proof,
        access: AuthRequired::Proof,
    };
    // Use a DIFFERENT federation root than what the proof was generated for
    let mut wrong_vk_bytes = [0u8; 32];
    wrong_vk_bytes[..4].copy_from_slice(&99999u32.to_le_bytes());
    target_cell.verification_key = Some(VerificationKey::from_parts(
        *blake3::hash(&wrong_vk_bytes).as_bytes(),
        wrong_vk_bytes.to_vec(),
    ));
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    let verifier = StarkProofVerifier::new();
    let executor =
        TurnExecutor::with_proof_verifier(ComputronCosts::default_costs(), Box::new(verifier));

    let mut turn_builder = TurnBuilder::new(agent_id, 0);
    turn_builder.set_fee(50000);
    {
        let action = turn_builder.action(target_id, "compute");
        action.delegation(DelegationMode::None);
        action.authorize_proof(proof_bytes, "", "");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xBB; 32],
        });
    }
    let turn = turn_builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Rejected { .. }),
        "Should reject proof with wrong federation root"
    );
}
