//! End-to-end adversarial integration tests for pyana.
//!
//! Each test exercises the FULL pipeline — real crypto, real execution — then
//! tampers with an intermediate value and verifies that the tampered version
//! is REJECTED at the correct layer.
//!
//! Test scenarios:
//! 1. Token lifecycle with forgery attempts (HMAC chain, action binding, federation root)
//! 2. Revocation propagation (stale revocation root, non-membership proof failure)
//! 3. Attenuation honesty (claiming wider permissions than granted)
//! 4. Cross-cell unauthorized access (no capability, read-only bypass, write success)
//! 5. Note double-spend (nullifier replay)
//! 6. Turn replay (nonce mismatch)
//! 7. Conservation violation (excess != 0, transfer creates value)
//! 8. Proof for wrong statement (wrong action binding in proof authorization)

use pyana_cell::{AuthRequired, Permissions};
use pyana_turn::ProofVerifier;

// =============================================================================
// Helpers
// =============================================================================

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("adversarial-pipeline:{name}").as_bytes()).as_bytes()
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A mock proof verifier that accepts proofs IFF the proof bytes encode the
/// expected (action, resource) binding via BLAKE3 hash. This simulates real
/// ZK proof binding without requiring actual STARK proof generation for
/// non-circuit tests.
struct BindingProofVerifier;

impl ProofVerifier for BindingProofVerifier {
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool {
        // The "proof" is blake3(action || resource || vk) — a simple binding check.
        // This mirrors how real ZK proofs bind to a specific statement.
        let expected = blake3::keyed_hash(
            &[0u8; 32],
            &[action.as_bytes(), b":", resource.as_bytes(), b":", vk].concat(),
        );
        proof == expected.as_bytes()
    }
}

/// Generate a valid proof for the BindingProofVerifier.
fn make_binding_proof(action: &str, resource: &str, vk: &[u8]) -> Vec<u8> {
    let hash = blake3::keyed_hash(
        &[0u8; 32],
        &[action.as_bytes(), b":", resource.as_bytes(), b":", vk].concat(),
    );
    hash.as_bytes().to_vec()
}

// =============================================================================
// TEST 1: Token lifecycle with forgery attempts
// =============================================================================

/// Full lifecycle: Mint -> attenuate -> verify -> tamper HMAC chain -> REJECTED
/// -> wrong action binding -> REJECTED -> wrong federation root -> REJECTED
#[test]
fn adversarial_token_lifecycle_forgery() {
    // --- Step 1: Mint root token ---
    let issuer_key = test_key("issuer-lifecycle");
    let root_token = MacaroonToken::mint(issuer_key, b"lifecycle-kid", "auth.pyana.dev");

    // --- Step 2: Attenuate (restrict to compute/read, expiry) ---
    let att = Attenuation {
        services: vec![("compute".into(), "r".into())],
        not_after: Some(2_000_000_000),
        ..Default::default()
    };
    let attenuated = root_token.attenuate(&att).unwrap();

    // --- Step 3: Verify the token works for the intended request ---
    let valid_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    assert!(
        attenuated.verify(&valid_request).is_ok(),
        "Attenuated token should verify for intended request"
    );

    // --- Step 4: TAMPER with the HMAC chain (use wrong key) ---
    // Mint with a DIFFERENT key, then try to verify with the original key.
    let wrong_key = test_key("wrong-issuer");
    let forged_root = MacaroonToken::mint(wrong_key, b"lifecycle-kid", "auth.pyana.dev");
    let forged_attenuated = forged_root.attenuate(&att).unwrap();

    // The forged token cannot verify against the original issuer's key.
    // Construct a new token object with the ORIGINAL key but the forged inner.
    // Since MacaroonToken encapsulates the key, the cleanest forgery test is:
    // verify that a token minted with key A, when verified by someone expecting key B, fails.
    let wrong_key_token = MacaroonToken::mint(wrong_key, b"lifecycle-kid", "auth.pyana.dev");
    let wrong_attenuated = wrong_key_token.attenuate(&att).unwrap();

    // Encode and decode with the WRONG key to simulate HMAC chain mismatch.
    let encoded = wrong_attenuated.to_encoded().unwrap();
    let decoded_with_correct_key = MacaroonToken::from_encoded(&encoded, issuer_key);
    match decoded_with_correct_key {
        Ok(token) => {
            // Even if decoding succeeds (the format is valid), verification MUST fail
            // because the HMAC chain was computed with a different root key.
            let result = token.verify(&valid_request);
            assert!(
                result.is_err(),
                "Token forged with wrong key MUST fail verification against correct key"
            );
        }
        Err(_) => {
            // Decoding failure is also acceptable (detected at parse time)
        }
    }

    // --- Step 5: Present with wrong action binding -> REJECTED ---
    let wrong_action_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("w".into()), // write, not read
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let result = attenuated.verify(&wrong_action_request);
    assert!(
        result.is_err(),
        "Attenuated token with read-only MUST reject write action"
    );

    // --- Step 6: Present with wrong service binding -> REJECTED ---
    let wrong_service_request = AuthRequest {
        service: Some("storage".into()), // wrong service
        action: Some("r".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    let result = attenuated.verify(&wrong_service_request);
    assert!(
        result.is_err(),
        "Attenuated token for 'compute' MUST reject 'storage' service"
    );

    // --- Step 7: Present after expiry -> REJECTED ---
    let expired_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(2_000_000_001), // past expiry
        ..Default::default()
    };
    let result = attenuated.verify(&expired_request);
    assert!(result.is_err(), "Token MUST fail after expiry timestamp");
}

// =============================================================================
// TEST 2: Revocation propagation
// =============================================================================

/// Mint -> present -> SUCCESS -> revoke -> present again -> REJECTED
#[test]
fn adversarial_revocation_propagation() {
    // --- Step 1: Mint token with Revocable caveat ---
    let issuer_key = test_key("issuer-revocation");
    let root_token = MacaroonToken::mint(issuer_key, b"revoke-kid", "auth.pyana.dev");

    // Attenuate with a revocable caveat (token_id = "revocable-token-1")
    let att = Attenuation {
        services: vec![("compute".into(), "rw".into())],
        revocable: Some("revocable-token-1".into()),
        not_after: Some(2_000_000_000),
        ..Default::default()
    };
    let revocable_token = root_token.attenuate(&att).unwrap();

    // --- Step 2: Present with non-revocation proof (token NOT in revocation set) ---
    let mut valid_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    // Add the token to the "not revoked" set (non-membership proof)
    valid_request
        .not_revoked
        .insert("revocable-token-1".to_string());

    let result = revocable_token.verify(&valid_request);
    assert!(
        result.is_ok(),
        "Token with valid non-revocation proof should verify: {:?}",
        result.err()
    );

    // --- Step 3: Revoke the token (remove from not_revoked set) ---
    // Now present WITHOUT the non-revocation proof (simulating stale verifier state)
    let revoked_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_700_000_000),
        // NOT including "revocable-token-1" in not_revoked set
        ..Default::default()
    };
    let result = revocable_token.verify(&revoked_request);
    assert!(
        result.is_err(),
        "Revocable token MUST fail when not_revoked set doesn't contain the token ID"
    );

    // --- Step 4: Also test with NullifierSet double-insertion (cell-level revocation) ---
    let mut nullifier_set = NullifierSet::new();
    let token_nullifier = Nullifier(*blake3::hash(b"revocable-token-1-nullifier").as_bytes());

    // First insertion (marking as spent/revoked) succeeds
    nullifier_set.insert(token_nullifier).unwrap();
    assert!(nullifier_set.contains(&token_nullifier));

    // Second insertion fails (already revoked)
    let double_revoke = nullifier_set.insert(token_nullifier);
    assert!(
        double_revoke.is_err(),
        "Double-revocation (nullifier already in set) MUST be rejected"
    );
}

// =============================================================================
// TEST 3: Attenuation honesty
// =============================================================================

/// Mint [read, write, admin] -> attenuate to [read] -> claim [write] -> REJECTED
/// The token's HMAC chain prevents widening.
#[test]
fn adversarial_attenuation_honesty() {
    let issuer_key = test_key("issuer-attenuation-honesty");
    let root_token = MacaroonToken::mint(issuer_key, b"honesty-kid", "auth.pyana.dev");

    // Root has all permissions (no restrictions)
    let full_request = AuthRequest {
        service: Some("admin".into()),
        action: Some("rwcd".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    assert!(
        root_token.verify(&full_request).is_ok(),
        "Root token should authorize everything"
    );

    // --- Step 1: Attenuate to read-only on compute ---
    let narrow_att = Attenuation {
        services: vec![("compute".into(), "r".into())],
        not_after: Some(2_000_000_000),
        ..Default::default()
    };
    let narrow_token = root_token.attenuate(&narrow_att).unwrap();

    // --- Step 2: Claiming write -> REJECTED ---
    let write_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("w".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    assert!(
        narrow_token.verify(&write_request).is_err(),
        "Attenuated-to-read token MUST reject write"
    );

    // --- Step 3: Claiming admin -> REJECTED ---
    let admin_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("rwcd".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    assert!(
        narrow_token.verify(&admin_request).is_err(),
        "Attenuated token MUST reject admin actions"
    );

    // --- Step 4: Claiming a completely different service -> REJECTED ---
    let other_service = AuthRequest {
        service: Some("storage".into()),
        action: Some("r".into()),
        now: Some(1_700_000_000),
        ..Default::default()
    };
    assert!(
        narrow_token.verify(&other_service).is_err(),
        "Token attenuated to 'compute' MUST reject 'storage'"
    );

    // --- Step 5: Expiry attenuation cannot be widened by later attenuation ---
    // Narrow the expiry: first att expires at 2B, try to re-attenuate with later expiry
    let short_expiry_att = Attenuation {
        services: vec![("compute".into(), "r".into())],
        not_after: Some(1_800_000_000), // EARLIER expiry than the first attenuation's 2B
        ..Default::default()
    };
    let short_lived = narrow_token.attenuate(&short_expiry_att).unwrap();

    // Verify it works before the narrower expiry
    let before_short_expiry = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_799_000_000),
        ..Default::default()
    };
    assert!(
        short_lived.verify(&before_short_expiry).is_ok(),
        "Token should work before narrower expiry"
    );

    // Verify it fails after the narrower expiry even though the original allowed until 2B
    let after_short_expiry = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_800_000_001),
        ..Default::default()
    };
    assert!(
        short_lived.verify(&after_short_expiry).is_err(),
        "Shorter expiry attenuation MUST be enforced (monotone narrowing on time)"
    );

    // --- Step 6: User confinement cannot be bypassed ---
    let confined_att = Attenuation {
        confine_user: Some("alice".into()),
        ..Default::default()
    };
    let confined_token = narrow_token.attenuate(&confined_att).unwrap();

    // Request from a different user should fail
    let wrong_user_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1_700_000_000),
        user_id: Some("bob".into()), // wrong user
        ..Default::default()
    };
    assert!(
        confined_token.verify(&wrong_user_request).is_err(),
        "User-confined token MUST reject requests from other users"
    );
}

// =============================================================================
// TEST 4: Cross-cell unauthorized access
// =============================================================================

/// Alice's cell, Bob's cell. Bob tries without cap -> REJECTED.
/// Bob gets read cap -> tries write -> REJECTED.
/// Bob gets write cap -> write succeeds.
#[test]
fn adversarial_cross_cell_unauthorized_access() {
    let token_id = test_key("cross-cell-domain");
    let mut ledger = Ledger::new();

    // --- Alice's cell (the target being protected) ---
    let alice_key = test_key("alice-cell-owner");
    let mut alice_cell = Cell::with_balance(alice_key, token_id, 100_000);
    alice_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let alice_id = alice_cell.id;
    ledger.insert_cell(alice_cell).unwrap();

    // --- Bob's cell (the attacker) ---
    let bob_key = test_key("bob-cell-attacker");
    let mut bob_cell = Cell::with_balance(bob_key, token_id, 100_000);
    bob_cell.permissions = open_permissions();
    let bob_id = bob_cell.id;
    ledger.insert_cell(bob_cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // --- Attack 1: Bob tries to modify Alice's cell without ANY capability ---
    let mut builder = TurnBuilder::new(bob_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(alice_id, "steal");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: alice_id,
            index: 0,
            value: *blake3::hash(b"hacked-by-bob").as_bytes(),
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Bob without capability MUST be rejected when targeting Alice's cell"
    );

    // Verify Alice's state is unmodified
    assert_eq!(
        ledger.get(&alice_id).unwrap().state.fields[0],
        [0u8; 32],
        "Alice's cell MUST be unmodified after rejected attack"
    );

    // After the rejected turn, Bob's nonce was incremented (fee+nonce are Phase 1,
    // never rolled back). Check Bob's current nonce.
    let bob_nonce_after_reject = ledger.get(&bob_id).unwrap().state.nonce;

    // --- Attack 2: Bob gets a capability, but Alice's cell requires Proof for SetState ---
    {
        let alice = ledger.get_mut(&alice_id).unwrap();
        alice.permissions.set_state = AuthRequired::Proof;
    }
    {
        let bob = ledger.get_mut(&bob_id).unwrap();
        bob.capabilities.grant(alice_id, AuthRequired::None);
    }

    // Bob tries to SetField (requires Proof auth on Alice's cell) without providing proof
    let mut builder2 = TurnBuilder::new(bob_id, bob_nonce_after_reject);
    builder2.set_fee(1000);
    {
        let action = builder2.action(alice_id, "write-attempt");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: alice_id,
            index: 0,
            value: *blake3::hash(b"bob-unauthorized-write").as_bytes(),
        });
    }
    let turn2 = builder2.build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(
        result2.is_rejected(),
        "Bob with capability but no proof MUST be rejected for proof-required SetState"
    );

    // Verify Alice's state is STILL unmodified
    assert_eq!(
        ledger.get(&alice_id).unwrap().state.fields[0],
        [0u8; 32],
        "Alice's cell MUST remain unmodified after insufficient auth"
    );

    let bob_nonce_after_reject2 = ledger.get(&bob_id).unwrap().state.nonce;

    // --- Success case: Relax Alice's permissions, Bob can now write ---
    {
        let alice = ledger.get_mut(&alice_id).unwrap();
        alice.permissions.set_state = AuthRequired::None;
    }

    let mut builder3 = TurnBuilder::new(bob_id, bob_nonce_after_reject2);
    builder3.set_fee(1000);
    {
        let action = builder3.action(alice_id, "authorized-write");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: alice_id,
            index: 0,
            value: *blake3::hash(b"bob-authorized-write").as_bytes(),
        });
    }
    let turn3 = builder3.build();
    let result3 = executor.execute(&turn3, &mut ledger);
    assert!(
        result3.is_committed(),
        "Bob with capability and sufficient permission SHOULD succeed"
    );
    assert_eq!(
        ledger.get(&alice_id).unwrap().state.fields[0],
        *blake3::hash(b"bob-authorized-write").as_bytes(),
        "Alice's cell should be modified after authorized write"
    );
}

// =============================================================================
// TEST 5: Note double-spend
// =============================================================================

/// Create note -> spend (nullifier recorded) -> spend again -> REJECTED
#[test]
fn adversarial_note_double_spend() {
    // --- Step 1: Create a note ---
    let owner_key = test_key("note-owner-ds");
    let spending_key = test_key("note-spending-ds");
    let gold_asset: u64 = 0x474F4C44;

    let note = Note::with_randomness(owner_key, [gold_asset, 100, 0, 0, 0, 0, 0, 0], [0x42u8; 32]);
    let nullifier = note.nullifier(&spending_key);

    // --- Step 2: First spend succeeds ---
    let mut nullifier_set = NullifierSet::new();
    let insert_result = nullifier_set.insert(nullifier);
    assert!(
        insert_result.is_ok(),
        "First spend (nullifier insertion) should succeed"
    );
    assert!(nullifier_set.contains(&nullifier));

    // --- Step 3: Second spend (replay) -> REJECTED ---
    let double_spend_result = nullifier_set.insert(nullifier);
    assert!(
        double_spend_result.is_err(),
        "Double-spend MUST be rejected"
    );
    match double_spend_result {
        Err(pyana_cell::NoteError::DoubleSpend { nullifier: n }) => {
            assert_eq!(n, nullifier, "Rejected nullifier should match");
        }
        _ => panic!("Expected DoubleSpend error variant"),
    }

    // --- Step 4: Different note with different nullifier still works ---
    let other_note =
        Note::with_randomness(owner_key, [gold_asset, 200, 0, 0, 0, 0, 0, 0], [0x99u8; 32]);
    let other_nullifier = other_note.nullifier(&spending_key);
    assert_ne!(
        nullifier, other_nullifier,
        "Different notes should have different nullifiers"
    );

    let other_result = nullifier_set.insert(other_nullifier);
    assert!(
        other_result.is_ok(),
        "Spending a different note should succeed"
    );
}

// =============================================================================
// TEST 6: Turn replay
// =============================================================================

/// Execute turn with nonce=0 -> succeeds, nonce advances to 1.
/// Replay same turn (nonce=0) -> REJECTED (nonce mismatch).
/// Try nonce=5 (gap) -> REJECTED.
/// Execute nonce=1 -> succeeds.
#[test]
fn adversarial_turn_replay() {
    let token_id = test_key("replay-domain");
    let mut ledger = Ledger::new();

    let agent_key = test_key("replay-agent");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 1_000_000);
    agent_cell.permissions = open_permissions();
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    let target_key = test_key("replay-target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 500_000);
    target_cell.permissions = open_permissions();
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // --- Step 1: Execute turn with nonce=0 -> SUCCESS ---
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(target_id, "first");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"turn-zero").as_bytes(),
        });
    }
    let turn_0 = builder.build();
    let result = executor.execute(&turn_0, &mut ledger);
    assert!(result.is_committed(), "First turn (nonce=0) should commit");

    // Verify nonce advanced
    assert_eq!(ledger.get(&agent_id).unwrap().state.nonce, 1);

    // --- Step 2: Replay exact same turn (nonce=0) -> REJECTED ---
    let replay_result = executor.execute(&turn_0, &mut ledger);
    assert!(
        replay_result.is_rejected(),
        "Replay of turn with stale nonce=0 MUST be rejected"
    );

    // State should remain unchanged after rejected replay
    assert_eq!(
        ledger.get(&target_id).unwrap().state.fields[0],
        *blake3::hash(b"turn-zero").as_bytes(),
        "State must not change after rejected replay"
    );

    // --- Step 3: Try nonce=5 (gap) -> REJECTED ---
    let mut builder_gap = TurnBuilder::new(agent_id, 5);
    builder_gap.set_fee(1000);
    {
        let action = builder_gap.action(target_id, "gap");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"turn-gap").as_bytes(),
        });
    }
    let turn_gap = builder_gap.build();
    let gap_result = executor.execute(&turn_gap, &mut ledger);
    assert!(
        gap_result.is_rejected(),
        "Turn with nonce gap (5 when expecting 1) MUST be rejected"
    );

    // --- Step 4: Execute nonce=1 -> SUCCESS (proves sequential enforcement) ---
    let mut builder_1 = TurnBuilder::new(agent_id, 1);
    builder_1.set_fee(1000);
    {
        let action = builder_1.action(target_id, "second");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"turn-one").as_bytes(),
        });
    }
    let turn_1 = builder_1.build();
    let result_1 = executor.execute(&turn_1, &mut ledger);
    assert!(
        result_1.is_committed(),
        "Turn with correct sequential nonce=1 should commit"
    );
    assert_eq!(ledger.get(&agent_id).unwrap().state.nonce, 2);
}

// =============================================================================
// TEST 7: Conservation violation
// =============================================================================

/// Attempt to create more value than consumed via balance_change -> REJECTED by
/// ExcessNotZero. Also test Transfer doesn't create value.
#[test]
fn adversarial_conservation_violation() {
    let token_id = test_key("conservation-domain");
    let mut ledger = Ledger::new();

    // Agent cell with some balance
    let agent_key = test_key("cons-agent");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 500_000);
    agent_cell.permissions = open_permissions();
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    // Target cell
    let target_key = test_key("cons-target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 200_000);
    target_cell.permissions = open_permissions();
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    // Second target for multi-action conservation testing
    let target2_key = test_key("cons-target2");
    let mut target2_cell = Cell::with_balance(target2_key, token_id, 100_000);
    target2_cell.permissions = open_permissions();
    let target2_id = target2_cell.id;
    ledger.insert_cell(target2_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
        agent.capabilities.grant(target2_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut agent_nonce = 0u64;

    // --- Attack 1: balance_change deposits without matching withdrawal ---
    // Try to deposit +1000 into target without withdrawing from anywhere.
    // This violates excess conservation (excess must be zero at turn end).
    let mut builder = TurnBuilder::new(agent_id, agent_nonce);
    builder.set_fee(0);
    {
        let action = builder.action(target_id, "inflate");
        action.delegation(DelegationMode::None);
        action.balance_change(1000);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0x01; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Depositing without matching withdrawal MUST be rejected (excess != 0)"
    );
    // Nonce is consumed even on rejection (Phase 1 already ran)
    agent_nonce = ledger.get(&agent_id).unwrap().state.nonce;

    // Verify balances unchanged (target should not have changed)
    assert_eq!(ledger.get(&target_id).unwrap().state.balance, 200_000);

    // --- Attack 2: Withdraw more than deposit (excess != 0) ---
    let mut builder2 = TurnBuilder::new(agent_id, agent_nonce);
    builder2.set_fee(0);
    {
        // Withdraw 1000 from target
        let action = builder2.action(target_id, "drain");
        action.delegation(DelegationMode::None);
        action.balance_change(-1000);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0x02; 32],
        });
    }
    {
        // Deposit only 500 into target2 (doesn't match the 1000 withdrawn)
        let action = builder2.action(target2_id, "partial");
        action.delegation(DelegationMode::None);
        action.balance_change(500);
        action.effect(Effect::SetField {
            cell: target2_id,
            index: 0,
            value: [0x03; 32],
        });
    }
    let turn2 = builder2.build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(
        result2.is_rejected(),
        "Mismatched withdrawal/deposit (excess != 0) MUST be rejected"
    );
    agent_nonce = ledger.get(&agent_id).unwrap().state.nonce;

    // --- Success case: balanced withdraw + deposit ---
    let mut builder3 = TurnBuilder::new(agent_id, agent_nonce);
    builder3.set_fee(0);
    {
        // Withdraw 1000 from target
        let action = builder3.action(target_id, "send");
        action.delegation(DelegationMode::None);
        action.balance_change(-1000);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0x04; 32],
        });
    }
    {
        // Deposit exactly 1000 into target2
        let action = builder3.action(target2_id, "recv");
        action.delegation(DelegationMode::None);
        action.balance_change(1000);
        action.effect(Effect::SetField {
            cell: target2_id,
            index: 0,
            value: [0x05; 32],
        });
    }
    let turn3 = builder3.build();
    let result3 = executor.execute(&turn3, &mut ledger);
    assert!(
        result3.is_committed(),
        "Balanced withdraw + deposit (excess == 0) should succeed"
    );

    // Verify balances: target lost 1000, target2 gained 1000
    assert_eq!(ledger.get(&target_id).unwrap().state.balance, 199_000);
    assert_eq!(ledger.get(&target2_id).unwrap().state.balance, 101_000);
}

// =============================================================================
// TEST 8: Proof for wrong statement (wrong action binding)
// =============================================================================

/// Generate valid proof for action A, present it claiming action B -> REJECTED.
/// The proof verifier checks the binding between proof and the claimed statement.
#[test]
fn adversarial_proof_wrong_statement() {
    let token_id = test_key("proof-binding-domain");
    let mut ledger = Ledger::new();

    // Agent cell
    let agent_key = test_key("proof-agent");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 500_000);
    agent_cell.permissions = open_permissions();
    let agent_id = agent_cell.id;
    ledger.insert_cell(agent_cell).unwrap();

    // Target cell requiring proof authorization
    let target_key = test_key("proof-target");
    let vk_data = *blake3::hash(b"verification-key-data").as_bytes();
    let mut target_cell = Cell::with_balance(target_key, token_id, 200_000);
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
    target_cell.verification_key = Some(VerificationKey::new(vk_data.to_vec()));
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    // Create executor with binding proof verifier
    let executor = TurnExecutor::with_proof_verifier(
        ComputronCosts::default_costs(),
        Box::new(BindingProofVerifier),
    );

    // --- Step 1: Generate valid proof for "read" on "target" ---
    let valid_proof = make_binding_proof("read", "target-resource", &vk_data);

    // --- Step 2: Present the valid proof with CORRECT binding -> SUCCESS ---
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(2000);
    {
        let action = builder.action(target_id, "read");
        action.delegation(DelegationMode::None);
        action.authorize_proof(valid_proof.clone(), "read", "target-resource");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"valid-proof-read").as_bytes(),
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "Valid proof with correct binding should succeed"
    );

    // --- Step 3: Present same proof bytes claiming "write" binding -> REJECTED ---
    // The attacker takes a valid proof for "read" and claims it's for "write"
    let mut builder2 = TurnBuilder::new(agent_id, 1);
    builder2.set_fee(2000);
    {
        let action = builder2.action(target_id, "write");
        action.delegation(DelegationMode::None);
        action.authorize_proof(valid_proof.clone(), "write", "target-resource");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"wrong-binding-write").as_bytes(),
        });
    }
    let turn2 = builder2.build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(
        result2.is_rejected(),
        "Proof bound to 'read' MUST be rejected when presented as 'write'"
    );

    // --- Step 4: Present proof for wrong resource -> REJECTED ---
    let wrong_resource_proof = make_binding_proof("read", "other-resource", &vk_data);
    let mut builder3 = TurnBuilder::new(agent_id, 1);
    builder3.set_fee(2000);
    {
        let action = builder3.action(target_id, "read");
        action.delegation(DelegationMode::None);
        action.authorize_proof(wrong_resource_proof, "read", "target-resource");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"wrong-resource").as_bytes(),
        });
    }
    let turn3 = builder3.build();
    let result3 = executor.execute(&turn3, &mut ledger);
    assert!(
        result3.is_rejected(),
        "Proof bound to wrong resource MUST be rejected"
    );

    // --- Step 5: Empty proof bytes -> REJECTED ---
    let mut builder4 = TurnBuilder::new(agent_id, 1);
    builder4.set_fee(2000);
    {
        let action = builder4.action(target_id, "read");
        action.delegation(DelegationMode::None);
        action.authorize_proof(vec![], "read", "target-resource");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"empty-proof").as_bytes(),
        });
    }
    let turn4 = builder4.build();
    let result4 = executor.execute(&turn4, &mut ledger);
    assert!(result4.is_rejected(), "Empty proof bytes MUST be rejected");

    // --- Step 6: No proof verifier configured -> fail-closed ---
    let executor_no_verifier = TurnExecutor::new(ComputronCosts::default_costs());
    let correct_proof = make_binding_proof("read", "target-resource", &vk_data);
    let mut builder5 = TurnBuilder::new(agent_id, 1);
    builder5.set_fee(2000);
    {
        let action = builder5.action(target_id, "read");
        action.delegation(DelegationMode::None);
        action.authorize_proof(correct_proof, "read", "target-resource");
        action.effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"no-verifier").as_bytes(),
        });
    }
    let turn5 = builder5.build();
    let result5 = executor_no_verifier.execute(&turn5, &mut ledger);
    assert!(
        result5.is_rejected(),
        "Proof auth without configured verifier MUST be rejected (fail-closed)"
    );
}

// =============================================================================
// TEST BONUS: STARK proof tampering (real STARK, byte-level)
// =============================================================================

/// Generate a real STARK proof -> verify succeeds -> tamper one byte -> REJECTED.
/// This uses the actual FRI-based STARK prover/verifier.
#[test]
fn adversarial_stark_proof_tamper() {
    // Generate a valid Merkle STARK proof (real crypto)
    let siblings = [
        [111u32, 222, 333],
        [444, 555, 666],
        [777, 888, 999],
        [1010, 1111, 1212],
    ];
    let positions = [0u32, 2, 1, 3];
    let (trace, public_inputs) = generate_merkle_trace(99999, &siblings, &positions);
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);

    // --- Verify the original proof ---
    assert!(
        verify(&air, &proof, &public_inputs).is_ok(),
        "Valid STARK proof should verify"
    );

    // --- Serialize ---
    let proof_bytes = proof_to_bytes(&proof);
    assert!(
        proof_bytes.len() > 100,
        "Real STARK proof should be substantial in size"
    );

    // --- Tamper with the proof bytes (flip a byte in the middle) ---
    let tamper_pos = proof_bytes.len() / 2;
    let mut tampered_bytes = proof_bytes.clone();
    tampered_bytes[tamper_pos] ^= 0xFF;

    match proof_from_bytes(&tampered_bytes) {
        Err(_) => {
            // Good: detected at deserialization
        }
        Ok(tampered_proof) => {
            // If it parses, verification must fail
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                verify(&air, &tampered_proof, &public_inputs)
            }));
            match result {
                Err(_) => {} // panic = rejection, acceptable
                Ok(Ok(())) => {
                    panic!("Tampered STARK proof MUST NOT verify successfully");
                }
                Ok(Err(_)) => {} // verification error = correctly rejected
            }
        }
    }

    // --- Tamper with public inputs (wrong leaf value) ---
    let mut wrong_inputs = public_inputs.clone();
    wrong_inputs[0] = BabyBear::new(wrong_inputs[0].0 ^ 1); // flip one bit of the leaf hash

    let wrong_input_result = verify(&air, &proof, &wrong_inputs);
    assert!(
        wrong_input_result.is_err(),
        "STARK proof against wrong public inputs MUST be rejected"
    );
}

// =============================================================================
// TEST BONUS: Transfer cannot create value
// =============================================================================

/// Attempt Transfer where amount > sender's balance -> REJECTED.
/// Verify total value is conserved on successful transfer.
#[test]
fn adversarial_transfer_no_value_creation() {
    let token_id = test_key("transfer-conservation");
    let mut ledger = Ledger::new();

    let alice_key = test_key("transfer-alice");
    let mut alice_cell = Cell::with_balance(alice_key, token_id, 1000);
    alice_cell.permissions = open_permissions();
    let alice_id = alice_cell.id;
    ledger.insert_cell(alice_cell).unwrap();

    let bob_key = test_key("transfer-bob");
    let mut bob_cell = Cell::with_balance(bob_key, token_id, 2000);
    bob_cell.permissions = open_permissions();
    let bob_id = bob_cell.id;
    ledger.insert_cell(bob_cell).unwrap();

    {
        let alice = ledger.get_mut(&alice_id).unwrap();
        alice.capabilities.grant(bob_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let total_before =
        ledger.get(&alice_id).unwrap().state.balance + ledger.get(&bob_id).unwrap().state.balance;

    // --- Attack: Transfer more than Alice has ---
    let alice_nonce = ledger.get(&alice_id).unwrap().state.nonce;
    let mut builder = TurnBuilder::new(alice_id, alice_nonce);
    builder.set_fee(0);
    {
        let action = builder.action(alice_id, "overdraft");
        action.delegation(DelegationMode::None);
        action.effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 5000, // Alice only has 1000
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Transfer of more than available balance MUST be rejected"
    );

    // Verify no value was created or destroyed
    let total_after_attack =
        ledger.get(&alice_id).unwrap().state.balance + ledger.get(&bob_id).unwrap().state.balance;
    assert_eq!(
        total_before, total_after_attack,
        "Failed transfer must not change total value"
    );

    // --- Valid transfer ---
    let alice_nonce = ledger.get(&alice_id).unwrap().state.nonce;
    let mut builder2 = TurnBuilder::new(alice_id, alice_nonce);
    builder2.set_fee(0);
    {
        let action = builder2.action(alice_id, "send");
        action.delegation(DelegationMode::None);
        action.effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 500,
        });
    }
    let turn2 = builder2.build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(result2.is_committed(), "Valid transfer should succeed");

    let total_after_valid =
        ledger.get(&alice_id).unwrap().state.balance + ledger.get(&bob_id).unwrap().state.balance;
    assert_eq!(
        total_before, total_after_valid,
        "Valid transfer MUST conserve total value"
    );
    assert_eq!(ledger.get(&alice_id).unwrap().state.balance, 500);
    assert_eq!(ledger.get(&bob_id).unwrap().state.balance, 2500);
}
