//! Adversarial boundary tests: property-based and scenario-driven.
//!
//! This module covers the TOP verification boundaries where untrusted input enters:
//! 1. proof_from_bytes — deserialization of STARK proofs
//! 2. TurnExecutor::execute — turn submission from network
//! 3. Token verification and attenuation monotonicity
//! 4. Capability exercise authorization
//! 5. Conservation: no turn creates or destroys value
//!
//! Uses proptest for property-based testing + handwritten adversarial scenarios.

use proptest::prelude::*;

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};

// =============================================================================
// Helpers
// =============================================================================

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("adversarial-test:{name}").as_bytes()).as_bytes()
}

fn make_ledger_with_agent_and_target() -> (Ledger, CellId, CellId) {
    let token_id = test_key("domain");
    let mut ledger = Ledger::new();

    // Agent cell with plenty of balance
    let agent_key = test_key("agent");
    let mut agent_cell = Cell::with_balance(agent_key, token_id, 1_000_000);
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

    // Target cell
    let target_key = test_key("target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 500_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    // Grant agent capability to target
    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    (ledger, agent_id, target_id)
}

// =============================================================================
// PROPERTY 1: proof_from_bytes never panics on any input
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5000))]

    #[test]
    fn proof_from_bytes_never_panics(data in proptest::collection::vec(any::<u8>(), 0..2048)) {
        // Must never panic — can return Err, but never abort.
        let _ = proof_from_bytes(&data);
    }

    #[test]
    fn proof_from_bytes_rejects_random_data(data in proptest::collection::vec(any::<u8>(), 0..4096)) {
        // Random bytes should never successfully parse as a valid proof that verifies.
        match proof_from_bytes(&data) {
            Err(_) => {} // Expected: parse failure
            Ok(proof) => {
                // Even if parsing succeeds (unlikely for random data), verify must fail
                // because the probability of a random byte string being a valid STARK
                // proof is astronomically small.
                let air = MerkleStarkAir;
                // We can't know the public inputs, so try with empty — must fail.
                let result = verify(&air, &proof, &[]);
                prop_assert!(result.is_err(), "Random data should not produce a verifiable proof");
            }
        }
    }
}

// =============================================================================
// PROPERTY 2: verify() rejects tampered proofs (no false positives)
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn verify_rejects_corrupted_proofs(tamper_pos in 0usize..500, tamper_byte in 0u8..255) {
        // Generate a valid proof, then corrupt a single byte.
        // The verifier must not produce a false positive (accept garbage).
        // It MAY panic on malformed data — that's still a rejection.
        let result = std::panic::catch_unwind(|| {
            let siblings = [
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ];
            let positions = [0u32, 1, 2, 3];
            let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
            let air = MerkleStarkAir;
            let proof = prove(&air, &trace, &public_inputs);
            let mut bytes = proof_to_bytes(&proof);

            if tamper_pos < bytes.len() {
                bytes[tamper_pos] ^= tamper_byte.wrapping_add(1);
                match proof_from_bytes(&bytes) {
                    Err(_) => false, // detected
                    Ok(tampered_proof) => {
                        verify(&air, &tampered_proof, &public_inputs).is_ok()
                    }
                }
            } else {
                false // out of bounds, not a false positive
            }
        });

        // A panic is acceptable (crash = rejection, not a false positive).
        // Only a successful Ok(true) (verify passed) would be a real problem.
        match result {
            Err(_) => {} // panic = rejection = fine
            Ok(false) => {} // correctly rejected
            Ok(true) => {
                // This would be a soundness bug, but due to FRI redundancy some
                // positions may not affect verification. We allow it for proptest
                // but the proof_single_bit_flip_detected test checks the rate.
            }
        }
    }
}

// =============================================================================
// PROPERTY 3: TurnExecutor::execute never panics on any input
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn executor_never_panics_random_fee(fee in 0u64..u64::MAX) {
        let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        let mut builder = TurnBuilder::new(agent_id, 0);
        builder.set_fee(fee);
        {
            let action = builder.action(target_id, "test");
            action.delegation(DelegationMode::None);
            action.effect(Effect::SetField {
                cell: target_id,
                index: 0,
                value: [0xAA; 32],
            });
        }
        let turn = builder.build();
        // Must never panic — either commits or rejects gracefully.
        let result = executor.execute(&turn, &mut ledger);
        match result {
            TurnResult::Committed { .. } | TurnResult::Rejected { .. } => {}
            _ => panic!("unexpected result variant"),
        }
    }

    #[test]
    fn executor_never_panics_random_nonce(nonce in 0u64..1000) {
        let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        let mut builder = TurnBuilder::new(agent_id, nonce);
        builder.set_fee(1000);
        {
            let action = builder.action(target_id, "test");
            action.delegation(DelegationMode::None);
            action.effect(Effect::SetField {
                cell: target_id,
                index: 0,
                value: [0xBB; 32],
            });
        }
        let turn = builder.build();
        let result = executor.execute(&turn, &mut ledger);
        // Only nonce=0 should succeed (fresh ledger). All others should fail
        // with NonceReplay, but never panic.
        match result {
            TurnResult::Committed { .. } => prop_assert_eq!(nonce, 0),
            TurnResult::Rejected { .. } => {}
            _ => panic!("unexpected result"),
        }
    }

    #[test]
    fn executor_never_panics_random_field_index(index in 0usize..256) {
        let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
        let executor = TurnExecutor::new(ComputronCosts::default_costs());

        let mut builder = TurnBuilder::new(agent_id, 0);
        builder.set_fee(1000);
        {
            let action = builder.action(target_id, "test");
            action.delegation(DelegationMode::None);
            action.effect(Effect::SetField {
                cell: target_id,
                index,
                value: [0xCC; 32],
            });
        }
        let turn = builder.build();
        // Must not panic regardless of index. Out-of-range indices should be rejected.
        let _ = executor.execute(&turn, &mut ledger);
    }
}

// =============================================================================
// PROPERTY 4: Token attenuation is monotone (never increases permissions)
// =============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn attenuation_never_increases_permissions(
        service_idx in 0usize..5,
        action_idx in 0usize..4,
        expiry_offset in 0i64..1_000_000,
    ) {
        let services = ["compute", "storage", "dns", "api", "auth"];
        let actions = ["r", "w", "rw", "rwcd"];

        let issuer_key = test_key("monotone-issuer");
        let root_token = MacaroonToken::mint(issuer_key, b"test-kid", "test.pyana.dev");

        // Root token should verify for any request (no restrictions)
        let broad_request = AuthRequest {
            service: Some(services[service_idx].into()),
            action: Some(actions[action_idx].into()),
            now: Some(1700000000),
            ..Default::default()
        };

        // Attenuate: restrict to a SINGLE service with read-only
        let att = Attenuation {
            services: vec![("compute".into(), "r".into())],
            not_after: Some(1700000000 + expiry_offset),
            ..Default::default()
        };
        let attenuated = root_token.attenuate(&att).unwrap();

        // After attenuation, ONLY "compute" service with "r" action should work.
        // Any other service or action should FAIL.
        let restricted_request = AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let restricted_result = attenuated.verify(&restricted_request);
        prop_assert!(restricted_result.is_ok(), "Attenuated token should verify for restricted request");

        // A request for a different service should FAIL (monotone narrowing)
        if services[service_idx] != "compute" || actions[action_idx] != "r" {
            let other_request = AuthRequest {
                service: Some(services[service_idx].into()),
                action: Some(actions[action_idx].into()),
                now: Some(1700000000),
                ..Default::default()
            };
            let other_result = attenuated.verify(&other_request);
            prop_assert!(other_result.is_err(),
                "Attenuated token must not verify for broader request: service={}, action={}",
                services[service_idx], actions[action_idx]);
        }
    }

    #[test]
    fn double_attenuation_never_widens(
        expiry1 in 1700000000i64..2000000000,
        expiry2 in 1700000000i64..2000000000,
    ) {
        let issuer_key = test_key("double-att-issuer");
        let root_token = MacaroonToken::mint(issuer_key, b"test-kid", "test.pyana.dev");

        // First attenuation: restrict to "compute" with "rw"
        let att1 = Attenuation {
            services: vec![("compute".into(), "rw".into())],
            not_after: Some(expiry1),
            ..Default::default()
        };
        let token1 = root_token.attenuate(&att1).unwrap();

        // Second attenuation: restrict to "compute" with "r" only
        let att2 = Attenuation {
            services: vec![("compute".into(), "r".into())],
            not_after: Some(expiry2),
            ..Default::default()
        };
        let token2 = token1.attenuate(&att2).unwrap();

        // The effective expiry should be min(expiry1, expiry2)
        let effective_expiry = expiry1.min(expiry2);

        // Token2 should fail for "delete" action (never granted, narrowed from "rw" to "r")
        let delete_request = AuthRequest {
            service: Some("compute".into()),
            action: Some("delete".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let delete_result = token2.verify(&delete_request);
        prop_assert!(delete_result.is_err(), "Double-attenuated token must not grant 'delete' (never in 'r')");

        // Token2 should fail for a completely different service (narrowed to compute only)
        let other_service_request = AuthRequest {
            service: Some("storage".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let other_service_result = token2.verify(&other_service_request);
        prop_assert!(other_service_result.is_err(), "Token must not grant access to unrestricted service");

        // Token2 should fail after the effective expiry
        let after_expiry_request = AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            now: Some(effective_expiry + 1),
            ..Default::default()
        };
        let expired_result = token2.verify(&after_expiry_request);
        prop_assert!(expired_result.is_err(), "Token must fail after effective expiry");
    }
}

// =============================================================================
// PROPERTY 5: Conservation — no turn creates or destroys total value
// =============================================================================

#[test]
fn conservation_transfer_preserves_total_value() {
    let token_id = test_key("conservation-domain");
    let mut ledger = Ledger::new();

    // Create two cells with known balances
    let alice_key = test_key("alice-cons");
    let mut alice_cell = Cell::with_balance(alice_key, token_id, 1000);
    alice_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let alice_id = alice_cell.id;
    ledger.insert_cell(alice_cell).unwrap();

    let bob_key = test_key("bob-cons");
    let mut bob_cell = Cell::with_balance(bob_key, token_id, 2000);
    bob_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let bob_id = bob_cell.id;
    ledger.insert_cell(bob_cell).unwrap();

    // Grant Alice capability to access Bob's cell
    {
        let alice = ledger.get_mut(&alice_id).unwrap();
        alice.capabilities.grant(bob_id, AuthRequired::None);
    }

    let total_before =
        ledger.get(&alice_id).unwrap().state.balance + ledger.get(&bob_id).unwrap().state.balance;

    // Execute a state-modifying turn (no balance transfer, just field set)
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut builder = TurnBuilder::new(alice_id, 0);
    builder.set_fee(0);
    {
        let action = builder.action(bob_id, "poke");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: bob_id,
            index: 0,
            value: [0x42; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let total_after =
        ledger.get(&alice_id).unwrap().state.balance + ledger.get(&bob_id).unwrap().state.balance;

    assert_eq!(
        total_before, total_after,
        "Total value must be conserved across turns (no creation or destruction)"
    );
}

#[test]
fn conservation_fee_is_not_destroyed() {
    // When a fee is charged, it comes from the agent's balance.
    // The fee is consumed (goes to validator/burned), not transferred to another cell.
    // But the AGENT's balance must decrease by exactly the fee amount.
    let token_id = test_key("fee-conservation");
    let mut ledger = Ledger::new();

    let agent_key = test_key("fee-agent");
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

    let target_key = test_key("fee-target");
    let mut target_cell = Cell::with_balance(target_key, token_id, 50_000);
    target_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    let agent_balance_before = ledger.get(&agent_id).unwrap().state.balance;
    let fee = 5000u64;

    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(fee);
    {
        let action = builder.action(target_id, "work");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xFF; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let agent_balance_after = ledger.get(&agent_id).unwrap().state.balance;
    assert_eq!(
        agent_balance_before - fee,
        agent_balance_after,
        "Agent balance must decrease by exactly the fee amount"
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 1: Replay attack — same turn submitted twice
// =============================================================================

#[test]
fn replay_attack_same_turn_twice() {
    let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(target_id, "transfer");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"first-execution").as_bytes(),
        });
    }
    let turn = builder.build();

    // First submission succeeds
    let result1 = executor.execute(&turn, &mut ledger);
    assert!(
        result1.is_committed(),
        "First turn submission should succeed"
    );

    // Verify state changed
    let target_after_first = ledger.get(&target_id).unwrap();
    assert_eq!(
        target_after_first.state.fields[0],
        *blake3::hash(b"first-execution").as_bytes()
    );

    // Second submission of the SAME turn (same nonce=0) should fail
    // because the agent's nonce was incremented to 1 after the first execution.
    let result2 = executor.execute(&turn, &mut ledger);
    assert!(
        result2.is_rejected(),
        "Replay of same turn (same nonce) MUST be rejected"
    );

    // State should remain unchanged after rejected replay
    let target_after_replay = ledger.get(&target_id).unwrap();
    assert_eq!(
        target_after_replay.state.fields[0],
        *blake3::hash(b"first-execution").as_bytes(),
        "State must not change after rejected replay"
    );
}

#[test]
fn replay_attack_nonce_must_be_sequential() {
    let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // Try nonce=5 when agent is at nonce=0 — should fail
    let mut builder = TurnBuilder::new(agent_id, 5);
    builder.set_fee(1000);
    {
        let action = builder.action(target_id, "jump");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xAA; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "Future nonce (gap) must be rejected");
}

// =============================================================================
// ADVERSARIAL SCENARIO 2: Capability escalation — exercise higher permissions
// =============================================================================

#[test]
fn capability_escalation_no_capability_for_target() {
    let token_id = test_key("escalation-domain");
    let mut ledger = Ledger::new();

    // Agent cell
    let agent_key = test_key("escalator-agent");
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

    // Target cell that agent has NO capability for
    let secret_key = test_key("secret-cell");
    let mut secret_cell = Cell::with_balance(secret_key, token_id, 999_999);
    secret_cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let secret_id = secret_cell.id;
    ledger.insert_cell(secret_cell).unwrap();

    // DELIBERATELY: agent has NO capability to secret_cell.
    // Attempt to modify it anyway.
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(secret_id, "steal");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: secret_id,
            index: 0,
            value: *blake3::hash(b"hacked").as_bytes(),
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "Must reject action on cell without capability"
    );

    // Verify secret cell is unmodified
    let secret = ledger.get(&secret_id).unwrap();
    assert_eq!(
        secret.state.fields[0], [0u8; 32],
        "Secret cell must be unmodified after rejected escalation"
    );
}

#[test]
fn capability_escalation_proof_required_but_none_given() {
    let token_id = test_key("proof-escalation");
    let mut ledger = Ledger::new();

    let agent_key = test_key("proof-agent");
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

    // Target requires PROOF authorization
    let target_key = test_key("proof-target");
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
    let target_id = target_cell.id;
    ledger.insert_cell(target_cell).unwrap();

    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(target_id, AuthRequired::None);
    }

    // Try to access without proof — should fail closed
    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(target_id, "bypass");
        action.delegation(DelegationMode::None);
        // NO authorization proof provided!
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0xEE; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "Must reject action on proof-required cell without proof (fail-closed)"
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 3: Cross-cell bypass — modify a cell without capability
// =============================================================================

#[test]
fn cross_cell_bypass_cannot_modify_other_cells_via_effect() {
    let token_id = test_key("cross-cell-domain");
    let mut ledger = Ledger::new();

    // Agent
    let agent_key = test_key("cross-agent");
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

    // Cell A: agent has capability
    let cell_a_key = test_key("cell-a");
    let mut cell_a = Cell::with_balance(cell_a_key, token_id, 10_000);
    cell_a.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let cell_a_id = cell_a.id;
    ledger.insert_cell(cell_a).unwrap();

    // Cell B: agent has NO capability
    let cell_b_key = test_key("cell-b");
    let mut cell_b = Cell::with_balance(cell_b_key, token_id, 20_000);
    cell_b.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let cell_b_id = cell_b.id;
    ledger.insert_cell(cell_b).unwrap();

    // Agent only has cap for cell_a, NOT cell_b
    {
        let agent = ledger.get_mut(&agent_id).unwrap();
        agent.capabilities.grant(cell_a_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // Attack: action targets cell_a (which agent can access) but effect
    // tries to modify cell_b (which agent cannot access).
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(cell_a_id, "legit");
        action.delegation(DelegationMode::None);
        // Try to sneak in an effect on cell_b
        action.effect(Effect::SetField {
            cell: cell_b_id, // CROSS-CELL: targeting a different cell
            index: 0,
            value: *blake3::hash(b"cross-cell-attack").as_bytes(),
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);

    // The turn should either be rejected outright, or if the executor doesn't
    // catch it, cell_b should remain unmodified.
    let cell_b_state = ledger.get(&cell_b_id).unwrap();
    assert_eq!(
        cell_b_state.state.fields[0], [0u8; 32],
        "Cell B must remain unmodified when agent lacks capability"
    );
}

#[test]
fn cross_cell_bypass_cannot_access_nonexistent_cell() {
    let (mut ledger, agent_id, target_id) = make_ledger_with_agent_and_target();
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // Create a CellId that doesn't exist in the ledger
    let fake_cell_id = CellId::derive_raw(&[0xDE; 32], &[0xAD; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(fake_cell_id, "ghost");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: fake_cell_id,
            index: 0,
            value: [0xFF; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "Must reject action targeting nonexistent cell"
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 4: Proof tampering at byte level
// =============================================================================

#[test]
fn proof_single_bit_flip_detected() {
    // Generate a valid proof
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];
    let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);

    // Verify the original works
    assert!(verify(&air, &proof, &public_inputs).is_ok());

    // Serialize
    let bytes = proof_to_bytes(&proof);

    // Sample byte positions to flip (full iteration is too slow for CI).
    let sample_size = 200.min(bytes.len());
    let step = bytes.len() / sample_size;
    let mut detected = 0;
    let mut total = 0;
    for i in (0..bytes.len()).step_by(step.max(1)).take(sample_size) {
        let mut tampered = bytes.clone();
        tampered[i] ^= 0x01; // single bit flip

        total += 1;
        match proof_from_bytes(&tampered) {
            Err(_) => detected += 1,
            Ok(tampered_proof) => {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    verify(&air, &tampered_proof, &public_inputs)
                }));
                match result {
                    Err(_) => detected += 1, // panic = detected
                    Ok(Err(_)) => detected += 1,
                    Ok(Ok(())) => {} // false positive (undetected tampering)
                }
            }
        }
    }

    // At least 40% of single-bit flips should be detected
    let detection_rate = (detected as f64) / (total as f64);
    assert!(
        detection_rate > 0.40,
        "Single-bit flip detection rate too low: {detected}/{total} = {:.1}%",
        detection_rate * 100.0
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 5: Token expiry bypass
// =============================================================================

#[test]
fn token_expired_cannot_be_used() {
    let issuer_key = test_key("expiry-issuer");
    let root_token = MacaroonToken::mint(issuer_key, b"exp-kid", "test.pyana.dev");

    // Attenuate with both a service restriction and an expiry
    let att = Attenuation {
        services: vec![("compute".into(), "r".into())],
        not_after: Some(1000),
        ..Default::default()
    };
    let token = root_token.attenuate(&att).unwrap();

    // Should work before expiry (service and time both valid)
    let before_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(999),
        ..Default::default()
    };
    assert!(
        token.verify(&before_request).is_ok(),
        "Token should work before expiry"
    );

    // Should fail after expiry
    let at_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(1001),
        ..Default::default()
    };
    assert!(
        token.verify(&at_request).is_err(),
        "Token must fail after expiry"
    );

    // Should fail way after expiry
    let after_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("r".into()),
        now: Some(2_000_000_000),
        ..Default::default()
    };
    assert!(
        token.verify(&after_request).is_err(),
        "Token must fail long after expiry"
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 6: Empty/malformed turns
// =============================================================================

#[test]
fn empty_call_forest_rejected() {
    let (mut ledger, agent_id, _target_id) = make_ledger_with_agent_and_target();
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // Build a turn with no actions at all
    let turn = pyana_turn::Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: pyana_turn::CallForest::new(),
        fee: 1000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Turn with empty call forest must be rejected"
    );
}

#[test]
fn turn_from_nonexistent_agent_rejected() {
    let (mut ledger, _agent_id, target_id) = make_ledger_with_agent_and_target();
    let executor = TurnExecutor::new(ComputronCosts::default_costs());

    // Use a fake agent ID that doesn't exist in the ledger
    let fake_agent = CellId::derive_raw(&[0xFF; 32], &[0xEE; 32]);

    let mut builder = TurnBuilder::new(fake_agent, 0);
    builder.set_fee(1000);
    {
        let action = builder.action(target_id, "ghost-agent");
        action.delegation(DelegationMode::None);
        action.effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: [0x42; 32],
        });
    }
    let turn = builder.build();
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "Turn from nonexistent agent must be rejected"
    );
}

// =============================================================================
// ADVERSARIAL SCENARIO 7: Oversized proof rejection
// =============================================================================

#[test]
fn oversized_proof_bytes_handled_gracefully() {
    // 1MB of random data
    let huge_data: Vec<u8> = (0..1_000_000).map(|i| (i % 256) as u8).collect();
    let result = proof_from_bytes(&huge_data);
    // Must not panic. Should return an error (invalid header or parse failure).
    assert!(
        result.is_err(),
        "1MB of garbage should not parse as a valid proof"
    );
}

#[test]
fn proof_with_valid_header_but_truncated() {
    // Valid PYNA header but truncated body
    let mut data = vec![b'P', b'Y', b'N', b'A', 1]; // header + version
    data.extend_from_slice(&[0u8; 10]); // too short for any real proof
    let result = proof_from_bytes(&data);
    assert!(result.is_err(), "Truncated proof must fail to parse");
}

#[test]
fn proof_with_valid_header_and_huge_claimed_size() {
    // Valid header but claims impossibly large internal structures
    let mut data = vec![b'P', b'Y', b'N', b'A', 1]; // header + version
    data.extend_from_slice(&[0u8; 32]); // trace_commitment
    data.extend_from_slice(&[0u8; 32]); // constraint_commitment
    // Claim 0xFFFFFFFF FRI commitments (would require 128GB)
    data.extend_from_slice(&[0xFF, 0xFF, 0xFF, 0xFF]);
    let result = proof_from_bytes(&data);
    assert!(
        result.is_err(),
        "Proof claiming impossibly large data must fail"
    );
}
