//! Factory and Sovereign checks: deploy, peer exchange, multi-party atomic, IVC history.

use pyana_cell::{
    AuthRequired, Cell, CellId, CellMode, ChildVkStrategy, FactoryDescriptor, FactoryRegistry,
    FieldConstraint, Ledger, Permissions,
};
use pyana_circuit::BabyBear;
use pyana_circuit::fold_air::{FoldWitness, compute_test_checks_commitment};
use pyana_circuit::ivc::{FoldDelta, IvcVerification, prove_ivc, verify_ivc};
use pyana_turn::builder::ActionBuilder;
use pyana_turn::{ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-sovereign:{name}").as_bytes()).as_bytes()
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

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("deploy", check_factory_deploy),
        run_check("peer_exchange", check_sovereign_peer_exchange),
        run_check("atomic", check_multi_party_atomic),
        run_check("ivc", check_ivc_history_compression),
    ]
}

fn check_factory_deploy() -> Result<(), String> {
    let mut registry = FactoryRegistry::new();

    let factory_vk = test_key("factory-deploy");
    let descriptor = FactoryDescriptor {
        factory_vk,
        child_program_vk: None,
        child_vk_strategy: Some(ChildVkStrategy::Derived {
            base_vk: factory_vk,
        }),
        allowed_cap_templates: vec![],
        field_constraints: vec![
            FieldConstraint::NonZero { field_index: 0 },
            FieldConstraint::Range {
                field_index: 1,
                min: 1,
                max: 100,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(1000),
    };

    registry.deploy(descriptor);

    // Verify factory is registered
    let retrieved = registry.get(&factory_vk).ok_or("factory not in registry")?;
    if retrieved.factory_vk != factory_vk {
        return Err("factory VK mismatch".into());
    }

    // Verify VK derivation for child
    let params_hash = *blake3::hash(b"nft-params-1").as_bytes();
    let child_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &params_hash);

    // Verify VK derivation is deterministic
    let child_vk2 = ChildVkStrategy::derive_child_vk(&factory_vk, &params_hash);
    if child_vk != child_vk2 {
        return Err("VK derivation should be deterministic".into());
    }

    // Verify different params produce different VKs
    let other_params = *blake3::hash(b"nft-params-2").as_bytes();
    let other_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &other_params);
    if child_vk == other_vk {
        return Err("different params should produce different VKs".into());
    }

    // Record creation in registry
    registry
        .record_creation(&factory_vk)
        .map_err(|e| format!("{e:?}"))?;

    Ok(())
}

fn check_sovereign_peer_exchange() -> Result<(), String> {
    // Sovereign cells exchange state commitments.
    // We simulate: cell A registers as sovereign, stores commitment, retrieves it.
    let mut ledger = Ledger::new();

    let cell_a_key = test_key("sovereign-a");
    let token_id = test_key("sovereign-token");
    let cell_a_id = CellId::derive_raw(&cell_a_key, &token_id);

    // Register as sovereign cell with a commitment
    let state_commitment = *blake3::hash(b"cell-a-state-v1").as_bytes();
    ledger
        .register_sovereign_cell(cell_a_id, state_commitment)
        .map_err(|e| format!("{e:?}"))?;

    // Verify commitment is retrievable
    let stored = ledger
        .get_sovereign_commitment(&cell_a_id)
        .ok_or("no sovereign commitment for cell A")?;
    if *stored != state_commitment {
        return Err("commitment mismatch in sovereign store".into());
    }

    // Verify cell is recognized as sovereign
    if !ledger.is_sovereign(&cell_a_id) {
        return Err("cell A should be sovereign".into());
    }

    // Update commitment (simulates peer exchange after state transition)
    let new_commitment = *blake3::hash(b"cell-a-state-v2").as_bytes();
    ledger
        .update_sovereign_commitment(&cell_a_id, new_commitment)
        .map_err(|e| format!("{e:?}"))?;

    let updated = ledger
        .get_sovereign_commitment(&cell_a_id)
        .ok_or("commitment lost after update")?;
    if *updated != new_commitment {
        return Err("commitment should be updated".into());
    }

    Ok(())
}

fn check_multi_party_atomic() -> Result<(), String> {
    // Multi-party atomic: 2 cells swap value atomically.
    // Both transfers must succeed or both must fail (conservation).
    let token_id = test_key("atomic-token");
    let mut ledger = Ledger::new();

    let alice_key = test_key("atomic-alice");
    let mut alice = Cell::with_balance(alice_key, token_id, 50_000);
    alice.permissions = open_permissions();
    let alice_id = alice.id();
    ledger.insert_cell(alice).map_err(|e| format!("{e:?}"))?;

    let bob_key = test_key("atomic-bob");
    let mut bob = Cell::with_balance(bob_key, token_id, 50_000);
    bob.permissions = open_permissions();
    let bob_id = bob.id();
    ledger.insert_cell(bob).map_err(|e| format!("{e:?}"))?;

    // Grant mutual capabilities
    {
        let a = ledger.get_mut(&alice_id).unwrap();
        a.capabilities.grant(bob_id, AuthRequired::None);
    }
    {
        let b = ledger.get_mut(&bob_id).unwrap();
        b.capabilities.grant(alice_id, AuthRequired::None);
    }

    // Use zero costs so fee doesn't interfere with the test logic.
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Atomic turn: alice sends 100 to bob
    let mut tb = TurnBuilder::new(alice_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(bob_id, "atomic-swap", alice_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 100,
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();

    let total_before = {
        let a = ledger.get(&alice_id).unwrap();
        let b = ledger.get(&bob_id).unwrap();
        a.state.balance() + b.state.balance()
    };

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("atomic turn rejected: {reason}"));
        }
        _ => return Err("unexpected result".into()),
    }

    // Verify conservation: total value minus fee is preserved.
    // Fee is deducted from alice's balance in Phase 1 (never rolled back).
    let total_after = {
        let a = ledger.get(&alice_id).unwrap();
        let b = ledger.get(&bob_id).unwrap();
        a.state.balance() + b.state.balance()
    };

    let fee = 1000u64;
    if total_after != total_before - fee {
        return Err(format!(
            "conservation violated: before={total_before}, after={total_after}, fee={fee}"
        ));
    }

    Ok(())
}

fn check_ivc_history_compression() -> Result<(), String> {
    // IVC: compress N turn state transitions into a single proof.
    let initial_root = BabyBear::new(77777);
    let n_turns = 5u32;

    let deltas: Vec<FoldDelta> = (0..n_turns)
        .map(|i| {
            let fold = FoldWitness {
                old_root: BabyBear::new(77777 + i),
                new_root: BabyBear::new(77777 + i + 1),
                removed_facts: vec![],
                num_added_checks: 1,
                added_checks_commitment: compute_test_checks_commitment(1),
            };
            FoldDelta::new(fold)
        })
        .collect();

    let proof = prove_ivc(initial_root, deltas).ok_or("IVC history compression failed")?;

    if proof.step_count != n_turns {
        return Err(format!(
            "expected {} steps, got {}",
            n_turns, proof.step_count
        ));
    }

    // Single proof covers all N turns
    let verification = verify_ivc(&proof, Some(initial_root));
    match verification {
        IvcVerification::Valid => {}
        other => return Err(format!("IVC history verification failed: {:?}", other)),
    }

    // Final state root should be initial + n_turns
    let expected_final = BabyBear::new(77777 + n_turns);
    if proof.final_root != expected_final {
        return Err(format!(
            "expected final_root {:?}, got {:?}",
            expected_final, proof.final_root
        ));
    }

    Ok(())
}
