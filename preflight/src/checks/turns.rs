//! Turn execution checks: transfer, set_field, grant, multi-effect, nonce, conservation.

use pyana_cell::{AuthRequired, CapabilityRef, Cell, Ledger, Permissions};
use pyana_turn::builder::ActionBuilder;
use pyana_turn::{
    BudgetGate, BudgetSlice, ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor,
    TurnResult,
};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-turns:{name}").as_bytes()).as_bytes()
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
        run_check("transfer", check_transfer),
        run_check("setfield", check_set_field),
        run_check("grant", check_grant_capability),
        run_check("multi_effect", check_multi_effect),
        run_check("nonce", check_nonce_increments),
        run_check("conservation", check_conservation_law),
        run_check("budget_gate", check_budget_gate),
    ]
}

fn check_transfer() -> Result<(), String> {
    let token_id = test_key("token");
    let mut ledger = Ledger::new();

    let alice_key = test_key("alice");
    let mut alice = Cell::with_balance(alice_key, token_id, 10_000);
    alice.permissions = open_permissions();
    let alice_id = alice.id();
    ledger.insert_cell(alice).map_err(|e| format!("{e:?}"))?;

    let bob_key = test_key("bob");
    let mut bob = Cell::with_balance(bob_key, token_id, 0);
    bob.permissions = open_permissions();
    let bob_id = bob.id();
    ledger.insert_cell(bob).map_err(|e| format!("{e:?}"))?;

    // Grant alice capability to bob
    {
        let a = ledger.get_mut(&alice_id).unwrap();
        a.capabilities.grant(bob_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut tb = TurnBuilder::new(alice_id, 0);
    tb.set_fee(100);
    let action = ActionBuilder::new_unchecked_for_tests(bob_id, "transfer", alice_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 200,
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("transfer rejected: {reason}"));
        }
        _ => return Err("unexpected turn result".into()),
    }

    let bob_cell = ledger.get(&bob_id).ok_or("bob not found")?;
    if bob_cell.state.balance() != 200 {
        return Err(format!(
            "expected bob balance 200, got {}",
            bob_cell.state.balance()
        ));
    }

    Ok(())
}

fn check_set_field() -> Result<(), String> {
    let token_id = test_key("token-sf");
    let mut ledger = Ledger::new();

    let owner_key = test_key("owner-sf");
    let mut cell = Cell::with_balance(owner_key, token_id, 10000);
    cell.permissions = open_permissions();
    let cell_id = cell.id();
    ledger.insert_cell(cell).map_err(|e| format!("{e:?}"))?;

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut tb = TurnBuilder::new(cell_id, 0);
    tb.set_fee(100);
    let action = ActionBuilder::new_unchecked_for_tests(cell_id, "setfield", cell_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: cell_id,
            index: 3,
            value: *blake3::hash(b"my-data").as_bytes(),
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("setfield rejected: {reason}"));
        }
        _ => return Err("unexpected turn result".into()),
    }

    let updated = ledger.get(&cell_id).ok_or("cell not found")?;
    if updated.state.fields[3] != *blake3::hash(b"my-data").as_bytes() {
        return Err("field 3 not updated correctly".into());
    }

    Ok(())
}

fn check_grant_capability() -> Result<(), String> {
    let token_id = test_key("token-gc");
    let mut ledger = Ledger::new();

    let granter_key = test_key("granter");
    let mut granter = Cell::with_balance(granter_key, token_id, 10000);
    granter.permissions = open_permissions();
    let granter_id = granter.id();
    ledger.insert_cell(granter).map_err(|e| format!("{e:?}"))?;

    let target_key = test_key("target-gc");
    let mut target = Cell::with_balance(target_key, token_id, 0);
    target.permissions = open_permissions();
    let target_id = target.id();
    ledger.insert_cell(target).map_err(|e| format!("{e:?}"))?;

    // Bootstrap: granter must have existing cap to target in order to grant it.
    {
        let g = ledger.get_mut(&granter_id).unwrap();
        g.capabilities.grant(target_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut tb = TurnBuilder::new(granter_id, 0);
    tb.set_fee(100);
    // Action targets granter's own cell (granting a capability to itself).
    let action = ActionBuilder::new_unchecked_for_tests(granter_id, "grant", granter_id)
        .delegation(DelegationMode::None)
        .effect(Effect::GrantCapability {
            from: granter_id,
            to: granter_id,
            cap: CapabilityRef {
                target: target_id,
                slot: 0,
                permissions: AuthRequired::None,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
            },
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("grant rejected: {reason}"));
        }
        _ => return Err("unexpected turn result".into()),
    }

    // Verify capability is still in c-list after the grant turn.
    let g = ledger.get(&granter_id).ok_or("granter not found")?;
    if !g.capabilities.has_access(&target_id) {
        return Err("granter should have capability to target after grant".into());
    }

    Ok(())
}

fn check_multi_effect() -> Result<(), String> {
    let token_id = test_key("token-me");
    let mut ledger = Ledger::new();

    let owner_key = test_key("owner-me");
    let mut owner = Cell::with_balance(owner_key, token_id, 50000);
    owner.permissions = open_permissions();
    let owner_id = owner.id();
    ledger.insert_cell(owner).map_err(|e| format!("{e:?}"))?;

    let target_key = test_key("target-me");
    let mut target = Cell::with_balance(target_key, token_id, 0);
    target.permissions = open_permissions();
    let target_id = target.id();
    ledger.insert_cell(target).map_err(|e| format!("{e:?}"))?;

    // Grant owner cap to target
    {
        let o = ledger.get_mut(&owner_id).unwrap();
        o.capabilities.grant(target_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut tb = TurnBuilder::new(owner_id, 0);
    tb.set_fee(1000);
    // Multiple effects in one action
    let action = ActionBuilder::new_unchecked_for_tests(target_id, "multi", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: owner_id,
            to: target_id,
            amount: 100,
        })
        .effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"multi-effect-1").as_bytes(),
        })
        .effect(Effect::SetField {
            cell: target_id,
            index: 1,
            value: *blake3::hash(b"multi-effect-2").as_bytes(),
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("multi-effect rejected: {reason}"));
        }
        _ => return Err("unexpected turn result".into()),
    }

    let t = ledger.get(&target_id).ok_or("target not found")?;
    if t.state.balance() != 100 {
        return Err(format!(
            "expected target balance 100, got {}",
            t.state.balance()
        ));
    }
    if t.state.fields[0] != *blake3::hash(b"multi-effect-1").as_bytes() {
        return Err("field 0 not set".into());
    }
    if t.state.fields[1] != *blake3::hash(b"multi-effect-2").as_bytes() {
        return Err("field 1 not set".into());
    }

    Ok(())
}

fn check_nonce_increments() -> Result<(), String> {
    let token_id = test_key("token-nonce");
    let mut ledger = Ledger::new();

    let owner_key = test_key("owner-nonce");
    let mut owner = Cell::with_balance(owner_key, token_id, 50000);
    owner.permissions = open_permissions();
    let owner_id = owner.id();
    ledger.insert_cell(owner).map_err(|e| format!("{e:?}"))?;

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Execute turn with nonce=0
    let mut tb = TurnBuilder::new(owner_id, 0);
    tb.set_fee(100);
    let action = ActionBuilder::new_unchecked_for_tests(owner_id, "noop", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::IncrementNonce { cell: owner_id })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    if !matches!(result, TurnResult::Committed { .. }) {
        return Err("first turn should commit".into());
    }

    // Phase 1 increments nonce (always), then IncrementNonce effect adds another.
    // So final nonce = 0 + 1 (Phase 1) + 1 (effect) = 2.
    let after = ledger.get(&owner_id).ok_or("cell not found")?;
    if after.state.nonce() != 2 {
        return Err(format!(
            "expected nonce=2 after Phase1+effect increment, got {}",
            after.state.nonce()
        ));
    }

    Ok(())
}

fn check_conservation_law() -> Result<(), String> {
    let token_id = test_key("token-cons");
    let mut ledger = Ledger::new();

    let alice_key = test_key("alice-cons");
    let mut alice = Cell::with_balance(alice_key, token_id, 500);
    alice.permissions = open_permissions();
    let alice_id = alice.id();
    ledger.insert_cell(alice).map_err(|e| format!("{e:?}"))?;

    let bob_key = test_key("bob-cons");
    let mut bob = Cell::with_balance(bob_key, token_id, 0);
    bob.permissions = open_permissions();
    let bob_id = bob.id();
    ledger.insert_cell(bob).map_err(|e| format!("{e:?}"))?;

    {
        let a = ledger.get_mut(&alice_id).unwrap();
        a.capabilities.grant(bob_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // Attempt to transfer more than balance (should be rejected)
    let mut tb = TurnBuilder::new(alice_id, 0);
    tb.set_fee(100);
    let action = ActionBuilder::new_unchecked_for_tests(bob_id, "transfer", alice_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: alice_id,
            to: bob_id,
            amount: 100_000, // more than alice has
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Rejected { .. } => {
            // Good: conservation law enforced
        }
        TurnResult::Committed { .. } => {
            return Err(
                "transfer exceeding balance should be rejected (conservation law violated)".into(),
            );
        }
        _ => return Err("unexpected turn result".into()),
    }

    // Verify: fee was deducted (never rolled back) but transfer was NOT applied.
    // alice started with 500, fee=100 deducted in Phase 1, so alice has 400.
    // bob still has 0 (transfer was not executed).
    let a = ledger.get(&alice_id).ok_or("alice not found")?;
    let b = ledger.get(&bob_id).ok_or("bob not found")?;
    if a.state.balance() != 400 {
        return Err(format!(
            "alice should have 400 (500 - 100 fee), got {}",
            a.state.balance()
        ));
    }
    if b.state.balance() != 0 {
        return Err("bob should still have 0 after rejected transfer".into());
    }

    Ok(())
}

/// Verify the SharedResourceBudget (BudgetGate) path:
/// budget ceiling limits turn execution, exhaustion rejects.
fn check_budget_gate() -> Result<(), String> {
    let token_id = test_key("token-budget");
    let mut ledger = Ledger::new();

    let owner_key = test_key("owner-budget");
    let mut owner = Cell::with_balance(owner_key, token_id, 100_000);
    owner.permissions = open_permissions();
    let owner_id = owner.id();
    ledger.insert_cell(owner).map_err(|e| format!("{e:?}"))?;

    // Create a BudgetGate with a ceiling of 600.
    // Each turn with fee=300 costs ~222 computrons (action_base=100+effect_base=50+field_cost=72).
    // Fee of 300 covers the cost. Budget ceiling of 600 allows 2 turns but rejects the 3rd.
    let slice = BudgetSlice::new(600);
    let gate = BudgetGate::new(1, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::default_costs(), gate);

    // First turn with fee=300: should succeed (300 <= ceiling 600).
    // Phase 1 always increments nonce by 1, so after turn 1 nonce = 1.
    let mut tb1 = TurnBuilder::new(owner_id, 0);
    tb1.set_fee(300);
    let action = ActionBuilder::new_unchecked_for_tests(owner_id, "budget-test-1", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: owner_id,
            index: 0,
            value: *blake3::hash(b"budget-1").as_bytes(),
        })
        .build();
    tb1.add_action(action);
    let turn1 = tb1.build();
    let result1 = executor.execute(&turn1, &mut ledger);
    match result1 {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("first turn (fee=300) should commit: {reason}"));
        }
        _ => return Err("unexpected result for first turn".into()),
    }

    // After turn 1: nonce is 1, budget used: 300.
    // Second turn with fee=300: should succeed (600 total == ceiling).
    let mut tb2 = TurnBuilder::new(owner_id, 1);
    tb2.set_fee(300);
    let action = ActionBuilder::new_unchecked_for_tests(owner_id, "budget-test-2", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: owner_id,
            index: 1,
            value: *blake3::hash(b"budget-2").as_bytes(),
        })
        .build();
    tb2.add_action(action);
    let turn2 = tb2.build();
    let result2 = executor.execute(&turn2, &mut ledger);
    match result2 {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("second turn (fee=300) should commit: {reason}"));
        }
        _ => return Err("unexpected result for second turn".into()),
    }

    // After turn 2: nonce is 2, budget used: 600 (at ceiling).
    // Third turn with fee=300: should be REJECTED (900 > ceiling 600).
    let mut tb3 = TurnBuilder::new(owner_id, 2);
    tb3.set_fee(300);
    let action = ActionBuilder::new_unchecked_for_tests(owner_id, "budget-test-3", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: owner_id,
            index: 2,
            value: *blake3::hash(b"budget-3").as_bytes(),
        })
        .build();
    tb3.add_action(action);
    let turn3 = tb3.build();
    let result3 = executor.execute(&turn3, &mut ledger);
    match result3 {
        TurnResult::Rejected { .. } => {
            // Good: budget exhausted.
        }
        TurnResult::Committed { .. } => {
            return Err("third turn should be REJECTED (budget exhausted: 900 > 600)".into());
        }
        _ => return Err("unexpected result for third turn".into()),
    }

    Ok(())
}
