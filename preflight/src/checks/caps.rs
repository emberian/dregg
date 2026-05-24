//! Capability model checks: c-list, bearer, facet, revocation.

use pyana_cell::{
    AuthRequired, CapabilitySet, Cell, CellId, Ledger, Permissions,
    facet::{
        EFFECT_ALL, EFFECT_SET_FIELD, EFFECT_TRANSFER, FacetBuilder, is_effect_permitted,
        is_facet_attenuation,
    },
};
use pyana_turn::builder::ActionBuilder;
use pyana_turn::{ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult};

use crate::report::{CheckResult, run_check};

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("preflight-caps:{name}").as_bytes()).as_bytes()
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
        run_check("clist", check_clist_grant_exercise),
        run_check("bearer", check_bearer_cap),
        run_check("bearer_exercise", check_bearer_cap_through_executor),
        run_check("facet", check_faceted_cap),
        run_check("revocation", check_revocation),
        run_check("unauthorized", check_unauthorized_rejected),
    ]
}

fn check_clist_grant_exercise() -> Result<(), String> {
    let token_id = test_key("token-clist");
    let mut ledger = Ledger::new();

    let owner_key = test_key("owner-clist");
    let mut owner = Cell::with_balance(owner_key, token_id, 50000);
    owner.permissions = open_permissions();
    let owner_id = owner.id();
    ledger.insert_cell(owner).map_err(|e| format!("{e:?}"))?;

    let target_key = test_key("target-clist");
    let mut target = Cell::with_balance(target_key, token_id, 0);
    target.permissions = open_permissions();
    let target_id = target.id();
    ledger.insert_cell(target).map_err(|e| format!("{e:?}"))?;

    // Grant capability via c-list
    {
        let o = ledger.get_mut(&owner_id).unwrap();
        o.capabilities.grant(target_id, AuthRequired::None);
    }

    // Exercise: set field on target
    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut tb = TurnBuilder::new(owner_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(target_id, "write", owner_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: target_id,
            index: 0,
            value: *blake3::hash(b"clist-exercise").as_bytes(),
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("c-list exercise rejected: {reason}"));
        }
        _ => return Err("unexpected result".into()),
    }

    let t = ledger.get(&target_id).ok_or("target not found")?;
    if t.state.fields[0] != *blake3::hash(b"clist-exercise").as_bytes() {
        return Err("field not set by c-list exercise".into());
    }

    Ok(())
}

fn check_bearer_cap() -> Result<(), String> {
    // Bearer capabilities are exercised immediately without c-list storage.
    // Verify the capability model: creating a cap ref and checking access.
    let target_id = CellId::derive_raw(&test_key("bearer-target"), &test_key("bearer-token"));

    let mut cap_set = CapabilitySet::new();

    // No access initially
    if cap_set.has_access(&target_id) {
        return Err("should not have access before grant".into());
    }

    // Grant bearer-style (no auth required)
    cap_set.grant(target_id, AuthRequired::None);
    if !cap_set.has_access(&target_id) {
        return Err("should have access after bearer grant".into());
    }

    Ok(())
}

fn check_faceted_cap() -> Result<(), String> {
    // Build a faceted capability that only allows SetField (not Transfer)
    let mask = FacetBuilder::new().allow_set_field().build();

    // SetField should be permitted
    if !is_effect_permitted(Some(mask), EFFECT_SET_FIELD) {
        return Err("SetField should be permitted by facet".into());
    }

    // Transfer should NOT be permitted
    if is_effect_permitted(Some(mask), EFFECT_TRANSFER) {
        return Err("Transfer should NOT be permitted by SetField-only facet".into());
    }

    // Verify facet attenuation: narrowing from ALL to subset is valid
    let narrow_mask = FacetBuilder::new()
        .allow_set_field()
        .allow_transfer()
        .build();
    if !is_facet_attenuation(EFFECT_ALL, narrow_mask) {
        return Err("narrowing from ALL should be valid attenuation".into());
    }

    // Verify widening is NOT a valid attenuation
    if is_facet_attenuation(mask, EFFECT_ALL) {
        return Err("widening from subset to ALL should NOT be valid attenuation".into());
    }

    Ok(())
}

fn check_revocation() -> Result<(), String> {
    let token_id = test_key("token-rev");
    let mut ledger = Ledger::new();

    let granter_key = test_key("granter-rev");
    let mut granter = Cell::with_balance(granter_key, token_id, 50000);
    granter.permissions = open_permissions();
    let granter_id = granter.id();
    ledger.insert_cell(granter).map_err(|e| format!("{e:?}"))?;

    let target_key = test_key("target-rev");
    let mut target = Cell::with_balance(target_key, token_id, 0);
    target.permissions = open_permissions();
    let target_id = target.id();
    ledger.insert_cell(target).map_err(|e| format!("{e:?}"))?;

    // Grant capability
    {
        let g = ledger.get_mut(&granter_id).unwrap();
        g.capabilities.grant(target_id, AuthRequired::None);
    }

    // Verify access
    {
        let g = ledger.get(&granter_id).unwrap();
        if !g.capabilities.has_access(&target_id) {
            return Err("should have access after grant".into());
        }
    }

    // Revoke capability
    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut tb = TurnBuilder::new(granter_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(granter_id, "revoke", granter_id)
        .delegation(DelegationMode::None)
        .effect(Effect::RevokeCapability {
            cell: granter_id,
            slot: 0,
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("revocation rejected: {reason}"));
        }
        _ => return Err("unexpected result".into()),
    }

    // Verify access revoked
    let g = ledger.get(&granter_id).ok_or("granter not found")?;
    if g.capabilities.has_access(&target_id) {
        return Err("should NOT have access after revocation".into());
    }

    Ok(())
}

/// Exercise a bearer capability through the ACTUAL executor (not just CapabilitySet API).
fn check_bearer_cap_through_executor() -> Result<(), String> {
    let token_id = test_key("token-bearer-exec");
    let mut ledger = Ledger::new();

    let sender_key = test_key("sender-bearer");
    let mut sender = Cell::with_balance(sender_key, token_id, 50000);
    sender.permissions = open_permissions();
    let sender_id = sender.id();
    ledger.insert_cell(sender).map_err(|e| format!("{e:?}"))?;

    let target_key = test_key("target-bearer");
    let mut target = Cell::with_balance(target_key, token_id, 0);
    target.permissions = open_permissions();
    let target_id = target.id();
    ledger.insert_cell(target).map_err(|e| format!("{e:?}"))?;

    // Grant sender bearer-style capability to target with specific permissions.
    {
        let s = ledger.get_mut(&sender_id).unwrap();
        s.capabilities.grant(target_id, AuthRequired::None);
    }

    // Exercise the bearer cap: transfer through the executor.
    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut tb = TurnBuilder::new(sender_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(target_id, "bearer-transfer", sender_id)
        .delegation(DelegationMode::None)
        .effect(Effect::Transfer {
            from: sender_id,
            to: target_id,
            amount: 500,
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Committed { .. } => {}
        TurnResult::Rejected { reason, .. } => {
            return Err(format!("bearer cap exercise rejected: {reason}"));
        }
        _ => return Err("unexpected result".into()),
    }

    let t = ledger.get(&target_id).ok_or("target not found")?;
    if t.state.balance() != 500 {
        return Err(format!(
            "target should have 500 after bearer transfer, got {}",
            t.state.balance()
        ));
    }

    Ok(())
}

/// Adversarial: a cell WITHOUT capability should be REJECTED when trying to act on another cell.
fn check_unauthorized_rejected() -> Result<(), String> {
    let token_id = test_key("token-unauth");
    let mut ledger = Ledger::new();

    let attacker_key = test_key("attacker");
    let mut attacker = Cell::with_balance(attacker_key, token_id, 50000);
    attacker.permissions = open_permissions();
    let attacker_id = attacker.id();
    ledger.insert_cell(attacker).map_err(|e| format!("{e:?}"))?;

    let victim_key = test_key("victim");
    let mut victim = Cell::with_balance(victim_key, token_id, 10000);
    victim.permissions = open_permissions();
    let victim_id = victim.id();
    ledger.insert_cell(victim).map_err(|e| format!("{e:?}"))?;

    // Attacker does NOT have a capability to victim.
    // Attempt to set field on victim should be REJECTED.
    let executor = TurnExecutor::new(ComputronCosts::default_costs());
    let mut tb = TurnBuilder::new(attacker_id, 0);
    tb.set_fee(1000);
    let action = ActionBuilder::new_unchecked_for_tests(victim_id, "steal", attacker_id)
        .delegation(DelegationMode::None)
        .effect(Effect::SetField {
            cell: victim_id,
            index: 0,
            value: *blake3::hash(b"hacked").as_bytes(),
        })
        .build();
    tb.add_action(action);
    let turn = tb.build();
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Rejected { .. } => {
            // Good: unauthorized access rejected.
        }
        TurnResult::Committed { .. } => {
            return Err(
                "SECURITY: attacker without capability should be REJECTED, but was committed"
                    .into(),
            );
        }
        _ => return Err("unexpected result".into()),
    }

    // Verify victim's state is unchanged.
    let v = ledger.get(&victim_id).ok_or("victim not found")?;
    if v.state.fields[0] != [0u8; 32] {
        return Err("victim field should be unchanged after rejected attack".into());
    }

    Ok(())
}
