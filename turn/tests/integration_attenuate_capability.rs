//! Integration tests: Effect::AttenuateCapability through the executor.
//!
//! Exercises:
//! - Broad cap attenuated to narrow: actor can exercise narrow but
//!   an action requiring broad is rejected.
//! - Widening an existing cap is rejected (monotone narrowing only).
//! - Attenuation of a non-existent slot is rejected.
//! - Chained attenuation: repeated narrowing is monotone and each step accepted.
//! - Attenuating a cap held by a *different* actor is rejected.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn zero_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// Test 1 (happy path): Either → Signature attenuation is accepted.
// The post-attenuation cap has Signature permissions in the actor's c-list.
// ---------------------------------------------------------------------------

#[test]
fn attenuate_from_either_to_signature_accepted() {
    let actor = make_open_cell(1, 1000);
    let target = make_open_cell(2, 0);
    let actor_id = actor.id();
    let target_id = target.id();

    let mut actor_with_cap = actor;
    let slot = actor_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();
    let turn = single_effect_turn(
        actor_id,
        actor_id,
        0,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "attenuation Either→Signature must commit; got {result:?}"
    );

    // Post-state: cap permissions are now Signature, not Either.
    let cap = ledger
        .get(&actor_id)
        .unwrap()
        .capabilities
        .lookup(slot)
        .expect("slot must still exist");
    assert_eq!(
        cap.permissions,
        AuthRequired::Signature,
        "cap permissions must be Signature after attenuation"
    );
}

// ---------------------------------------------------------------------------
// Test 2 (adversarial): Widening Signature → Either is rejected.
// ---------------------------------------------------------------------------

#[test]
fn attenuate_widening_rejected() {
    let actor = make_open_cell(3, 1000);
    let target = make_open_cell(4, 0);
    let actor_id = actor.id();
    let target_id = target.id();

    let mut actor_with_cap = actor;
    let slot = actor_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Signature)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();
    // Trying to widen Signature → Either (not a narrowing).
    let turn = single_effect_turn(
        actor_id,
        actor_id,
        0,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot,
            narrower_permissions: AuthRequired::Either,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "widening attenuation must be rejected; got {result:?}"
    );

    // Cap permissions unchanged.
    let cap = ledger
        .get(&actor_id)
        .unwrap()
        .capabilities
        .lookup(slot)
        .unwrap();
    assert_eq!(
        cap.permissions,
        AuthRequired::Signature,
        "cap permissions must be unchanged"
    );
}

// ---------------------------------------------------------------------------
// Test 3 (adversarial): Attenuation of non-existent slot is rejected.
// ---------------------------------------------------------------------------

#[test]
fn attenuate_nonexistent_slot_rejected() {
    let actor = make_open_cell(5, 500);
    let actor_id = actor.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor).unwrap();

    let executor = zero_executor();
    // Slot 99 doesn't exist.
    let turn = single_effect_turn(
        actor_id,
        actor_id,
        0,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot: 99,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "attenuating nonexistent slot must be rejected; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Test 4 (adversarial): Attenuating a cap held by a *different* actor is rejected.
//
// The AttenuateCapability executor check requires cell == actor.
// ---------------------------------------------------------------------------

#[test]
fn attenuate_other_actors_cap_rejected() {
    let actor = make_open_cell(6, 1000);
    let other = make_open_cell(7, 0);
    let target = make_open_cell(8, 0);
    let actor_id = actor.id();
    let other_id = other.id();
    let target_id = target.id();

    // Give ACTOR a cap to OTHER, and OTHER a cap to TARGET.
    let mut actor_with_cap = actor;
    actor_with_cap
        .capabilities
        .grant(other_id, AuthRequired::None);

    let mut other_with_cap = other;
    let slot_in_other = other_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(actor_with_cap).unwrap();
    ledger.insert_cell(other_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();
    // Actor submits a turn targeting OTHER's slot — must be rejected
    // because AttenuateCapability requires cell == actor (the executor's
    // "cell must match the actor" guard).
    let mut forest = CallForest::new();
    let action = Action {
        target: other_id, // action targets OTHER
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::AttenuateCapability {
            cell: other_id, // trying to narrow OTHER's slot
            slot: slot_in_other,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    let turn = Turn {
        agent: actor_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "attenuating another actor's cap must be rejected; got {result:?}"
    );

    // OTHER's cap is unchanged.
    let cap = ledger
        .get(&other_id)
        .unwrap()
        .capabilities
        .lookup(slot_in_other)
        .unwrap();
    assert_eq!(
        cap.permissions,
        AuthRequired::Either,
        "OTHER's cap must be unchanged"
    );
}

// ---------------------------------------------------------------------------
// Test 5 (happy path): Chained attenuation — Either → Signature → Impossible.
// Each step is a monotone narrowing and accepted.
// ---------------------------------------------------------------------------

#[test]
fn attenuate_chained_narrowing_accepted() {
    let actor = make_open_cell(9, 1000);
    let target = make_open_cell(10, 0);
    let actor_id = actor.id();
    let target_id = target.id();

    let mut actor_with_cap = actor;
    let slot = actor_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_executor();

    // Step 1: Either → Signature.
    let t1 = single_effect_turn(
        actor_id,
        actor_id,
        0,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    let r1 = executor.execute(&t1, &mut ledger);
    let prev_receipt_hash = match r1 {
        dregg_turn::TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("first narrowing must commit, got {other:?}"),
    };

    let cap = ledger
        .get(&actor_id)
        .unwrap()
        .capabilities
        .lookup(slot)
        .unwrap();
    assert_eq!(cap.permissions, AuthRequired::Signature);

    // Step 2: Signature → Impossible.
    let mut t2 = single_effect_turn(
        actor_id,
        actor_id,
        1,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot,
            narrower_permissions: AuthRequired::Impossible,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    t2.previous_receipt_hash = Some(prev_receipt_hash);
    assert!(
        executor.execute(&t2, &mut ledger).is_committed(),
        "second narrowing must commit"
    );

    let cap = ledger
        .get(&actor_id)
        .unwrap()
        .capabilities
        .lookup(slot)
        .unwrap();
    assert_eq!(
        cap.permissions,
        AuthRequired::Impossible,
        "cap must be Impossible after chained narrowing"
    );
}
