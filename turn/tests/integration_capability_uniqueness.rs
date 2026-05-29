//! Integration tests (AUDIT item 1 + item 3): executor-side enforcement of
//! `StateConstraint::CapabilityUniqueness` and the `BoundDelta` cross-cell
//! γ.2 reject-on-missing-peer path.
//!
//! The scalar `(old_state, new_state)` program evaluator cannot decide
//! structural capability uniqueness (it only sees the 8 state slots, not
//! the cell's `CapabilitySet`), so it fails closed. The real enforcement
//! lives in `TurnExecutor` (`execute_tree::validate_capability_uniqueness`),
//! which binds the declared cap-set-root slot to the cell's canonical
//! capability root and rejects duplicate capabilities.
//!
//! FAIL-before / PASS-after: before the fix the constraint was a no-op
//! (`Ok(())`), so a cell with a duplicate owner cap committed silently.

use dregg_cell::program::{CellProgram, StateConstraint};
use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, compute_canonical_capability_root,
    field_from_u64,
};
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

/// Happy path: a cell holding exactly one capability, whose cap-set-root
/// slot is bound to the canonical capability root, accepts a mutation.
#[test]
fn capability_uniqueness_single_cap_accepts() {
    let mut owner = make_open_cell(1, 1000);
    let target = make_open_cell(2, 0);
    let target_id = target.id();

    // Exactly one cap.
    owner
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    // Bind slot 0 to the canonical capability root.
    let root = compute_canonical_capability_root(&owner.capabilities);
    owner.state.fields[0] = root;
    owner.program = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 0,
    }]);
    let owner_id = owner.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(owner).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    // Mutate a non-root slot so the cap-root binding still holds.
    let turn = single_effect_turn(
        owner_id,
        owner_id,
        0,
        Effect::SetField {
            cell: owner_id,
            index: 1,
            value: field_from_u64(7),
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "single-cap + bound root must commit; got {result:?}"
    );
}

/// Adversarial: a cell holding TWO identical capabilities (same target,
/// permissions, breadstuff, facet) violates the "exactly one" guarantee
/// and must be rejected.
#[test]
fn capability_uniqueness_duplicate_cap_rejected() {
    let mut owner = make_open_cell(3, 1000);
    let target = make_open_cell(4, 0);
    let target_id = target.id();

    // Two caps with the SAME identity tuple (different slots).
    owner
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    owner
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    // Bind slot 0 to the (duplicate-containing) canonical root so the
    // root-binding check passes and we exercise the duplicate-detection
    // path specifically.
    let root = compute_canonical_capability_root(&owner.capabilities);
    owner.state.fields[0] = root;
    owner.program = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 0,
    }]);
    let owner_id = owner.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(owner).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        owner_id,
        owner_id,
        0,
        Effect::SetField {
            cell: owner_id,
            index: 1,
            value: field_from_u64(7),
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "duplicate capability must be rejected; got {result:?}"
    );
}

/// Adversarial: the declared cap-set-root slot does not match the cell's
/// actual canonical capability root → reject (a cell cannot claim a cap
/// commitment that does not reflect the caps it holds).
#[test]
fn capability_uniqueness_root_mismatch_rejected() {
    let mut owner = make_open_cell(5, 1000);
    let target = make_open_cell(6, 0);
    let target_id = target.id();

    owner
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    // Slot 0 carries a BOGUS root (not the canonical cap root).
    owner.state.fields[0] = [0xAB; 32];
    owner.program = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 0,
    }]);
    let owner_id = owner.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(owner).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        owner_id,
        owner_id,
        0,
        Effect::SetField {
            cell: owner_id,
            index: 1,
            value: field_from_u64(7),
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "cap-root-slot mismatch must be rejected; got {result:?}"
    );
}

/// Adversarial: a zero cap-set-root slot cannot commit to a unique cap →
/// reject (fail-closed sentinel; never silently pass).
#[test]
fn capability_uniqueness_zero_root_rejected() {
    let mut owner = make_open_cell(7, 1000);
    let target = make_open_cell(8, 0);
    let target_id = target.id();

    owner
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    // Slot 0 left at zero.
    owner.program = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 0,
    }]);
    let owner_id = owner.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(owner).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        owner_id,
        owner_id,
        0,
        Effect::SetField {
            cell: owner_id,
            index: 1,
            value: field_from_u64(7),
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "zero cap-set-root slot must be rejected; got {result:?}"
    );
}

/// Adversarial (item 3): a `BoundDelta` whose peer cell is NOT touched by
/// the action (no peer state in scope) must REJECT, not skip. This
/// confirms the executor's γ.2 cross-cell match loop fails closed when
/// peer state is absent.
#[test]
fn bound_delta_without_peer_state_rejected() {
    use dregg_cell::program::DeltaRelation;

    let mut local = make_open_cell(9, 1000);
    // Peer cell exists in the ledger but is never touched by the action.
    let peer = make_open_cell(10, 1000);
    let peer_id = peer.id();

    local.program = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: peer_id,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    let local_id = local.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(local).unwrap();
    ledger.insert_cell(peer).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    // Mutate ONLY the local cell. The peer is not touched, so the γ.2
    // match loop has no peer (old, new) pair → must reject.
    let turn = single_effect_turn(
        local_id,
        local_id,
        0,
        Effect::SetField {
            cell: local_id,
            index: 0,
            value: field_from_u64(7),
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "BoundDelta with untouched peer must be rejected; got {result:?}"
    );
}
