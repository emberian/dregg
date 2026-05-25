//! Integration test: audit P0 #69 — `Effect::SetVerificationKey` apply
//! rejects a `VerificationKey` whose declared `hash` does not match
//! `blake3(data)`.
//!
//! Construction: build a turn that sets a fake `VerificationKey` with
//! a hash deliberately wrong for the data. The executor must reject
//! the apply with `InvalidEffect`.

use pyana_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, VerificationKey, VerificationKeyIntegrityError,
};
use pyana_turn::{
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

#[test]
fn set_verification_key_rejects_hash_data_mismatch() {
    let cell = make_open_cell(1, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    // Construct a forged VK: hash claims to be one thing, data is another.
    let forged_vk = VerificationKey::from_parts([0xAA; 32], b"unrelated-vk-data".to_vec());
    assert_ne!(forged_vk.hash, *blake3::hash(&forged_vk.data).as_bytes());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(forged_vk),
        },
    );

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "SetVerificationKey with forged hash must NOT commit; got {result:?}"
    );
    // The cell's verification_key field must still be `None` (no mutation
    // leaked through the rejected apply).
    assert!(ledger.get(&cell_id).unwrap().verification_key.is_none());
}

#[test]
fn set_verification_key_accepts_consistent_hash() {
    let cell = make_open_cell(2, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    // Honest VK: hash IS blake3(data).
    let honest_vk = VerificationKey::new(b"honest-vk-data".to_vec());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(honest_vk.clone()),
        },
    );

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "SetVerificationKey with valid hash must commit; got {result:?}"
    );
    assert_eq!(
        ledger.get(&cell_id).unwrap().verification_key.as_ref(),
        Some(&honest_vk)
    );
}

#[test]
fn from_parts_checked_rejects_mismatch_and_accepts_match() {
    // Direct invariant on the constructor: documents the audit P0 #69
    // remedy at the type level.
    let data = b"some-vk-data".to_vec();
    let good_hash = *blake3::hash(&data).as_bytes();
    let bad_hash = [0u8; 32];

    let ok = VerificationKey::from_parts_checked(good_hash, data.clone()).unwrap();
    assert_eq!(ok.hash, good_hash);

    let err = VerificationKey::from_parts_checked(bad_hash, data).unwrap_err();
    let VerificationKeyIntegrityError { expected, got } = err;
    assert_eq!(expected, good_hash);
    assert_eq!(got, bad_hash);
}
