//! Integration test: audit P0 #79 —
//! `ArchivalAttestation.archive_terminal_receipt_hash` is now bound to
//! the live chain head. An attestation that lies about its terminal
//! hash must be rejected at apply.

use pyana_cell::lifecycle::ArchivalAttestation;
use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
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

fn single_effect_turn(
    agent: CellId,
    target: CellId,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
    effect: Effect,
) -> Turn {
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
        previous_receipt_hash,
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
fn archive_rejects_terminal_receipt_hash_mismatch() {
    let cell = make_open_cell(1, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(200);

    // Establish a live chain-head for this cell. The terminal hash in
    // the attestation must equal this exact value or the archive is
    // rejected.
    let real_head = [0x77; 32];
    executor.set_last_receipt_hash(cell_id, real_head);

    // Attestation lies: it claims a different terminal hash.
    let lying_attestation = ArchivalAttestation {
        cell_id,
        archive_start_height: 0,
        archive_end_height: 100,
        archive_blob_hash: [0xAB; 32],
        archive_terminal_commitment: [0xCD; 32],
        archive_terminal_receipt_hash: [0xEF; 32], // wrong!
    };

    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Some(real_head),
        Effect::ReceiptArchive {
            prefix_end_height: 100,
            checkpoint: lying_attestation,
        },
    );

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "ReceiptArchive with mismatched archive_terminal_receipt_hash must reject; got {result:?}"
    );
}

#[test]
fn archive_accepts_matching_terminal_receipt_hash() {
    let cell = make_open_cell(2, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_block_height(200);

    let real_head = [0x42; 32];
    executor.set_last_receipt_hash(cell_id, real_head);

    let honest_attestation = ArchivalAttestation {
        cell_id,
        archive_start_height: 0,
        archive_end_height: 100,
        archive_blob_hash: [0xAB; 32],
        archive_terminal_commitment: [0xCD; 32],
        archive_terminal_receipt_hash: real_head,
    };

    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Some(real_head),
        Effect::ReceiptArchive {
            prefix_end_height: 100,
            checkpoint: honest_attestation,
        },
    );

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "ReceiptArchive with matching archive_terminal_receipt_hash must commit; got {result:?}"
    );
}
