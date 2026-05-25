//! Integration tests: Effect::Burn and receipt.was_burn binding.
//!
//! Exercises:
//! - Burn reduces balance and sets receipt.was_burn = true.
//! - receipt_hash changes when was_burn differs (bit is genuinely bound).
//! - Burn exceeding balance is rejected, balance preserved.
//! - Non-zero slot is rejected (only slot 0 supported in Silver-Vision).
//! - receipt.was_burn is false for a plain transfer (control case).

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnResult, TurnReceipt},
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

fn unwrap_receipt(result: TurnResult) -> TurnReceipt {
    match result {
        TurnResult::Committed { receipt, .. } => receipt,
        other => panic!("expected Committed, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 1 (happy path): Burn reduces balance and sets was_burn = true.
// ---------------------------------------------------------------------------

#[test]
fn burn_reduces_balance_and_sets_was_burn_flag() {
    let cell = make_open_cell(1, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let burn_amount = 300u64;
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::Burn { target: cell_id, slot: 0, amount: burn_amount },
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    // Balance reduced by exactly burn_amount.
    assert_eq!(
        ledger.get(&cell_id).unwrap().state.balance(),
        1000 - burn_amount,
        "balance must be reduced by burn_amount"
    );

    // was_burn must be set.
    assert!(receipt.was_burn, "receipt.was_burn must be true when Effect::Burn was applied");
}

// ---------------------------------------------------------------------------
// Test 2: receipt_hash binds was_burn — flipping it changes the hash.
// ---------------------------------------------------------------------------

#[test]
fn receipt_hash_binds_was_burn_flag() {
    // Construct two receipts that are identical except for was_burn.
    let mut r_no_burn = TurnReceipt::default();
    r_no_burn.was_burn = false;
    let mut r_with_burn = r_no_burn.clone();
    r_with_burn.was_burn = true;

    let hash_no_burn = r_no_burn.receipt_hash();
    let hash_with_burn = r_with_burn.receipt_hash();

    assert_ne!(
        hash_no_burn, hash_with_burn,
        "receipt_hash must differ when was_burn differs — the flag must be bound"
    );
}

// ---------------------------------------------------------------------------
// Test 3 (adversarial): Burn exceeding balance is rejected; balance preserved.
// ---------------------------------------------------------------------------

#[test]
fn burn_exceeding_balance_rejected_balance_preserved() {
    let balance = 100u64;
    let cell = make_open_cell(2, balance);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::Burn { target: cell_id, slot: 0, amount: balance + 1 },
    );
    let result = executor.execute(&turn, &mut ledger);

    assert!(result.is_rejected(), "burn > balance must be rejected; got {result:?}");
    // Balance unchanged.
    assert_eq!(
        ledger.get(&cell_id).unwrap().state.balance(),
        balance,
        "balance must be preserved on rejection"
    );
}

// ---------------------------------------------------------------------------
// Test 4 (adversarial): Burn with non-zero slot rejected.
// ---------------------------------------------------------------------------

#[test]
fn burn_non_zero_slot_rejected() {
    let cell = make_open_cell(3, 500);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    // slot = 1 is not supported in Silver-Vision.
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::Burn { target: cell_id, slot: 1, amount: 50 },
    );
    let result = executor.execute(&turn, &mut ledger);

    assert!(result.is_rejected(), "Burn with slot != 0 must be rejected; got {result:?}");
    // Balance unchanged.
    assert_eq!(ledger.get(&cell_id).unwrap().state.balance(), 500);
}

// ---------------------------------------------------------------------------
// Test 5 (control): A plain Transfer does NOT set was_burn.
// ---------------------------------------------------------------------------

#[test]
fn plain_transfer_does_not_set_was_burn() {
    let sender = make_open_cell(4, 1000);
    let receiver = make_open_cell(5, 0);
    let sender_id = sender.id();
    let receiver_id = receiver.id();
    let mut ledger = Ledger::new();
    // Give sender capability to reach receiver.
    let mut sender_with_cap = sender;
    sender_with_cap
        .capabilities
        .grant(receiver_id, AuthRequired::None);
    ledger.insert_cell(sender_with_cap).unwrap();
    ledger.insert_cell(receiver).unwrap();

    let executor = zero_executor();
    let turn = single_effect_turn(
        sender_id,
        sender_id,
        0,
        Effect::Transfer { from: sender_id, to: receiver_id, amount: 100 },
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    assert!(!receipt.was_burn, "was_burn must be false for a plain Transfer");
    assert_eq!(ledger.get(&sender_id).unwrap().state.balance(), 900);
    assert_eq!(ledger.get(&receiver_id).unwrap().state.balance(), 100);
}

// ---------------------------------------------------------------------------
// Test 6 (adversarial): Burn entire balance leaves cell at zero, was_burn = true.
// ---------------------------------------------------------------------------

#[test]
fn burn_entire_balance_leaves_zero() {
    let balance = 777u64;
    let cell = make_open_cell(6, balance);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let turn = single_effect_turn(
        cell_id,
        cell_id,
        0,
        Effect::Burn { target: cell_id, slot: 0, amount: balance },
    );
    let receipt = unwrap_receipt(executor.execute(&turn, &mut ledger));

    assert_eq!(ledger.get(&cell_id).unwrap().state.balance(), 0, "balance must be zero after full burn");
    assert!(receipt.was_burn);
}
