//! Integration test: Proof-carrying sovereign turns (Phase 2).
//!
//! Tests the full pipeline:
//!   1. Cipherclerk generates a STARK proof of valid state transition
//!   2. Turn carries the proof (no sovereign_witnesses needed)
//!   3. Executor verifies the proof and updates commitment (no re-execution)

use pyana_cell::{Cell, CellId, CellMode, Ledger};
use pyana_circuit::CellState as VmCellState;
use pyana_sdk::AgentCipherclerk;
use pyana_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

/// Create a sovereign cell in a ledger and return the cell + ledger.
///
/// The executor requires the agent cell (= sovereign cell) to exist in the hosted
/// table for nonce/fee checks. For proof-carrying turns, the cell is registered as
/// both sovereign (commitment) AND hosted (balance/nonce). The proof replaces
/// re-execution, but the executor still needs balance/nonce for basic validation.
fn setup_sovereign_cell(balance: u64) -> (AgentCipherclerk, CellId, Ledger) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"test-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, balance);
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    // Compute the initial state commitment using the Effect VM's Poseidon2 scheme.
    // The executor converts stored commitments to BabyBear for proof verification,
    // so we must store the Poseidon2-based commitment (not blake3).
    let vm_state = VmCellState::new(balance, cell.state.nonce() as u32);
    let commitment = TurnExecutor::babybear_to_commitment(vm_state.state_commitment);

    // Store the cell state in the cclerk.
    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    // Create a ledger with both:
    // 1. Sovereign commitment registration (for proof verification)
    // 2. Hosted cell entry (for nonce/fee checks by executor)
    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    (cclerk, cell_id, ledger)
}

#[test]
fn test_proof_carrying_sovereign_turn_accepted() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    // Create a destination cell for the transfer.
    let dest_key = [42u8; 32];
    let dest_token_id = *blake3::hash(b"test-domain").as_bytes();
    let dest_cell = Cell::with_balance(dest_key, dest_token_id, 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    // Generate a proof-carrying turn: transfer 100 from our sovereign cell.
    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];

    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("should generate proof-carrying turn");

    // Verify the turn has an execution_proof.
    assert!(turn.execution_proof.is_some());
    assert_eq!(turn.execution_proof_cell, Some(cell_id));
    assert!(turn.execution_proof_new_commitment.is_some());
    assert!(turn.sovereign_witnesses.is_empty());

    // Execute with the TurnExecutor.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    match result {
        TurnResult::Committed {
            computrons_used, ..
        } => {
            // Proof-carrying turns use zero computrons (just verification).
            assert_eq!(computrons_used, 0);
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Turn was rejected: {:?}", reason);
        }
        other => panic!("Unexpected result: {:?}", other),
    }

    // Verify the sovereign commitment was updated.
    let new_commitment = ledger.get_sovereign_commitment(&cell_id);
    assert!(new_commitment.is_some());
    assert_eq!(
        *new_commitment.unwrap(),
        turn.execution_proof_new_commitment.unwrap()
    );
}

#[test]
fn test_proof_carrying_turn_tampered_commitment_rejected() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_key = [43u8; 32];
    let dest_token_id = *blake3::hash(b"test-domain").as_bytes();
    let dest_cell = Cell::with_balance(dest_key, dest_token_id, 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 50,
    }];

    let mut turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("should generate proof-carrying turn");

    // Tamper with the new commitment (simulates attacker trying to claim wrong state).
    turn.execution_proof_new_commitment = Some([0xFFu8; 32]);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    // Should be rejected because the proof's public inputs won't match the tampered commitment.
    match result {
        TurnResult::Rejected { reason, .. } => {
            // Expected: the proof verification should fail because the public inputs
            // don't match what's embedded in the STARK proof.
            let reason_str = format!("{:?}", reason);
            assert!(
                reason_str.contains("new_commitment")
                    || reason_str.contains("ProofVerificationFailed")
                    || reason_str.contains("mismatch"),
                "Expected commitment mismatch error, got: {}",
                reason_str
            );
        }
        TurnResult::Committed { .. } => {
            panic!("Tampered turn should have been rejected!");
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

#[test]
fn test_backward_compat_witness_path_still_works() {
    // Verify that turns WITHOUT execution_proof still work (Phase 1 witness path).
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"test-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, 5000);
    cell.mode = CellMode::Sovereign;
    // Set permissive send permission — this test verifies the witness injection
    // mechanism, not authorization. Default permissions require Signature which
    // would need a separate authorization test path.
    cell.permissions.send = pyana_cell::AuthRequired::None;
    let cell_id = cell.id();
    let commitment = cell.state_commitment();

    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    // Insert the sovereign cell into the hosted table too (executor needs it for
    // nonce/fee lookup since turn.agent == cell_id). The witness injection will
    // replace it with the witnessed state.
    let _ = ledger.insert_cell(cell.clone());

    let dest_key = [44u8; 32];
    let dest_token_id = *blake3::hash(b"test-domain").as_bytes();
    let dest_cell = Cell::with_balance(dest_key, dest_token_id, 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    // Use the Phase 1 witness path (no proof, sovereign_witnesses populated).
    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 200,
    }];

    let turn = cclerk
        .execute_sovereign_turn(&cell_id, effects, 500)
        .expect("should build witness-based turn");

    // Verify it has witnesses but NO execution proof.
    assert!(turn.execution_proof.is_none());
    assert!(!turn.sovereign_witnesses.is_empty());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);

    match result {
        TurnResult::Committed { .. } => {
            // Phase 1 path still works.
        }
        TurnResult::Rejected { reason, .. } => {
            panic!("Witness-based turn should succeed: {:?}", reason);
        }
        other => panic!("Unexpected: {:?}", other),
    }
}
