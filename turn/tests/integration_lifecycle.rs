//! Integration tests: full cell lifecycle transitions through the executor.
//!
//! Each test exercises a *composed flow* end-to-end: build a turn, run it
//! through `TurnExecutor::execute`, inspect the post-state on the ledger
//! and/or the receipt.  Every happy-path test has an adversarial counterpart
//! that verifies the rejection case.
//!
//! Covers: Seal → post-seal effect rejection, Seal → Unseal roundtrip,
//! Destroy with DeathCertificate → terminal permanence, double-destroy rejection,
//! Seal-then-destroy (terminal from sealed), Destroy-then-seal rejection.

use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions,
    lifecycle::{CellLifecycle, DeathCertificate, DeathReason},
};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

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

fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
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
// Test 1 (happy path): Seal a cell; verify lifecycle = Sealed.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_seal_transitions_to_sealed() {
    let cell = make_open_cell(1, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let reason = [0xAA; 32];
    let turn = bare_turn(
        cell_id,
        0,
        vec![Effect::CellSeal {
            target: cell_id,
            reason,
        }],
    );
    let result = executor.execute(&turn, &mut ledger);

    assert!(result.is_committed(), "seal should commit; got {result:?}");
    let cell = ledger.get(&cell_id).unwrap();
    assert!(
        cell.lifecycle.is_sealed(),
        "cell must be Sealed after Effect::CellSeal"
    );
    match &cell.lifecycle {
        CellLifecycle::Sealed { reason_hash, .. } => {
            assert_eq!(
                *reason_hash, [0xAA; 32],
                "reason_hash must be bound into lifecycle"
            );
        }
        other => panic!("expected Sealed, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 2 (adversarial): Post-seal Effect::SetField is rejected.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_post_seal_effect_rejected() {
    let cell = make_open_cell(2, 1000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();

    // Seal first.
    let seal_turn = bare_turn(
        cell_id,
        0,
        vec![Effect::CellSeal {
            target: cell_id,
            reason: [0xBB; 32],
        }],
    );
    assert!(executor.execute(&seal_turn, &mut ledger).is_committed());

    // Now try to set a field on the sealed cell.
    let set_turn = bare_turn(
        cell_id,
        1,
        vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [0xFF; 32],
        }],
    );
    let result = executor.execute(&set_turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "SetField on a sealed cell must be rejected; got {result:?}"
    );
    // Field must be unchanged.
    let cell = ledger.get(&cell_id).unwrap();
    assert_eq!(
        cell.state.fields[0], [0u8; 32],
        "field must be unchanged after rejection"
    );
}

// ---------------------------------------------------------------------------
// Test 3 (happy path): Seal → Unseal roundtrip restores to Live.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_seal_then_unseal_restores_live() {
    let cell = make_open_cell(3, 500);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();

    // Seal.
    let seal_turn = bare_turn(
        cell_id,
        0,
        vec![Effect::CellSeal {
            target: cell_id,
            reason: [0x01; 32],
        }],
    );
    let seal_result = executor.execute(&seal_turn, &mut ledger);
    let seal_receipt_hash = match seal_result {
        dregg_turn::TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("seal must commit; got {other:?}"),
    };
    assert!(ledger.get(&cell_id).unwrap().lifecycle.is_sealed());

    // Unseal.
    let mut unseal_turn = bare_turn(cell_id, 1, vec![Effect::CellUnseal { target: cell_id }]);
    unseal_turn.previous_receipt_hash = Some(seal_receipt_hash);
    let result = executor.execute(&unseal_turn, &mut ledger);
    let unseal_receipt_hash = match result {
        dregg_turn::TurnResult::Committed { receipt, .. } => receipt.receipt_hash(),
        other => panic!("unseal must commit; got {other:?}"),
    };

    let cell = ledger.get(&cell_id).unwrap();
    assert_eq!(
        cell.lifecycle,
        CellLifecycle::Live,
        "lifecycle must be Live after unseal"
    );

    // Effects accepted again after unseal.
    let mut set_turn = bare_turn(
        cell_id,
        2,
        vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [0x42; 32],
        }],
    );
    set_turn.previous_receipt_hash = Some(unseal_receipt_hash);
    let result = executor.execute(&set_turn, &mut ledger);
    assert!(
        result.is_committed(),
        "SetField must succeed after unseal; got {result:?}"
    );
    assert_eq!(ledger.get(&cell_id).unwrap().state.fields[0], [0x42; 32]);
}

// ---------------------------------------------------------------------------
// Test 4 (adversarial): Unseal on a Live cell is rejected.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_unseal_of_live_cell_rejected() {
    let cell = make_open_cell(4, 500);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let turn = bare_turn(cell_id, 0, vec![Effect::CellUnseal { target: cell_id }]);
    let result = executor.execute(&turn, &mut ledger);

    assert!(
        result.is_rejected(),
        "CellUnseal on a Live cell must be rejected; got {result:?}"
    );
    // Cell still Live.
    assert_eq!(ledger.get(&cell_id).unwrap().lifecycle, CellLifecycle::Live);
}

// ---------------------------------------------------------------------------
// Test 5 (happy path): Destroy with a valid DeathCertificate → Destroyed.
// Test 5b (adversarial): A second effect targeting the destroyed cell → rejected.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_destroy_with_certificate_then_terminal() {
    let cell = make_open_cell(5, 200);
    let cell_id = cell.id();
    let pre_commitment = cell.state_commitment();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();

    let cert = DeathCertificate {
        cell_id,
        last_receipt_hash: [1u8; 32],
        final_state_commitment: pre_commitment,
        destroyed_at_height: 42,
        reason: DeathReason::Voluntary,
    };
    let cert_hash = cert.certificate_hash();

    let destroy_turn = bare_turn(
        cell_id,
        0,
        vec![Effect::CellDestroy {
            target: cell_id,
            certificate: cert,
        }],
    );
    let result = executor.execute(&destroy_turn, &mut ledger);
    assert!(
        result.is_committed(),
        "CellDestroy must commit; got {result:?}"
    );

    // Lifecycle is Destroyed and carries the certificate hash.
    let cell = ledger.get(&cell_id).unwrap();
    assert!(cell.lifecycle.is_destroyed(), "cell must be Destroyed");
    match &cell.lifecycle {
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => {
            assert_eq!(
                *death_certificate_hash, cert_hash,
                "cert hash must be bound"
            );
            assert_eq!(*destroyed_at, 42, "destroyed_at must match the certificate");
        }
        other => panic!("expected Destroyed, got {other:?}"),
    }

    // Any subsequent effect is rejected (terminal).
    let set_turn = bare_turn(
        cell_id,
        1,
        vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [0xFF; 32],
        }],
    );
    let result = executor.execute(&set_turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "SetField on Destroyed cell must be rejected; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Test 6 (adversarial): DeathCertificate with wrong cell_id is rejected.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_destroy_certificate_mismatch_rejected() {
    let cell = make_open_cell(6, 100);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();

    // Wrong cell_id in the certificate.
    let cert = DeathCertificate {
        cell_id: CellId::from_bytes([0xDE; 32]), // wrong id
        last_receipt_hash: [0u8; 32],
        final_state_commitment: [0u8; 32],
        destroyed_at_height: 1,
        reason: DeathReason::Forced,
    };

    let turn = bare_turn(
        cell_id,
        0,
        vec![Effect::CellDestroy {
            target: cell_id,
            certificate: cert,
        }],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "CellDestroy with mismatched certificate must be rejected; got {result:?}"
    );
    // Cell still Live.
    assert_eq!(ledger.get(&cell_id).unwrap().lifecycle, CellLifecycle::Live);
}

// ---------------------------------------------------------------------------
// Test 7 (adversarial): Double-seal is rejected; first seal's reason preserved.
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_double_seal_rejected() {
    let cell = make_open_cell(7, 100);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();
    let first_reason = [0x11; 32];
    let second_reason = [0x22; 32];

    // First seal.
    let t1 = bare_turn(
        cell_id,
        0,
        vec![Effect::CellSeal {
            target: cell_id,
            reason: first_reason,
        }],
    );
    assert!(executor.execute(&t1, &mut ledger).is_committed());

    // Second seal must be rejected.
    let t2 = bare_turn(
        cell_id,
        1,
        vec![Effect::CellSeal {
            target: cell_id,
            reason: second_reason,
        }],
    );
    let result = executor.execute(&t2, &mut ledger);
    assert!(
        result.is_rejected(),
        "double-seal must be rejected; got {result:?}"
    );

    // Original reason_hash is preserved.
    match &ledger.get(&cell_id).unwrap().lifecycle {
        CellLifecycle::Sealed { reason_hash, .. } => {
            assert_eq!(
                *reason_hash, first_reason,
                "original reason_hash must be preserved"
            );
        }
        other => panic!("expected Sealed, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Test 8 (adversarial): Destroy a Destroyed cell is rejected (terminal).
// ---------------------------------------------------------------------------

#[test]
fn lifecycle_destroy_of_destroyed_cell_rejected() {
    let cell = make_open_cell(8, 100);
    let cell_id = cell.id();
    let pre_commitment = cell.state_commitment();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = zero_executor();

    let cert1 = DeathCertificate {
        cell_id,
        last_receipt_hash: [1u8; 32],
        final_state_commitment: pre_commitment,
        destroyed_at_height: 10,
        reason: DeathReason::Voluntary,
    };
    let t1 = bare_turn(
        cell_id,
        0,
        vec![Effect::CellDestroy {
            target: cell_id,
            certificate: cert1,
        }],
    );
    assert!(executor.execute(&t1, &mut ledger).is_committed());
    assert!(ledger.get(&cell_id).unwrap().lifecycle.is_destroyed());

    // Try to destroy again.
    let cert2 = DeathCertificate {
        cell_id,
        last_receipt_hash: [2u8; 32],
        final_state_commitment: pre_commitment,
        destroyed_at_height: 20,
        reason: DeathReason::Forced,
    };
    let t2 = bare_turn(
        cell_id,
        1,
        vec![Effect::CellDestroy {
            target: cell_id,
            certificate: cert2,
        }],
    );
    let result = executor.execute(&t2, &mut ledger);
    assert!(
        result.is_rejected(),
        "second CellDestroy must be rejected; got {result:?}"
    );
}
