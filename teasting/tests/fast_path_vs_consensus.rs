//! Fast-path vs consensus routing integration test.
//!
//! Dregg uses two execution paths:
//! - **Fast path (single-owner)**: A turn that only touches cells owned by the submitter
//!   can be applied immediately without consensus (local signature suffices).
//! - **Consensus path (shared cells)**: A turn touching cells owned by multiple agents
//!   requires consensus to prevent double-spend and resolve ordering.
//!
//! This test verifies that the routing logic correctly distinguishes these cases and
//! that both paths produce consistent results.

use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{Cell, CellId, Ledger, Preconditions};
use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
use dregg_turn::executor::{ComputronCosts, TurnExecutor};
use dregg_turn::fast_path::{
    CellLockTable, FastPathError, assemble_certificate, execute_certified_turn,
    process_fast_path_lock,
};
use dregg_turn::forest::{CallForest, CallTree};
use dregg_turn::{ExecutionPath, Turn, compute_execution_path};
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

/// Derive a deterministic Ed25519 keypair from a u8 seed.
fn keypair_from_seed(seed: u8) -> ([u8; 32], [u8; 32]) {
    let mut s = [0u8; 32];
    s[0] = seed;
    let sk = SigningKey::from_bytes(&s);
    let vk: VerifyingKey = (&sk).into();
    (s, vk.to_bytes())
}

/// Sign a turn_hash with the agent's seed.
fn agent_sig(seed: &[u8; 32], turn_hash: &[u8; 32]) -> [u8; 64] {
    let sk = SigningKey::from_bytes(seed);
    sk.sign(turn_hash).to_bytes()
}

/// Permissive permissions: no auth required for any action.
/// Used in tests to avoid needing real Ed25519 signatures.
fn permissive_permissions() -> Permissions {
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

/// Helper: create a cell owned by the given public key with permissive permissions.
fn insert_permissive_cell(ledger: &mut Ledger, owner: [u8; 32], balance: u64) -> CellId {
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(owner, token_id, balance);
    cell.permissions = permissive_permissions();
    let id = cell.id();
    ledger.insert_cell(cell).unwrap();
    id
}

/// Helper: create a cell with a specific token_id (to avoid CellId collision).
fn insert_permissive_cell_domain(
    ledger: &mut Ledger,
    owner: [u8; 32],
    token_id: [u8; 32],
    balance: u64,
) -> CellId {
    let mut cell = Cell::with_balance(owner, token_id, balance);
    cell.permissions = permissive_permissions();
    let id = cell.id();
    ledger.insert_cell(cell).unwrap();
    id
}

/// Helper: make a minimal turn with a single action targeting the agent's own cell (no effects).
/// This is the simplest turn that the executor accepts (non-empty forest, no effects).
fn make_own_cell_turn(agent_id: CellId) -> Turn {
    let action = Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        balance_change: None,
        witness_blobs: vec![],
        commitment_mode: Default::default(),
    };

    let tree = CallTree {
        action,
        children: vec![],
        hash: [0u8; 32],
    };

    Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        },
        fee: 100,
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

/// Helper: make a turn with a SetField effect on the agent's own cell.
fn make_self_write_turn(agent_id: CellId) -> Turn {
    let action = Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: agent_id,
            index: 0,
            value: [42u8; 32],
        }],
        may_delegate: DelegationMode::None,
        balance_change: None,
        witness_blobs: vec![],
        commitment_mode: Default::default(),
    };

    let tree = CallTree {
        action,
        children: vec![],
        hash: [0u8; 32],
    };

    Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        },
        fee: 100,
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

/// Helper: make a turn that writes to another cell (SetField effect on target).
fn make_cross_cell_turn(agent_id: CellId, target_id: CellId) -> Turn {
    let action = Action {
        target: target_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value: [1u8; 32],
        }],
        may_delegate: DelegationMode::None,
        balance_change: None,
        witness_blobs: vec![],
        commitment_mode: Default::default(),
    };

    let tree = CallTree {
        action,
        children: vec![],
        hash: [0u8; 32],
    };

    Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        },
        fee: 100,
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

/// Single-owner turn routes to fast path.
#[test]
fn test_single_owner_routes_to_fast_path() {
    let mut ledger = Ledger::new();
    let alice_pk = [1u8; 32];
    let alice_id = insert_permissive_cell(&mut ledger, alice_pk, 10_000);

    // A turn that only reads/writes Alice's own cell.
    let turn = make_own_cell_turn(alice_id);
    let path = compute_execution_path(&turn, &ledger);

    assert_eq!(path, ExecutionPath::FastPath);
    assert!(path.is_fast_path());
    assert!(!path.is_consensus());
}

/// Multi-owner turn routes to consensus.
#[test]
fn test_multi_owner_routes_to_consensus() {
    let mut ledger = Ledger::new();
    let alice_pk = [1u8; 32];
    let bob_pk = [2u8; 32];
    let alice_id = insert_permissive_cell(&mut ledger, alice_pk, 10_000);
    // Use a different token_id to avoid CellId collision.
    let bob_token = [1u8; 32];
    let bob_id = insert_permissive_cell_domain(&mut ledger, bob_pk, bob_token, 10_000);

    // Alice's turn writes to Bob's cell — must go through consensus.
    let turn = make_cross_cell_turn(alice_id, bob_id);
    let path = compute_execution_path(&turn, &ledger);

    assert_eq!(path, ExecutionPath::Consensus);
    assert!(path.is_consensus());
    assert!(!path.is_fast_path());
}

/// Fast-path execution: single-owner turn executes immediately via certificate.
#[test]
fn test_fast_path_executes_immediately() {
    let mut ledger = Ledger::new();
    let (alice_seed, alice_pk) = keypair_from_seed(1);
    let alice_id = insert_permissive_cell(&mut ledger, alice_pk, 10_000);

    // Verify the turn routes to fast path.
    let turn = make_self_write_turn(alice_id);
    assert_eq!(
        compute_execution_path(&turn, &ledger),
        ExecutionPath::FastPath
    );

    let turn_hash = turn.hash();
    let agent_signature = agent_sig(&alice_seed, &turn_hash);

    // Simulate 3 validators granting locks (2f+1 with f=1, n=3).
    let validator_seeds: Vec<[u8; 32]> = (0..3u8).map(|i| keypair_from_seed(0xA0 + i).0).collect();

    let mut table = CellLockTable::with_defaults();

    let mut signs = Vec::new();
    for seed in &validator_seeds {
        let sign = process_fast_path_lock(
            &mut table,
            &turn,
            turn_hash,
            100,
            &ledger,
            seed,
            &agent_signature,
        )
        .expect("lock should succeed for single-owner turn");
        signs.push(sign);
    }

    // Assemble certificate (threshold=2 for 2f+1 with f=0 simplified).
    let cert = assemble_certificate(turn, turn_hash, signs, 2)
        .expect("certificate assembly should succeed");

    // Execute the certified turn — this is the "immediate" execution (no consensus round).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = execute_certified_turn(&cert, &executor, &mut ledger, &mut table);

    // The turn should commit successfully.
    assert!(
        result.is_committed(),
        "fast-path turn should execute immediately, got: {result:?}"
    );

    // Locks should be released after execution.
    assert!(table.is_empty(), "locks should be released after execution");

    // Verify the ledger was updated (nonce bumped).
    let cell = ledger.get(&alice_id).expect("alice cell should exist");
    assert_eq!(
        cell.state.nonce(),
        1,
        "nonce should be bumped after execution"
    );
    // Verify the field was set.
    assert_eq!(cell.state.fields[0], [42u8; 32], "field should be updated");
}

/// Consensus-path execution: shared-cell turn should NOT execute via fast path.
#[test]
fn test_consensus_path_waits_for_finalization() {
    let mut ledger = Ledger::new();
    let (alice_seed, alice_pk) = keypair_from_seed(1);
    let (_bob_seed, bob_pk) = keypair_from_seed(2);
    let alice_id = insert_permissive_cell(&mut ledger, alice_pk, 10_000);
    let bob_token = [1u8; 32];
    let bob_id = insert_permissive_cell_domain(&mut ledger, bob_pk, bob_token, 10_000);

    // A multi-owner turn (Alice writes to Bob's cell).
    let turn = make_cross_cell_turn(alice_id, bob_id);
    let turn_hash = turn.hash();
    let agent_signature = agent_sig(&alice_seed, &turn_hash);

    // Verify it routes to consensus.
    assert_eq!(
        compute_execution_path(&turn, &ledger),
        ExecutionPath::Consensus
    );

    // Attempting to acquire a fast-path lock should fail (not eligible).
    let mut table = CellLockTable::with_defaults();
    let (validator_seed, _) = keypair_from_seed(0xAA);
    let result = process_fast_path_lock(
        &mut table,
        &turn,
        turn_hash,
        100,
        &ledger,
        &validator_seed,
        &agent_signature,
    );

    assert!(
        result.is_err(),
        "multi-owner turn should be rejected from fast path"
    );
    match result.unwrap_err() {
        FastPathError::NotEligible => {} // Expected.
        other => panic!("expected NotEligible, got: {other:?}"),
    }

    // The turn should NOT have executed — ledger state unchanged.
    let bob_cell = ledger.get(&bob_id).expect("bob cell should exist");
    assert_eq!(
        bob_cell.state.nonce(),
        0,
        "bob's cell should not have been modified"
    );
    assert!(table.is_empty(), "no locks should have been acquired");

    // In a real system, this turn would wait for consensus ordering.
    // We verify that it CAN execute through the normal executor (simulating post-consensus).
    // For cross-cell access, Alice's cell needs a capability to Bob's cell.
    // Grant Alice's cell the capability to access Bob's cell.
    {
        let alice_cell = ledger.get_mut(&alice_id).unwrap();
        alice_cell.capabilities.grant(bob_id, AuthRequired::None);
    }

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "multi-owner turn should execute after consensus (via normal executor), got: {result:?}"
    );
}

/// Both paths produce the same final state for equivalent operations.
#[test]
fn test_both_paths_deterministic() {
    // --- Fast-path execution ---
    let mut ledger_fast = Ledger::new();
    let (alice_seed, alice_pk) = keypair_from_seed(1);
    let alice_id_fast = insert_permissive_cell(&mut ledger_fast, alice_pk, 10_000);

    let turn_fast = make_self_write_turn(alice_id_fast);
    assert_eq!(
        compute_execution_path(&turn_fast, &ledger_fast),
        ExecutionPath::FastPath
    );

    // Execute via fast path (lock + certificate + execute).
    let turn_hash = turn_fast.hash();
    let agent_signature = agent_sig(&alice_seed, &turn_hash);
    let mut table = CellLockTable::with_defaults();
    let (validator_seed, _) = keypair_from_seed(0xAA);
    let sign = process_fast_path_lock(
        &mut table,
        &turn_fast,
        turn_hash,
        100,
        &ledger_fast,
        &validator_seed,
        &agent_signature,
    )
    .unwrap();
    let cert = assemble_certificate(turn_fast, turn_hash, vec![sign], 1).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result_fast = execute_certified_turn(&cert, &executor, &mut ledger_fast, &mut table);
    assert!(
        result_fast.is_committed(),
        "fast-path should commit, got: {result_fast:?}"
    );

    // --- Consensus-path execution (simulated: direct executor call) ---
    let mut ledger_consensus = Ledger::new();
    let alice_id_consensus = insert_permissive_cell(&mut ledger_consensus, alice_pk, 10_000);

    let turn_consensus = make_self_write_turn(alice_id_consensus);
    // Even though this could go fast-path, we simulate consensus by calling the executor directly.
    let consensus_executor = TurnExecutor::new(ComputronCosts::zero());
    let result_consensus = consensus_executor.execute(&turn_consensus, &mut ledger_consensus);
    assert!(
        result_consensus.is_committed(),
        "consensus-path should commit, got: {result_consensus:?}"
    );

    // Both ledgers should have the same final state for the affected cell.
    let cell_fast = ledger_fast.get(&alice_id_fast).unwrap();
    let cell_consensus = ledger_consensus.get(&alice_id_consensus).unwrap();

    // Same nonce (both bumped once).
    assert_eq!(cell_fast.state.nonce(), cell_consensus.state.nonce());
    // Same field values (both set field 0 to [42; 32]).
    assert_eq!(cell_fast.state.fields, cell_consensus.state.fields);
    // Same balance (both deducted the same fee of 0 since ComputronCosts::zero()).
    assert_eq!(cell_fast.state.balance(), cell_consensus.state.balance());
}

/// Conflict detection: two concurrent fast-path turns on the same cell conflict.
#[test]
fn test_fast_path_conflict_detection() {
    let mut ledger = Ledger::new();
    let (alice_seed, alice_pk) = keypair_from_seed(1);
    let alice_id = insert_permissive_cell(&mut ledger, alice_pk, 10_000);

    // Turn 1: Alice writes value A to her cell.
    let turn1 = make_self_write_turn(alice_id);
    let turn1_hash = turn1.hash();
    let sig1 = agent_sig(&alice_seed, &turn1_hash);

    // Turn 2: Alice writes a different value (different memo to get different hash).
    let mut turn2 = make_self_write_turn(alice_id);
    turn2.memo = Some("second turn".to_string());
    let turn2_hash = turn2.hash();
    let sig2 = agent_sig(&alice_seed, &turn2_hash);

    // Sanity: both are different turns.
    assert_ne!(turn1_hash, turn2_hash);

    // Both should individually route to fast path.
    assert_eq!(
        compute_execution_path(&turn1, &ledger),
        ExecutionPath::FastPath
    );
    assert_eq!(
        compute_execution_path(&turn2, &ledger),
        ExecutionPath::FastPath
    );

    let mut table = CellLockTable::with_defaults();
    let (validator_seed, _) = keypair_from_seed(0xAA);

    // First turn acquires the lock successfully.
    let result1 = process_fast_path_lock(
        &mut table,
        &turn1,
        turn1_hash,
        100,
        &ledger,
        &validator_seed,
        &sig1,
    );
    assert!(result1.is_ok(), "first turn should acquire lock");

    // Second turn tries to lock the same cell — should get a LockConflict.
    let result2 = process_fast_path_lock(
        &mut table,
        &turn2,
        turn2_hash,
        100,
        &ledger,
        &validator_seed,
        &sig2,
    );
    assert!(
        result2.is_err(),
        "second turn should be rejected due to conflict"
    );

    match result2.unwrap_err() {
        FastPathError::LockConflict { cell_id, held_by } => {
            assert_eq!(cell_id, alice_id, "conflict should be on alice's cell");
            assert_eq!(held_by, turn1_hash, "conflict should be held by first turn");
        }
        other => panic!("expected LockConflict, got: {other:?}"),
    }

    // No double-write occurred: only one lock is held.
    assert_eq!(table.len(), 1);
}
