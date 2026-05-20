//! Comprehensive tests for the turn crate.
//!
//! Tests cover:
//! - Simple single-action turns (set field, transfer)
//! - Multi-action turns with children (parent delegates to child)
//! - Permission denial (action requires Proof, only Signature given)
//! - Precondition failure (wrong nonce, insufficient balance)
//! - Budget enforcement (turn exceeds computron limit)
//! - Atomicity (child fails -> parent's effects rolled back too)
//! - Delegation modes (ParentsOwn works, None blocks children)
//! - Capability isolation (action targets cell not in capability set -> rejected)
//! - Replay protection (same nonce rejected)
//! - Turn receipt hashing (deterministic, Merkle-linked)
//! - Signature verification (real Ed25519 signatures required)
//! - Proof verification (fail-closed without verifier)
//! - Receive permission enforcement

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use pyana_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions, VerificationKey,
    preconditions::Preconditions as CellPreconditions,
    state::{FIELD_ZERO, STATE_SLOTS},
};

use crate::action::{Action, Authorization, DelegationMode, Effect, symbol};
use crate::builder::TurnBuilder;
use crate::error::TurnError;
use crate::executor::{ComputronCosts, ProofVerifier, TurnExecutor};
use crate::forest::{CallForest, CallTree};
use crate::turn::Turn;

// =============================================================================
// Test helpers
// =============================================================================

/// A test signing keypair.
struct TestKeypair {
    signing_key: SigningKey,
    public_key: [u8; 32],
}

impl TestKeypair {
    /// Create a keypair from a seed byte.
    fn from_seed(seed: u8) -> Self {
        let mut seed_bytes = [0u8; 32];
        seed_bytes[0] = seed;
        let signing_key = SigningKey::from_bytes(&seed_bytes);
        let verifying_key: VerifyingKey = (&signing_key).into();
        let public_key = verifying_key.to_bytes();
        TestKeypair { signing_key, public_key }
    }

    /// Sign an action and return the Authorization.
    fn sign_action(&self, action: &Action) -> Authorization {
        let message = TurnExecutor::compute_signing_message(action);
        let signature = self.signing_key.sign(&message);
        let sig_bytes = signature.to_bytes();
        Authorization::from_sig_bytes(sig_bytes)
    }
}

/// Helper: create a test cell with a known keypair and open permissions (no auth needed).
fn make_open_cell(seed: u8, balance: u64) -> (Cell, TestKeypair) {
    let kp = TestKeypair::from_seed(seed);
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(kp.public_key, token_id, balance);
    // Open permissions: no auth needed for anything.
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    (cell, kp)
}

/// Helper: create a test cell with signature-required permissions and a known keypair.
fn make_sig_cell(seed: u8, balance: u64) -> (Cell, TestKeypair) {
    let kp = TestKeypair::from_seed(seed);
    let token_id = [0u8; 32];
    let cell = Cell::with_balance(kp.public_key, token_id, balance);
    // Default permissions: Signature required.
    (cell, kp)
}

/// Helper: create a ledger with two open cells (agent + target).
fn setup_two_open_cells(agent_balance: u64, target_balance: u64) -> (Ledger, CellId, CellId) {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, agent_balance);
    let (target, _) = make_open_cell(2, target_balance);
    let agent_id = agent.id;
    let target_id = target.id;

    // Grant agent a capability to target.
    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();
    (ledger, agent_id, target_id)
}

/// Helper: create an executor with zero costs for simpler testing.
fn zero_cost_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

/// Helper: create an executor with default costs.
fn default_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::default_costs())
}

/// A test proof verifier that always accepts proofs.
struct AlwaysAcceptVerifier;

impl ProofVerifier for AlwaysAcceptVerifier {
    fn verify(&self, _proof: &[u8], _public_inputs: &[u8], _vk: &[u8]) -> bool {
        true
    }
}

/// A test proof verifier that always rejects proofs.
struct AlwaysRejectVerifier;

impl ProofVerifier for AlwaysRejectVerifier {
    fn verify(&self, _proof: &[u8], _public_inputs: &[u8], _vk: &[u8]) -> bool {
        false
    }
}

// =============================================================================
// Test: Simple single-action turn — SetField (open permissions)
// =============================================================================

#[test]
fn test_simple_set_field() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(1000, 0);
    let executor = zero_cost_executor();

    let value = [42u8; 32];
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_field");
        action.set_field(target_id, 0, value);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Verify the field was set.
    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], value);
}

// =============================================================================
// Test: Simple single-action turn — Transfer (open permissions)
// =============================================================================

#[test]
fn test_simple_transfer() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(1000, 500);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "transfer");
        action.transfer(agent_id, target_id, 200);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Agent paid 100 fee + transferred 200.
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(agent.state.balance, 1000 - 100 - 200);

    let target = ledger.get(&target_id).unwrap();
    assert_eq!(target.state.balance, 500 + 200);
}

// =============================================================================
// Test: Multi-action turn with children (delegation)
// =============================================================================

#[test]
fn test_multi_action_with_children() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 1000);
    let executor = zero_cost_executor();

    let value_parent = [1u8; 32];
    let value_child = [2u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "parent_op");
        action.set_field(target_id, 0, value_parent);
        action.delegation(DelegationMode::ParentsOwn);

        // Child action on the same target (delegation from parent).
        let child = action.child(target_id, "child_op");
        child.set_field(target_id, 1, value_child);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], value_parent);
    assert_eq!(cell.state.fields[1], value_child);
}

// =============================================================================
// Test: Permission denial — requires Proof, only Signature given
// =============================================================================

#[test]
fn test_permission_denied_proof_required() {
    let mut ledger = Ledger::new();
    let (agent, agent_kp) = make_sig_cell(1, 5000);
    let agent_id = agent.id;

    // Target requires Proof for set_state.
    let (mut target, _target_kp) = make_sig_cell(2, 0);
    target.permissions = Permissions::zkapp();
    // Give it a verification key so proofs can potentially work.
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Build action, then sign it properly with agent's key.
    // But the TARGET cell requires proof, not signature.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        // Provide Signature (with valid sig for agent's key), but cell requires Proof.
        action.authorize_signature([0u8; 64]); // placeholder, will be rejected for wrong type
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _path) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { required, .. } => {
            assert_eq!(required, AuthRequired::Proof);
        }
        other => panic!("expected PermissionDenied, got {other:?}"),
    }
}

// =============================================================================
// Test: Permission satisfied with Proof (with verifier)
// =============================================================================

#[test]
fn test_permission_satisfied_with_proof() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4]);
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], [99u8; 32]);
}

// =============================================================================
// Test: Proof rejected when verifier says no
// =============================================================================

#[test]
fn test_proof_rejected_by_verifier() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysRejectVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4]);
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(reason.contains("verification failed"), "got: {reason}");
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Proof rejected when no verifier configured (fail-closed)
// =============================================================================

#[test]
fn test_proof_fail_closed_no_verifier() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    // No proof verifier configured.
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4]);
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(reason.contains("no proof verifier"), "got: {reason}");
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Proof rejected when cell has no verification key
// =============================================================================

#[test]
fn test_proof_rejected_no_verification_key() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    // No verification key set!
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4]);
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(reason.contains("no verification key"), "got: {reason}");
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Real Ed25519 signature verification succeeds
// =============================================================================

#[test]
fn test_real_signature_verification() {
    let mut ledger = Ledger::new();
    let (agent, agent_kp) = make_sig_cell(1, 5000);
    let agent_id = agent.id;

    // Target with Signature-required permissions.
    let (target, target_kp) = make_sig_cell(2, 0);
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Build the action first to get the signing message, then sign it.
    let target_cell_id = target_id;
    let method = symbol("set_field");
    let effects = vec![Effect::SetField { cell: target_cell_id, index: 0, value: [42u8; 32] }];

    // Create the action to get the signing message.
    let unsigned_action = Action {
        target: target_cell_id,
        method,
        args: vec![],
        authorization: Authorization::None, // placeholder
        preconditions: CellPreconditions::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
    };
    let message = TurnExecutor::compute_signing_message(&unsigned_action);

    // Sign with TARGET's key (the cell being acted upon).
    let signature = target_kp.signing_key.sign(&message);
    let sig_bytes = signature.to_bytes();
    let auth = Authorization::from_sig_bytes(sig_bytes);

    // Build the turn manually with the real signature.
    let signed_action = Action {
        target: target_cell_id,
        method,
        args: vec![],
        authorization: auth,
        preconditions: CellPreconditions::default(),
        effects,
        may_delegate: DelegationMode::None,
    };

    let mut forest = CallForest::new();
    forest.add_root(signed_action);
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 500,
        memo: None,
        valid_until: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], [42u8; 32]);
}

// =============================================================================
// Test: Invalid Ed25519 signature is rejected
// =============================================================================

#[test]
fn test_invalid_signature_rejected() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_sig_cell(1, 5000);
    let agent_id = agent.id;

    let (target, _target_kp) = make_sig_cell(2, 0);
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Use a garbage signature (all zeros).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_field");
        action.authorize_signature([0u8; 64]);
        action.set_field(target_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(
                reason.contains("signature verification failed") || reason.contains("not a valid Ed25519"),
                "got: {reason}"
            );
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Signature from wrong key is rejected
// =============================================================================

#[test]
fn test_wrong_key_signature_rejected() {
    let mut ledger = Ledger::new();
    let (agent, agent_kp) = make_sig_cell(1, 5000);
    let agent_id = agent.id;

    let (target, _target_kp) = make_sig_cell(2, 0);
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Sign with AGENT's key, but the TARGET's permissions check against TARGET's public key.
    let method = symbol("set_field");
    let effects = vec![Effect::SetField { cell: target_id, index: 0, value: [42u8; 32] }];
    let unsigned_action = Action {
        target: target_id,
        method,
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
    };
    let message = TurnExecutor::compute_signing_message(&unsigned_action);

    // Sign with AGENT's key (wrong key for the target cell).
    let signature = agent_kp.signing_key.sign(&message);
    let sig_bytes = signature.to_bytes();
    let auth = Authorization::from_sig_bytes(sig_bytes);

    let signed_action = Action {
        target: target_id,
        method,
        args: vec![],
        authorization: auth,
        preconditions: CellPreconditions::default(),
        effects,
        may_delegate: DelegationMode::None,
    };

    let mut forest = CallForest::new();
    forest.add_root(signed_action);
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 500,
        memo: None,
        valid_until: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(reason.contains("signature verification failed"), "got: {reason}");
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Precondition failure — wrong nonce
// =============================================================================

#[test]
fn test_precondition_nonce_mismatch() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "check_nonce");
        // Require nonce = 5, but target has nonce = 0.
        action.require_nonce(5);
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PreconditionFailed { description } => {
            assert!(description.contains("Nonce"), "got: {description}");
        }
        other => panic!("expected PreconditionFailed, got {other:?}"),
    }
}

// =============================================================================
// Test: Precondition failure — insufficient balance
// =============================================================================

#[test]
fn test_precondition_min_balance() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 100);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "check_balance");
        // Require min balance of 500, but target only has 100.
        action.require_min_balance(500);
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PreconditionFailed { description } => {
            assert!(description.contains("InsufficientBalance"), "got: {description}");
        }
        other => panic!("expected PreconditionFailed, got {other:?}"),
    }
}

// =============================================================================
// Test: Budget enforcement — turn exceeds computron limit
// =============================================================================

#[test]
fn test_budget_exceeded() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    // Use default costs (action_base=100, signature_verify=200, etc.)
    let executor = default_executor();

    // Create a turn with many actions, but a very small fee.
    let mut builder = TurnBuilder::new(agent_id, 0);
    for i in 0..20 {
        let action = builder.action(target_id, "expensive_op");
        action.set_field(target_id, i % STATE_SLOTS, [i as u8; 32]);
    }
    // Fee is only 10 computrons — way too low for 20 actions.
    let turn = builder.fee(10).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::BudgetExceeded { limit, used } => {
            assert_eq!(limit, 10);
            assert!(used > 10);
        }
        other => panic!("expected BudgetExceeded, got {other:?}"),
    }

    // Verify atomicity: target field should be unchanged.
    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], FIELD_ZERO);
}

// =============================================================================
// Test: Atomicity — child fails, parent's effects rolled back
// =============================================================================

#[test]
fn test_atomicity_child_failure_rollback() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 1000);
    let executor = zero_cost_executor();

    // Snapshot the initial state.
    let initial_target_balance = ledger.get(&target_id).unwrap().state.balance;
    let initial_target_field = ledger.get(&target_id).unwrap().state.fields[0];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "parent_op");
        action.set_field(target_id, 0, [0xAA; 32]);
        action.delegation(DelegationMode::ParentsOwn);

        // Child tries to transfer more than is available (will fail).
        let child = action.child(target_id, "child_transfer");
        child.transfer(target_id, agent_id, 999_999); // way more than target has
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, path) = result.unwrap_rejected();
    match error {
        TurnError::InsufficientBalance { .. } => {}
        other => panic!("expected InsufficientBalance, got {other:?}"),
    }
    // The failure was in the child.
    assert_eq!(path.len(), 2); // [root_idx, child_idx]

    // Verify atomicity: parent's SetField was rolled back.
    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], initial_target_field);
    assert_eq!(cell.state.balance, initial_target_balance);

    // Agent nonce was NOT incremented (full rollback).
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(agent.state.nonce, 0);
}

// =============================================================================
// Test: Delegation mode — ParentsOwn works
// =============================================================================

#[test]
fn test_delegation_parents_own_allows_child() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "parent");
        action.delegation(DelegationMode::ParentsOwn);

        // Child targets same cell — should work.
        let child = action.child(target_id, "child_same_target");
        child.set_field(target_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], [42u8; 32]);
}

// =============================================================================
// Test: Delegation mode — None blocks children targeting different cells
// =============================================================================

#[test]
fn test_delegation_none_blocks_child() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target1, _) = make_open_cell(2, 0);
    let (target2, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target1_id = target1.id;
    let target2_id = target2.id;

    let mut agent_with_caps = agent;
    agent_with_caps.capabilities.grant(target1_id, AuthRequired::None);
    agent_with_caps.capabilities.grant(target2_id, AuthRequired::None);

    ledger.insert_cell(agent_with_caps).unwrap();
    ledger.insert_cell(target1).unwrap();
    ledger.insert_cell(target2).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target1_id, "parent");
        // DelegationMode::None — children cannot target different cells.
        action.delegation(DelegationMode::None);

        let child = action.child(target2_id, "child_different_target");
        child.set_field(target2_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::DelegationDenied { parent, child_target } => {
            assert_eq!(parent, target1_id);
            assert_eq!(child_target, target2_id);
        }
        other => panic!("expected DelegationDenied, got {other:?}"),
    }
}

// =============================================================================
// Test: Capability isolation — no capability to target cell
// =============================================================================

#[test]
fn test_capability_isolation() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target, _) = make_open_cell(2, 0);
    let agent_id = agent.id;
    let target_id = target.id;

    // Agent does NOT have a capability to target.
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "unauthorized_access");
        action.set_field(target_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::CapabilityNotHeld { actor, target } => {
            assert_eq!(actor, agent_id);
            assert_eq!(target, target_id);
        }
        other => panic!("expected CapabilityNotHeld, got {other:?}"),
    }
}

// =============================================================================
// Test: Replay protection — wrong nonce rejected
// =============================================================================

#[test]
fn test_replay_protection() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // Agent's nonce is 0, but we submit with nonce 5.
    let mut builder = TurnBuilder::new(agent_id, 5);
    {
        let action = builder.action(target_id, "op");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::NonceReplay { expected, got } => {
            assert_eq!(expected, 0);
            assert_eq!(got, 5);
        }
        other => panic!("expected NonceReplay, got {other:?}"),
    }
}

// =============================================================================
// Test: Replay protection — same nonce cannot be reused
// =============================================================================

#[test]
fn test_nonce_increment_prevents_replay() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // First turn with nonce 0: should succeed.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op1");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn1 = builder.fee(100).build();
    let result1 = executor.execute(&turn1, &mut ledger);
    assert!(result1.is_committed());

    // Agent nonce should now be 1.
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(agent.state.nonce, 1);

    // Try to replay with nonce 0 again: should fail.
    let mut builder2 = TurnBuilder::new(agent_id, 0);
    {
        let action = builder2.action(target_id, "op2");
        action.set_field(target_id, 1, [2u8; 32]);
    }
    let turn2 = builder2.fee(100).build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(result2.is_rejected());

    let (error, _) = result2.unwrap_rejected();
    match error {
        TurnError::NonceReplay { expected, got } => {
            assert_eq!(expected, 1);
            assert_eq!(got, 0);
        }
        other => panic!("expected NonceReplay, got {other:?}"),
    }
}

// =============================================================================
// Test: Expiration — turn past valid_until is rejected
// =============================================================================

#[test]
fn test_turn_expiration() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000); // current time = 1000

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(100).valid_until(500).build(); // expired at 500

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::Expired { valid_until, now } => {
            assert_eq!(valid_until, 500);
            assert_eq!(now, 1000);
        }
        other => panic!("expected Expired, got {other:?}"),
    }
}

// =============================================================================
// Test: Turn receipt hashing is deterministic
// =============================================================================

#[test]
fn test_receipt_deterministic() {
    let (mut ledger1, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let mut ledger2 = ledger1.clone();
    let executor = zero_cost_executor();

    let build_turn = || {
        let mut builder = TurnBuilder::new(agent_id, 0);
        {
            let action = builder.action(target_id, "op");
            action.set_field(target_id, 0, [42u8; 32]);
        }
        builder.fee(100).build()
    };

    let turn1 = build_turn();
    let turn2 = build_turn();

    let result1 = executor.execute(&turn1, &mut ledger1);
    let result2 = executor.execute(&turn2, &mut ledger2);

    let (_, receipt1, _) = result1.unwrap_committed();
    let (_, receipt2, _) = result2.unwrap_committed();

    // Receipts should be identical.
    assert_eq!(receipt1.turn_hash, receipt2.turn_hash);
    assert_eq!(receipt1.forest_hash, receipt2.forest_hash);
    assert_eq!(receipt1.pre_state_hash, receipt2.pre_state_hash);
    assert_eq!(receipt1.post_state_hash, receipt2.post_state_hash);
    assert_eq!(receipt1.effects_hash, receipt2.effects_hash);
    assert_eq!(receipt1.computrons_used, receipt2.computrons_used);
    assert_eq!(receipt1.action_count, receipt2.action_count);

    // Receipt hash should also be deterministic.
    assert_eq!(receipt1.receipt_hash(), receipt2.receipt_hash());
}

// =============================================================================
// Test: Turn receipt contains correct pre/post state hashes
// =============================================================================

#[test]
fn test_receipt_state_hashes() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.set_field(target_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    let (_, receipt, _) = result.unwrap_committed();

    // Pre-state hash should be non-zero.
    assert_ne!(receipt.pre_state_hash, [0u8; 32]);
    // Post-state hash should be non-zero.
    assert_ne!(receipt.post_state_hash, [0u8; 32]);
    // State changed (fee deducted, nonce incremented, field set), so hashes differ.
    assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
}

// =============================================================================
// Test: CallForest hash computation
// =============================================================================

#[test]
fn test_call_forest_hash() {
    let agent_id = CellId::from_bytes([1u8; 32]);

    let action = Action {
        target: agent_id,
        method: symbol("test"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
    };

    let mut forest = CallForest::new();
    forest.add_root(action.clone());

    let hash1 = forest.hash();
    assert_ne!(hash1, [0u8; 32]); // Non-zero hash.

    // Same forest produces same hash.
    let mut forest2 = CallForest::new();
    forest2.add_root(action);
    let hash2 = forest2.hash();
    assert_eq!(hash1, hash2);
}

// =============================================================================
// Test: CallForest iteration (DFS order)
// =============================================================================

#[test]
fn test_call_forest_dfs_iteration() {
    let id = CellId::from_bytes([1u8; 32]);

    let make_action = |name: &str| Action {
        target: id,
        method: symbol(name),
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
    };

    let mut forest = CallForest::new();
    let root = forest.add_root(make_action("root"));
    let child1 = root.add_child(make_action("child1"));
    child1.add_child(make_action("grandchild1"));
    root.add_child(make_action("child2"));

    // DFS order: root, child1, grandchild1, child2.
    let methods: Vec<_> = forest
        .iter_dfs()
        .map(|t| t.action.method)
        .collect();

    assert_eq!(methods.len(), 4);
    assert_eq!(methods[0], symbol("root"));
    assert_eq!(methods[1], symbol("child1"));
    assert_eq!(methods[2], symbol("grandchild1"));
    assert_eq!(methods[3], symbol("child2"));
}

// =============================================================================
// Test: CallTree depth computation
// =============================================================================

#[test]
fn test_call_tree_depth() {
    let id = CellId::from_bytes([1u8; 32]);

    let make_action = || Action {
        target: id,
        method: symbol("op"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
    };

    let mut tree = CallTree::new(make_action());
    assert_eq!(tree.depth(), 0);

    tree.add_child(make_action());
    assert_eq!(tree.depth(), 1);

    tree.children[0].add_child(make_action());
    assert_eq!(tree.depth(), 2);
}

// =============================================================================
// Test: Empty forest rejected
// =============================================================================

#[test]
fn test_empty_forest_rejected() {
    let (mut ledger, agent_id, _) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest::new(),
        fee: 100,
        memo: None,
        valid_until: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    assert_eq!(error, TurnError::EmptyForest);
}

// =============================================================================
// Test: Agent cell not found
// =============================================================================

#[test]
fn test_agent_not_found() {
    let mut ledger = Ledger::new();
    let fake_agent = CellId::from_bytes([99u8; 32]);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(fake_agent, 0);
    {
        let action = builder.action(fake_agent, "op");
        action.authorize_signature([0u8; 64]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::CellNotFound { id } => assert_eq!(id, fake_agent),
        other => panic!("expected CellNotFound, got {other:?}"),
    }
}

// =============================================================================
// Test: Insufficient balance for fee
// =============================================================================

#[test]
fn test_insufficient_balance_for_fee() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(50, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    // Fee is 100 but agent only has 50.
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InsufficientBalance { cell, required, available } => {
            assert_eq!(cell, agent_id);
            assert_eq!(required, 100);
            assert_eq!(available, 50);
        }
        other => panic!("expected InsufficientBalance, got {other:?}"),
    }
}

// =============================================================================
// Test: CreateCell effect
// =============================================================================

#[test]
fn test_create_cell_effect() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let new_pk = [77u8; 32];
    let new_token = [88u8; 32];
    let new_id = CellId::derive_raw(&new_pk, &new_token);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "create");
        action.create_cell(new_pk, new_token, 100);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // New cell should exist.
    let new_cell = ledger.get(&new_id).unwrap();
    assert_eq!(new_cell.state.balance, 100);
    assert_eq!(new_cell.public_key, new_pk);
    assert_eq!(new_cell.token_id, new_token);
}

// =============================================================================
// Test: CreateCell duplicate rejected
// =============================================================================

#[test]
fn test_create_cell_duplicate_rejected() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // Try to create a cell with the same identity as the existing target.
    let target = ledger.get(&target_id).unwrap();
    let existing_pk = target.public_key;
    let existing_token = target.token_id;

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "create_dup");
        action.create_cell(existing_pk, existing_token, 100);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::CellAlreadyExists { .. } => {}
        other => panic!("expected CellAlreadyExists, got {other:?}"),
    }
}

// =============================================================================
// Test: GrantCapability and use it
// =============================================================================

#[test]
fn test_grant_and_use_capability() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target1, _) = make_open_cell(2, 0);
    let (target2, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target1_id = target1.id;
    let target2_id = target2.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target1_id, AuthRequired::None);
    agent_with_cap.capabilities.grant(target2_id, AuthRequired::None);

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target1).unwrap();
    ledger.insert_cell(target2).unwrap();

    let executor = zero_cost_executor();

    // First turn: grant target1 a capability to reach target2.
    let cap = CapabilityRef {
        target: target2_id,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
    };

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target1_id, "grant");
        action.grant_capability(agent_id, target1_id, cap.clone());
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Verify target1 now has a capability to target2.
    let t1 = ledger.get(&target1_id).unwrap();
    assert!(t1.capabilities.has_access(&target2_id));
}

// =============================================================================
// Test: RevokeCapability
// =============================================================================

#[test]
fn test_revoke_capability() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target, _) = make_open_cell(2, 0);
    let (other, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target_id = target.id;
    let other_id = other.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);

    // Target starts with a capability to other.
    let mut target_with_cap = target;
    let slot = target_with_cap.capabilities.grant(other_id, AuthRequired::None);

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target_with_cap).unwrap();
    ledger.insert_cell(other).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "revoke");
        action.revoke_capability(target_id, slot);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Target should no longer have capability to other.
    let t = ledger.get(&target_id).unwrap();
    assert!(!t.capabilities.has_access(&other_id));
}

// =============================================================================
// Test: Agent acting on itself (no capability needed)
// =============================================================================

#[test]
fn test_self_action_no_capability_needed() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "self_op");
        action.set_field(agent_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&agent_id).unwrap();
    assert_eq!(cell.state.fields[0], [99u8; 32]);
}

// =============================================================================
// Test: Multiple root actions in one turn
// =============================================================================

#[test]
fn test_multiple_root_actions() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 1000);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        // First root action: set field.
        let action1 = builder.action(target_id, "set_field");
        action1.set_field(target_id, 0, [1u8; 32]);
    }
    {
        // Second root action: transfer.
        let action2 = builder.action(agent_id, "transfer");
        action2.transfer(agent_id, target_id, 100);
    }
    {
        // Third root action: set another field.
        let action3 = builder.action(target_id, "set_field_2");
        action3.set_field(target_id, 1, [2u8; 32]);
    }
    let turn = builder.fee(500).build();

    assert_eq!(turn.action_count(), 3);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let target = ledger.get(&target_id).unwrap();
    assert_eq!(target.state.fields[0], [1u8; 32]);
    assert_eq!(target.state.fields[1], [2u8; 32]);
    assert_eq!(target.state.balance, 1100); // 1000 + 100 transfer
}

// =============================================================================
// Test: Computron cost estimation
// =============================================================================

#[test]
fn test_cost_estimation() {
    let agent_id = CellId::from_bytes([1u8; 32]);
    let target_id = CellId::from_bytes([2u8; 32]);
    let executor = default_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.authorize_signature([0u8; 64]);
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(10000).build();

    let estimated = executor.estimate_cost(&turn);
    assert!(estimated > 0);
    // action_base(100) + signature_verify(200) + effect_base(50) + data overhead
    assert!(estimated >= 350, "estimated = {estimated}");
}

// =============================================================================
// Test: validate_without_apply
// =============================================================================

#[test]
fn test_validate_without_apply() {
    let (ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // Valid turn.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(100).build();
    assert!(executor.validate_without_apply(&turn, &ledger).is_ok());

    // Invalid: wrong nonce.
    let mut builder2 = TurnBuilder::new(agent_id, 99);
    {
        let action = builder2.action(target_id, "op");
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn2 = builder2.fee(100).build();
    let err = executor.validate_without_apply(&turn2, &ledger).unwrap_err();
    assert!(matches!(err, TurnError::NonceReplay { .. }));
}

// =============================================================================
// Test: EmitEvent does not modify state
// =============================================================================

#[test]
fn test_emit_event_no_state_change() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let target_before = ledger.get(&target_id).unwrap().state.clone();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "emit");
        action.emit_event(target_id, "hello", vec![[42u8; 32]]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Target state should be unchanged (events don't modify state).
    let target_after = ledger.get(&target_id).unwrap().state.clone();
    assert_eq!(target_before.fields, target_after.fields);
    assert_eq!(target_before.nonce, target_after.nonce);
    assert_eq!(target_before.balance, target_after.balance);
}

// =============================================================================
// Test: IncrementNonce effect
// =============================================================================

#[test]
fn test_increment_nonce_effect() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    assert_eq!(ledger.get(&target_id).unwrap().state.nonce, 0);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "inc_nonce");
        action.increment_nonce(target_id);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    assert_eq!(ledger.get(&target_id).unwrap().state.nonce, 1);
}

// =============================================================================
// Test: Invalid field index
// =============================================================================

#[test]
fn test_invalid_field_index() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "bad_field");
        // STATE_SLOTS = 8, so index 99 is out of bounds.
        action.set_field(target_id, 99, [1u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidFieldIndex { index, .. } => {
            assert_eq!(index, 99);
        }
        other => panic!("expected InvalidFieldIndex, got {other:?}"),
    }
}

// =============================================================================
// Test: Transfer to non-existent cell
// =============================================================================

#[test]
fn test_transfer_to_nonexistent_cell() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();
    let fake_id = CellId::from_bytes([99u8; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "bad_transfer");
        action.transfer(agent_id, fake_id, 100);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::TransferDestNotFound { id } => {
            assert_eq!(id, fake_id);
        }
        other => panic!("expected TransferDestNotFound, got {other:?}"),
    }
}

// =============================================================================
// Test: Deep nesting (3 levels of children)
// =============================================================================

#[test]
fn test_deep_nesting() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let root = builder.action(target_id, "level0");
        root.set_field(target_id, 0, [0u8; 32]);
        root.delegation(DelegationMode::ParentsOwn);

        let l1 = root.child(target_id, "level1");
        l1.set_field(target_id, 1, [1u8; 32]);
        l1.delegation(DelegationMode::ParentsOwn);

        let l2 = l1.child(target_id, "level2");
        l2.set_field(target_id, 2, [2u8; 32]);
        l2.delegation(DelegationMode::ParentsOwn);

        let l3 = l2.child(target_id, "level3");
        l3.set_field(target_id, 3, [3u8; 32]);
    }
    let turn = builder.fee(500).build();

    assert_eq!(turn.call_forest.action_count(), 4);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], [0u8; 32]);
    assert_eq!(cell.state.fields[1], [1u8; 32]);
    assert_eq!(cell.state.fields[2], [2u8; 32]);
    assert_eq!(cell.state.fields[3], [3u8; 32]);
}

// =============================================================================
// Test: Sequential turns with incrementing nonces
// =============================================================================

#[test]
fn test_sequential_turns() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(50000, 0);
    let executor = zero_cost_executor();

    for i in 0..5u64 {
        let mut builder = TurnBuilder::new(agent_id, i);
        {
            let action = builder.action(target_id, "seq_op");
            let mut val = [0u8; 32];
            val[0] = i as u8;
            action.set_field(target_id, (i as usize) % STATE_SLOTS, val);
        }
        let turn = builder.fee(100).build();
        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_committed(), "turn {i} should commit");
    }

    // Agent nonce should be 5.
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(agent.state.nonce, 5);

    // Agent balance: 50000 - 5*100 = 49500.
    assert_eq!(agent.state.balance, 49500);
}

// =============================================================================
// Test: TurnBuilder with memo and valid_until
// =============================================================================

#[test]
fn test_builder_memo_and_valid_until() {
    let agent_id = CellId::from_bytes([1u8; 32]);
    let target_id = CellId::from_bytes([2u8; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "op");
        action.authorize_signature([0u8; 64]);
    }
    let turn = builder
        .fee(100)
        .memo("test memo")
        .valid_until(99999)
        .build();

    assert_eq!(turn.memo.as_deref(), Some("test memo"));
    assert_eq!(turn.valid_until, Some(99999));
    assert_eq!(turn.fee, 100);
    assert_eq!(turn.agent, agent_id);
    assert_eq!(turn.nonce, 0);
}

// =============================================================================
// Test: Forest total_effects collects all effects
// =============================================================================

#[test]
fn test_forest_total_effects() {
    let id = CellId::from_bytes([1u8; 32]);

    let action_with_effects = |n: usize| Action {
        target: id,
        method: symbol("op"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: (0..n)
            .map(|i| Effect::SetField { cell: id, index: i % STATE_SLOTS, value: [i as u8; 32] })
            .collect(),
        may_delegate: DelegationMode::None,
    };

    let mut forest = CallForest::new();
    let root = forest.add_root(action_with_effects(3));
    root.add_child(action_with_effects(2));
    forest.add_root(action_with_effects(1));

    let effects = forest.total_effects();
    assert_eq!(effects.len(), 6); // 3 + 2 + 1
}

// =============================================================================
// Test: AuthRequired::None allows Authorization::None
// =============================================================================

#[test]
fn test_auth_none_allows_none() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Target with all-None permissions.
    let (target, _) = make_open_cell(2, 0);
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "no_auth");
        // Authorization::None — no auth provided.
        action.set_field(target_id, 0, [42u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
}

// =============================================================================
// Test: Effect hash determinism
// =============================================================================

#[test]
fn test_effect_hash_determinism() {
    let id = CellId::from_bytes([1u8; 32]);

    let e1 = Effect::SetField { cell: id, index: 0, value: [42u8; 32] };
    let e2 = Effect::SetField { cell: id, index: 0, value: [42u8; 32] };
    let e3 = Effect::SetField { cell: id, index: 1, value: [42u8; 32] };

    assert_eq!(e1.hash(), e2.hash());
    assert_ne!(e1.hash(), e3.hash());
}

// =============================================================================
// Test: Action hash includes all fields
// =============================================================================

#[test]
fn test_action_hash_sensitivity() {
    let id = CellId::from_bytes([1u8; 32]);

    let base = Action {
        target: id,
        method: symbol("test"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
    };

    // Different method -> different hash.
    let different_method = Action {
        method: symbol("other"),
        ..base.clone()
    };
    assert_ne!(base.hash(), different_method.hash());

    // Different target -> different hash.
    let different_target = Action {
        target: CellId::from_bytes([2u8; 32]),
        ..base.clone()
    };
    assert_ne!(base.hash(), different_target.hash());

    // Different authorization -> different hash.
    let with_sig = Action {
        authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
        ..base.clone()
    };
    assert_ne!(base.hash(), with_sig.hash());

    // Different delegation -> different hash.
    let with_delegation = Action {
        may_delegate: DelegationMode::Inherit,
        ..base.clone()
    };
    assert_ne!(base.hash(), with_delegation.hash());
}

// =============================================================================
// Test: Precondition state field check
// =============================================================================

#[test]
fn test_precondition_field_equals() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // Set a field on target first.
    {
        let cell = ledger.get_mut(&target_id).unwrap();
        cell.state.fields[3] = [0xBB; 32];
    }

    // Now require that field[3] == [0xBB; 32] (should pass).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "check_field");
        action.require_field_equals(3, [0xBB; 32]);
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Now require field[3] == [0xCC; 32] (should fail).
    let mut builder2 = TurnBuilder::new(agent_id, 1);
    {
        let action = builder2.action(target_id, "check_field_bad");
        action.require_field_equals(3, [0xCC; 32]);
        action.set_field(target_id, 1, [2u8; 32]);
    }
    let turn2 = builder2.fee(100).build();

    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(result2.is_rejected());

    let (error, _) = result2.unwrap_rejected();
    match error {
        TurnError::PreconditionFailed { description } => {
            assert!(description.contains("FieldMismatch"), "got: {description}");
        }
        other => panic!("expected PreconditionFailed, got {other:?}"),
    }
}

// =============================================================================
// Test: Breadstuff authorization
// =============================================================================

#[test]
fn test_breadstuff_authorization() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Target with Signature-level auth requirement.
    let (mut target, _) = make_sig_cell(2, 0);
    let target_id = target.id;

    // The target has a capability with a matching breadstuff token.
    let token_hash = [0xAB; 32];
    target.capabilities.grant_with_breadstuff(
        agent_id,
        AuthRequired::None,
        Some(token_hash),
    );

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Use breadstuff authorization with the matching token.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "breadstuff_op");
        action.authorize_breadstuff(token_hash);
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let cell = ledger.get(&target_id).unwrap();
    assert_eq!(cell.state.fields[0], [99u8; 32]);
}

// =============================================================================
// Test: Breadstuff authorization fails with wrong token
// =============================================================================

#[test]
fn test_breadstuff_wrong_token_rejected() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_sig_cell(2, 0);
    let target_id = target.id;

    // Target has breadstuff [0xAB; 32], but we provide [0xCD; 32].
    target.capabilities.grant_with_breadstuff(
        agent_id,
        AuthRequired::None,
        Some([0xAB; 32]),
    );

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "breadstuff_bad");
        action.authorize_breadstuff([0xCD; 32]); // Wrong token!
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    assert!(matches!(error, TurnError::PermissionDenied { .. }));
}

// =============================================================================
// Test: LedgerDelta in committed result
// =============================================================================

#[test]
fn test_ledger_delta_in_result() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    let new_pk = [77u8; 32];
    let new_token = [88u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "ops");
        action.set_field(agent_id, 0, [42u8; 32]);
        action.create_cell(new_pk, new_token, 100);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    let (delta, receipt, _computrons) = result.unwrap_committed();

    // Delta should record the created cell.
    assert_eq!(delta.created.len(), 1);
    assert_eq!(delta.created[0].public_key, new_pk);

    // Delta should record the updated agent.
    assert!(!delta.updated.is_empty());

    // Receipt should have non-zero hashes.
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    assert_ne!(receipt.forest_hash, [0u8; 32]);
    assert_ne!(receipt.effects_hash, [0u8; 32]);
    assert_eq!(receipt.action_count, 1);
}

// =============================================================================
// Test: Frozen cell (Impossible permissions) rejects everything
// =============================================================================

#[test]
fn test_frozen_cell_rejects_all() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut frozen, _) = make_open_cell(2, 1000);
    frozen.permissions = Permissions::frozen();
    let frozen_id = frozen.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(frozen_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(frozen).unwrap();

    let executor = zero_cost_executor();

    // Try with no auth (permissions are Impossible regardless).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(frozen_id, "try_set");
        action.set_field(frozen_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { required, .. } => {
            assert_eq!(required, AuthRequired::Impossible);
        }
        other => panic!("expected PermissionDenied/Impossible, got {other:?}"),
    }
}

// =============================================================================
// Test: Receive permission blocks transfer to locked cell
// =============================================================================

#[test]
fn test_receive_permission_blocks_transfer() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Destination cell has receive = Impossible (frozen).
    let (mut dest, _) = make_open_cell(2, 0);
    dest.permissions.receive = AuthRequired::Impossible;
    let dest_id = dest.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(dest_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(dest).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "transfer_to_locked");
        action.transfer(agent_id, dest_id, 100);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { cell, action, required } => {
            assert_eq!(cell, dest_id);
            assert_eq!(action, "Receive");
            assert_eq!(required, AuthRequired::Impossible);
        }
        other => panic!("expected PermissionDenied for Receive, got {other:?}"),
    }
}

// =============================================================================
// Test: Receive permission — requires auth blocks transfer
// =============================================================================

#[test]
fn test_receive_permission_requires_auth_blocks_transfer() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Destination cell requires Signature to receive.
    let (mut dest, _) = make_open_cell(2, 0);
    dest.permissions.receive = AuthRequired::Signature;
    let dest_id = dest.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(dest_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(dest).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "transfer_to_sig_required");
        action.transfer(agent_id, dest_id, 100);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { cell, action, required } => {
            assert_eq!(cell, dest_id);
            assert_eq!(action, "Receive");
            assert_eq!(required, AuthRequired::Signature);
        }
        other => panic!("expected PermissionDenied for Receive, got {other:?}"),
    }
}

// =============================================================================
// Test: Mixed-effect action checks all permissions
// =============================================================================

#[test]
fn test_mixed_effects_all_permissions_checked() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Target: set_state = None (allowed), but send = Impossible.
    let (mut target, _) = make_open_cell(2, 1000);
    target.permissions.set_state = AuthRequired::None;
    target.permissions.send = AuthRequired::Impossible;
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Action has BOTH SetField (set_state=None) AND Transfer (send=Impossible).
    // The old code would only check the first matching effect. Now it should check all.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "mixed");
        action.set_field(target_id, 0, [1u8; 32]);
        action.transfer(target_id, agent_id, 100); // This should fail (send=Impossible).
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { required, .. } => {
            assert_eq!(required, AuthRequired::Impossible);
        }
        other => panic!("expected PermissionDenied/Impossible, got {other:?}"),
    }
}

// =============================================================================
// Test: Empty proof bytes rejected
// =============================================================================

#[test]
fn test_empty_proof_rejected() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![]); // Empty proof!
        action.set_field(target_id, 0, [99u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(reason.contains("empty"), "got: {reason}");
        }
        other => panic!("expected InvalidAuthorization, got {other:?}"),
    }
}

// =============================================================================
// Test: Authority amplification blocked — granter does not hold capability
// =============================================================================

#[test]
fn test_grant_capability_amplification_blocked() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target1, _) = make_open_cell(2, 0);
    let (target2, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target1_id = target1.id;
    let target2_id = target2.id;

    // Agent has capability to target1, but NOT to target2.
    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target1_id, AuthRequired::None);
    // Deliberately NOT granting capability to target2_id.

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target1).unwrap();
    ledger.insert_cell(target2).unwrap();

    let executor = zero_cost_executor();

    // Try to grant target1 a capability to target2, but agent doesn't hold it.
    // This is authority amplification and must be rejected.
    let cap = CapabilityRef {
        target: target2_id,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
    };

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target1_id, "amplify");
        action.grant_capability(agent_id, target1_id, cap);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::CapabilityNotHeld { actor, target } => {
            assert_eq!(actor, agent_id);
            assert_eq!(target, target2_id);
        }
        other => panic!("expected CapabilityNotHeld, got {other:?}"),
    }

    // Verify target1 did NOT gain the capability (atomicity).
    let t1 = ledger.get(&target1_id).unwrap();
    assert!(!t1.capabilities.has_access(&target2_id));
}

// =============================================================================
// Test: Authority amplification blocked — granted permissions wider than held
// =============================================================================

#[test]
fn test_grant_capability_attenuation_only() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target1, _) = make_open_cell(2, 0);
    let (target2, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target1_id = target1.id;
    let target2_id = target2.id;

    // Agent has capability to target1 and target2,
    // but the cap to target2 requires Signature.
    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target1_id, AuthRequired::None);
    agent_with_cap.capabilities.grant(target2_id, AuthRequired::Signature);

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target1).unwrap();
    ledger.insert_cell(target2).unwrap();

    let executor = zero_cost_executor();

    // Try to grant target1 a capability to target2 with AuthRequired::None.
    // Agent holds Signature-level, so granting None (less restrictive) is amplification.
    let cap = CapabilityRef {
        target: target2_id,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
    };

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target1_id, "amplify_perms");
        action.grant_capability(agent_id, target1_id, cap);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::DelegationDenied { parent, child_target } => {
            assert_eq!(parent, agent_id);
            assert_eq!(child_target, target1_id);
        }
        other => panic!("expected DelegationDenied, got {other:?}"),
    }
}

// =============================================================================
// Test: Attenuation succeeds — granted permissions are stricter than held
// =============================================================================

#[test]
fn test_grant_capability_attenuation_succeeds() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target1, _) = make_open_cell(2, 0);
    let (target2, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let target1_id = target1.id;
    let target2_id = target2.id;

    // Agent has capability to target1 and target2 with AuthRequired::None.
    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant(target1_id, AuthRequired::None);
    agent_with_cap.capabilities.grant(target2_id, AuthRequired::None);

    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target1).unwrap();
    ledger.insert_cell(target2).unwrap();

    let executor = zero_cost_executor();

    // Grant target1 a capability to target2, but with Signature requirement
    // (stricter than agent's None). This is valid attenuation.
    let cap = CapabilityRef {
        target: target2_id,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: None,
    };

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target1_id, "attenuate");
        action.grant_capability(agent_id, target1_id, cap);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Verify target1 gained the (attenuated) capability.
    let t1 = ledger.get(&target1_id).unwrap();
    assert!(t1.capabilities.has_access(&target2_id));
    let granted = t1.capabilities.lookup_by_target(&target2_id).unwrap();
    assert_eq!(granted.permissions, AuthRequired::Signature);
}
