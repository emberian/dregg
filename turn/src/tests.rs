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

use ed25519_dalek::{Signer, SigningKey, Verifier, VerifyingKey};
use pyana_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions, VerificationKey,
    preconditions::Preconditions as CellPreconditions,
    state::{FIELD_ZERO, STATE_SLOTS},
};

use crate::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use crate::builder::TurnBuilder;
use crate::composer::{ComposeError, SignedFragment, TurnComposer};
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
        TestKeypair {
            signing_key,
            public_key,
        }
    }

    /// Sign an action and return the Authorization.
    /// Uses the zero federation_id (matches executor default for tests).
    fn sign_action(&self, action: &Action) -> Authorization {
        let message = TurnExecutor::compute_signing_message(action, &[0u8; 32]);
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);

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
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
        true
    }
}

/// A test proof verifier that always rejects proofs.
struct AlwaysRejectVerifier;

impl ProofVerifier for AlwaysRejectVerifier {
    fn verify(&self, _proof: &[u8], _action: &str, _resource: &str, _vk: &[u8]) -> bool {
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysRejectVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    // No proof verifier configured.
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Build the action first to get the signing message, then sign it.
    let target_cell_id = target_id;
    let method = symbol("set_field");
    let effects = vec![Effect::SetField {
        cell: target_cell_id,
        index: 0,
        value: [42u8; 32],
    }];

    // Create the action to get the signing message.
    let unsigned_action = Action {
        target: target_cell_id,
        method,
        args: vec![],
        authorization: Authorization::Unchecked, // placeholder
        preconditions: CellPreconditions::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };
    let message = TurnExecutor::compute_signing_message(&unsigned_action, &[0u8; 32]);

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
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
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
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
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
                reason.contains("signature verification failed")
                    || reason.contains("not a valid Ed25519"),
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Sign with AGENT's key, but the TARGET's permissions check against TARGET's public key.
    let method = symbol("set_field");
    let effects = vec![Effect::SetField {
        cell: target_id,
        index: 0,
        value: [42u8; 32],
    }];
    let unsigned_action = Action {
        target: target_id,
        method,
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };
    let message = TurnExecutor::compute_signing_message(&unsigned_action, &[0u8; 32]);

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
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
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
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidAuthorization { reason } => {
            assert!(
                reason.contains("signature verification failed"),
                "got: {reason}"
            );
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
            assert!(
                description.contains("InsufficientBalance"),
                "got: {description}"
            );
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

    // Agent nonce IS incremented (fee+nonce commit is permanent, prevents DoS).
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(agent.state.nonce, 1);
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
    agent_with_caps
        .capabilities
        .grant(target1_id, AuthRequired::None);
    agent_with_caps
        .capabilities
        .grant(target2_id, AuthRequired::None);

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
        TurnError::DelegationDenied {
            parent,
            child_target,
        } => {
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
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
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
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let mut forest = CallForest::new();
    let root = forest.add_root(make_action("root"));
    let child1 = root.add_child(make_action("child1"));
    child1.add_child(make_action("grandchild1"));
    root.add_child(make_action("child2"));

    // DFS order: root, child1, grandchild1, child2.
    let methods: Vec<_> = forest.iter_dfs().map(|t| t.action.method).collect();

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
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
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
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
        TurnError::InsufficientBalance {
            cell,
            required,
            available,
        } => {
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
        action.create_cell(new_pk, new_token, 0);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // New cell should exist with zero balance.
    let new_cell = ledger.get(&new_id).unwrap();
    assert_eq!(new_cell.state.balance, 0);
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
        action.create_cell(existing_pk, existing_token, 0);
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
    agent_with_cap
        .capabilities
        .grant(target1_id, AuthRequired::None);
    agent_with_cap
        .capabilities
        .grant(target2_id, AuthRequired::None);

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
        expires_at: None,
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);

    // Target starts with a capability to other.
    let mut target_with_cap = target;
    let slot = target_with_cap
        .capabilities
        .grant(other_id, AuthRequired::None)
        .unwrap();

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
    let err = executor
        .validate_without_apply(&turn2, &ledger)
        .unwrap_err();
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
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: (0..n)
            .map(|i| Effect::SetField {
                cell: id,
                index: i % STATE_SLOTS,
                value: [i as u8; 32],
            })
            .collect(),
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let mut forest = CallForest::new();
    let root = forest.add_root(action_with_effects(3));
    root.add_child(action_with_effects(2));
    forest.add_root(action_with_effects(1));

    let effects = forest.total_effects();
    assert_eq!(effects.len(), 6); // 3 + 2 + 1
}

// =============================================================================
// Test: AuthRequired::None allows Authorization::Unchecked
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "no_auth");
        // Authorization::Unchecked — no auth provided.
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

    let e1 = Effect::SetField {
        cell: id,
        index: 0,
        value: [42u8; 32],
    };
    let e2 = Effect::SetField {
        cell: id,
        index: 0,
        value: [42u8; 32],
    };
    let e3 = Effect::SetField {
        cell: id,
        index: 1,
        value: [42u8; 32],
    };

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
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
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
    let (target, _) = make_sig_cell(2, 0);
    let target_id = target.id;

    // The actor holds a capability with a matching breadstuff token (targeting the target cell).
    let token_hash = [0xAB; 32];
    let mut agent_with_cap = agent;
    agent_with_cap.capabilities.grant_with_breadstuff(
        target_id,
        AuthRequired::None,
        Some(token_hash),
    );
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
    target
        .capabilities
        .grant_with_breadstuff(agent_id, AuthRequired::None, Some([0xAB; 32]));

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
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
        action.create_cell(new_pk, new_token, 0);
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
    agent_with_cap
        .capabilities
        .grant(frozen_id, AuthRequired::None);
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
    agent_with_cap
        .capabilities
        .grant(dest_id, AuthRequired::None);
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
        TurnError::PermissionDenied {
            cell,
            action,
            required,
        } => {
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
    agent_with_cap
        .capabilities
        .grant(dest_id, AuthRequired::None);
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
        TurnError::PermissionDenied {
            cell,
            action,
            required,
        } => {
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
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
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_state");
        action.authorize_proof(vec![], "", ""); // Empty proof!
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
    agent_with_cap
        .capabilities
        .grant(target1_id, AuthRequired::None);
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
        expires_at: None,
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
    agent_with_cap
        .capabilities
        .grant(target1_id, AuthRequired::None);
    agent_with_cap
        .capabilities
        .grant(target2_id, AuthRequired::Signature);

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
        expires_at: None,
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
        TurnError::DelegationDenied {
            parent,
            child_target,
        } => {
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
    agent_with_cap
        .capabilities
        .grant(target1_id, AuthRequired::None);
    agent_with_cap
        .capabilities
        .grant(target2_id, AuthRequired::None);

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
        expires_at: None,
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

// =============================================================================
// Multi-party composition tests
// =============================================================================

/// Helper: create a partial-commitment action and sign it for composition.
/// Uses zero federation_id and nonce=0 for test compatibility.
fn sign_partial_action(action: &Action, position: usize, signing_key: &SigningKey) -> [u8; 64] {
    let message = TurnExecutor::compute_partial_signing_message(action, position, &[0u8; 32], 0);
    let sig = signing_key.sign(&message);
    sig.to_bytes()
}

// =============================================================================
// Test: Partial commitment signature valid
// =============================================================================

#[test]
fn test_partial_commitment_signature_valid() {
    // Create a partial-commitment action, sign it, verify signature independently.
    let kp = TestKeypair::from_seed(10);
    let cell_id = CellId::from_bytes(kp.public_key);

    let action = Action {
        target: cell_id,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [42u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-100),
    };

    let position = 0;

    // Sign.
    let sig_bytes = sign_partial_action(&action, position, &kp.signing_key);

    // Verify manually.
    let message = TurnExecutor::compute_partial_signing_message(&action, position, &[0u8; 32], 0);
    let verifying_key: VerifyingKey = (&kp.signing_key).into();
    let signature = ed25519_dalek::Signature::from_bytes(&sig_bytes);
    assert!(verifying_key.verify(&message, &signature).is_ok());
}

// =============================================================================
// Test: Partial commitment independent of other actions
// =============================================================================

#[test]
fn test_partial_commitment_independent_of_other_actions() {
    // A partial commitment signature remains valid even when other actions in the
    // forest change, as long as the signer's action and position stay the same.
    let kp = TestKeypair::from_seed(11);
    let cell_id = CellId::from_bytes(kp.public_key);

    let action = Action {
        target: cell_id,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [1u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-50),
    };

    // Sign the action at position 0 (partial commitment = action hash + position only).
    let sig = sign_partial_action(&action, 0, &kp.signing_key);

    // The signing message only depends on action.hash() and position.
    // If we build a DIFFERENT forest (adding another action), the signature remains valid
    // because partial signers do NOT commit to the forest root.
    // The coordinator_signature on the composed turn provides the forest root binding.
    let message = TurnExecutor::compute_partial_signing_message(&action, 0, &[0u8; 32], 0);
    let verifying_key: VerifyingKey = (&kp.signing_key).into();
    let signature = ed25519_dalek::Signature::from_bytes(&sig);
    assert!(verifying_key.verify(&message, &signature).is_ok());

    // Verify that a full-commitment approach produces a DIFFERENT message:
    // The full signing message depends on the action's own content
    // (target, method, args, effects, delegation) but NOT position.
    let full_message = TurnExecutor::compute_signing_message(&action, &[0u8; 32]);
    // Full message is different from partial message (different hash construction).
    assert_ne!(full_message, message);
}

// =============================================================================
// Test: Full commitment invalidated by changes
// =============================================================================

#[test]
fn test_full_commitment_invalidated_by_changes() {
    // With full commitment, signing the action content means the signature is tied
    // to the action's exact state. Changing any field invalidates it.
    let kp = TestKeypair::from_seed(12);
    let cell_id = CellId::from_bytes(kp.public_key);

    let action = Action {
        target: cell_id,
        method: symbol("transfer"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![Effect::SetField {
            cell: cell_id,
            index: 0,
            value: [1u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    // Sign with full commitment message.
    let message = TurnExecutor::compute_signing_message(&action, &[0u8; 32]);
    let sig = kp.signing_key.sign(&message);

    // Verify: original action verifies.
    let verifying_key: VerifyingKey = (&kp.signing_key).into();
    assert!(verifying_key.verify(&message, &sig).is_ok());

    // Now modify the action (change effect value) and re-compute message.
    let mut modified = action.clone();
    modified.effects = vec![Effect::SetField {
        cell: cell_id,
        index: 0,
        value: [99u8; 32],
    }];
    let modified_message = TurnExecutor::compute_signing_message(&modified, &[0u8; 32]);

    // The original signature does NOT verify for the modified message.
    assert_ne!(message, modified_message);
    assert!(verifying_key.verify(&modified_message, &sig).is_err());
}

// =============================================================================
// Test: Compose two-party swap
// =============================================================================

#[test]
fn test_compose_two_party_swap() {
    let alice_kp = TestKeypair::from_seed(20);
    let bob_kp = TestKeypair::from_seed(21);
    let matcher_kp = TestKeypair::from_seed(22);

    let alice_cell = CellId::from_bytes(alice_kp.public_key);
    let bob_cell = CellId::from_bytes(bob_kp.public_key);
    let matcher_cell = CellId::from_bytes(matcher_kp.public_key);

    // Alice's action: withdraw 100 (balance_change = -100)
    let alice_action = Action {
        target: alice_cell,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked, // will be set after signing
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-100),
    };

    // Bob's action: withdraw 50 (balance_change = -50)
    let bob_action = Action {
        target: bob_cell,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-50),
    };

    // Settlement actions from the matcher (deposit into opposite parties):
    // Alice gets +50 (what Bob withdrew), Bob gets +100 (what Alice withdrew).
    let settle_alice = Action {
        target: alice_cell,
        method: symbol("deposit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: Some(50),
    };

    let settle_bob = Action {
        target: bob_cell,
        method: symbol("deposit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: Some(100),
    };

    // Alice signs her action at position 0 (partial: action hash + position only).
    let alice_sig = sign_partial_action(&alice_action, 0, &alice_kp.signing_key);

    // Bob signs his action at position 1.
    let bob_sig = sign_partial_action(&bob_action, 1, &bob_kp.signing_key);

    // Compose.
    let mut composer = TurnComposer::new(matcher_cell, 1000, 0);
    composer
        .add_fragment(SignedFragment {
            actions: vec![alice_action],
            signatures: vec![alice_sig],
            signer: alice_kp.public_key,
        })
        .unwrap();
    composer
        .add_fragment(SignedFragment {
            actions: vec![bob_action],
            signatures: vec![bob_sig],
            signer: bob_kp.public_key,
        })
        .unwrap();
    composer.add_settlement_action(settle_alice);
    composer.add_settlement_action(settle_bob);

    let composed = composer.compose().unwrap();

    // Verify turn structure.
    assert_eq!(composed.turn.agent, matcher_cell);
    assert_eq!(composed.turn.fee, 1000);
    assert_eq!(composed.turn.call_forest.action_count(), 4);
}

// =============================================================================
// Test: Compose rejects invalid signature
// =============================================================================

#[test]
fn test_compose_rejects_invalid_signature() {
    let alice_kp = TestKeypair::from_seed(30);
    let wrong_kp = TestKeypair::from_seed(31);
    let matcher_kp = TestKeypair::from_seed(32);

    let alice_cell = CellId::from_bytes(alice_kp.public_key);
    let matcher_cell = CellId::from_bytes(matcher_kp.public_key);

    let alice_action = Action {
        target: alice_cell,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-100),
    };

    let settle = Action {
        target: alice_cell,
        method: symbol("deposit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: Some(100),
    };

    // Sign with the WRONG key (not Alice's).
    let wrong_sig = sign_partial_action(&alice_action, 0, &wrong_kp.signing_key);

    let mut composer = TurnComposer::new(matcher_cell, 1000, 0);
    composer
        .add_fragment(SignedFragment {
            actions: vec![alice_action],
            signatures: vec![wrong_sig],
            signer: alice_kp.public_key, // claims to be Alice, but signed by wrong key
        })
        .unwrap();
    composer.add_settlement_action(settle);

    let result = composer.compose();
    assert!(result.is_err());
    match result.unwrap_err() {
        ComposeError::InvalidSignature {
            fragment_index,
            action_index,
            ..
        } => {
            assert_eq!(fragment_index, 0);
            assert_eq!(action_index, 0);
        }
        other => panic!("expected InvalidSignature, got {other:?}"),
    }
}

// =============================================================================
// Test: Compose validates excess balance (must sum to zero)
// =============================================================================

#[test]
fn test_compose_validates_excess_balance() {
    let alice_kp = TestKeypair::from_seed(40);
    let matcher_kp = TestKeypair::from_seed(41);

    let alice_cell = CellId::from_bytes(alice_kp.public_key);
    let matcher_cell = CellId::from_bytes(matcher_kp.public_key);

    // Alice withdraws 100 but there's no matching deposit (imbalanced).
    let alice_action = Action {
        target: alice_cell,
        method: symbol("withdraw"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: Some(-100),
    };

    let alice_sig = sign_partial_action(&alice_action, 0, &alice_kp.signing_key);

    let mut composer = TurnComposer::new(matcher_cell, 1000, 0);
    composer
        .add_fragment(SignedFragment {
            actions: vec![alice_action],
            signatures: vec![alice_sig],
            signer: alice_kp.public_key,
        })
        .unwrap();
    // No settlement action to balance the -100.

    let result = composer.compose();
    assert!(result.is_err());
    match result.unwrap_err() {
        ComposeError::ExcessImbalance { total_excess } => {
            assert_eq!(total_excess, -100);
        }
        other => panic!("expected ExcessImbalance, got {other:?}"),
    }
}

// =============================================================================
// Test: Fragment with Full commitment mode is rejected
// =============================================================================

#[test]
fn test_fragment_full_commitment_rejected() {
    let kp = TestKeypair::from_seed(50);
    let cell_id = CellId::from_bytes(kp.public_key);
    let matcher_cell = CellId::from_bytes([99u8; 32]);

    let action = Action {
        target: cell_id,
        method: symbol("op"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full, // Wrong! Should be Partial.
        balance_change: None,
    };

    let mut composer = TurnComposer::new(matcher_cell, 1000, 0);
    let result = composer.add_fragment(SignedFragment {
        actions: vec![action],
        signatures: vec![[0u8; 64]],
        signer: kp.public_key,
    });

    assert!(result.is_err());
    match result.unwrap_err() {
        ComposeError::FullCommitmentInFragment {
            fragment_index,
            action_index,
        } => {
            assert_eq!(fragment_index, 0);
            assert_eq!(action_index, 0);
        }
        other => panic!("expected FullCommitmentInFragment, got {other:?}"),
    }
}

// =============================================================================
// Test: Fragment signature count mismatch rejected
// =============================================================================

#[test]
fn test_fragment_signature_count_mismatch() {
    let kp = TestKeypair::from_seed(51);
    let cell_id = CellId::from_bytes(kp.public_key);
    let matcher_cell = CellId::from_bytes([99u8; 32]);

    let action = Action {
        target: cell_id,
        method: symbol("op"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: CellPreconditions::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Partial,
        balance_change: None,
    };

    let mut composer = TurnComposer::new(matcher_cell, 1000, 0);
    // One action but zero signatures.
    let result = composer.add_fragment(SignedFragment {
        actions: vec![action],
        signatures: vec![],
        signer: kp.public_key,
    });

    assert!(result.is_err());
    match result.unwrap_err() {
        ComposeError::SignatureCountMismatch {
            fragment_index,
            actions,
            signatures,
        } => {
            assert_eq!(fragment_index, 0);
            assert_eq!(actions, 1);
            assert_eq!(signatures, 0);
        }
        other => panic!("expected SignatureCountMismatch, got {other:?}"),
    }
}

// =============================================================================
// Tests: Cell program enforcement in executor
// =============================================================================

/// Helper: create a cell with a program and open permissions.
fn make_programmed_cell(seed: u8, balance: u64, program: pyana_cell::CellProgram) -> Cell {
    let kp = TestKeypair::from_seed(seed);
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(kp.public_key, token_id, balance);
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
    cell.program = program;
    cell
}

#[test]
fn test_program_predicate_gte_enforced() {
    // A cell with FieldGte(index=0, value=100) rejects transitions that set field[0] < 100.
    use pyana_cell::program::{StateConstraint, field_from_u64};

    let program = pyana_cell::CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(100),
    }]);

    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let target = make_programmed_cell(2, 0, program);
    let agent_id = agent.id;
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Try to set field[0] = 50 (violates FieldGte 100) -> should be rejected.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "bad_set");
        action.set_field(target_id, 0, field_from_u64(50));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "expected rejection for field < 100");
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::ProgramViolation { cell, .. } => {
            assert_eq!(cell, target_id);
        }
        other => panic!("expected ProgramViolation, got {other:?}"),
    }

    // Set field[0] = 200 (satisfies FieldGte 100) -> should succeed.
    // Nonce is now 1 because fee+nonce commit is permanent even on failure.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "good_set");
        action.set_field(target_id, 0, field_from_u64(200));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "expected success for field >= 100, got: {result:?}"
    );
}

#[test]
fn test_program_immutable_field_enforced() {
    // A cell with Immutable(index=1) rejects transitions that change field[1].
    use pyana_cell::program::{StateConstraint, field_from_u64};

    let program = pyana_cell::CellProgram::Predicate(vec![StateConstraint::Immutable { index: 1 }]);

    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let mut target = make_programmed_cell(2, 0, program);
    // Initialize field[1] with a value.
    target.state.fields[1] = field_from_u64(42);
    let agent_id = agent.id;
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Try to change field[1] -> should be rejected.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "mutate_immutable");
        action.set_field(target_id, 1, field_from_u64(99));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "expected rejection for mutating immutable field"
    );
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::ProgramViolation { cell, .. } => {
            assert_eq!(cell, target_id);
        }
        other => panic!("expected ProgramViolation, got {other:?}"),
    }

    // Changing field[0] (not immutable) should succeed.
    // Nonce is now 1 because fee+nonce commit is permanent even on failure.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "mutate_mutable");
        action.set_field(target_id, 0, field_from_u64(77));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "expected success for mutable field, got: {result:?}"
    );
}

#[test]
fn test_program_none_backward_compat() {
    // A cell with CellProgram::None works exactly as before.
    use pyana_cell::program::field_from_u64;

    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // Set any field to any value -> should succeed.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "set_field");
        action.set_field(target_id, 0, field_from_u64(999));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "CellProgram::None should allow any state change"
    );
}

#[test]
fn test_program_sum_conservation_enforced() {
    // SumEquals constraint enforces that fields[0] + fields[1] + fields[2] = 1000.
    use pyana_cell::program::{StateConstraint, field_from_u64};

    let program = pyana_cell::CellProgram::Predicate(vec![StateConstraint::SumEquals {
        indices: vec![0, 1, 2],
        value: field_from_u64(1000),
    }]);

    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let mut target = make_programmed_cell(2, 0, program);
    // Initialize to satisfy conservation: 500 + 300 + 200 = 1000.
    target.state.fields[0] = field_from_u64(500);
    target.state.fields[1] = field_from_u64(300);
    target.state.fields[2] = field_from_u64(200);
    let agent_id = agent.id;
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Violate conservation: set field[0] = 600 (600 + 300 + 200 = 1100 != 1000).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "bad_update");
        action.set_field(target_id, 0, field_from_u64(600));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "expected rejection for conservation violation"
    );

    // Maintain conservation: set field[0] = 400, field[1] = 400 (400 + 400 + 200 = 1000).
    // Nonce is now 1 because fee+nonce commit is permanent even on failure.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "good_update");
        action.set_field(target_id, 0, field_from_u64(400));
        action.set_field(target_id, 1, field_from_u64(400));
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "expected success for conserving sum, got: {result:?}"
    );
}

// =============================================================================
// Tests: Mina-style balance_change and excess tracking
// =============================================================================

/// Helper: create a ledger with three open cells (agent, cell_a, cell_b).
fn setup_three_open_cells(
    agent_balance: u64,
    a_balance: u64,
    b_balance: u64,
) -> (Ledger, CellId, CellId, CellId) {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, agent_balance);
    let (cell_a, _) = make_open_cell(2, a_balance);
    let (cell_b, _) = make_open_cell(3, b_balance);
    let agent_id = agent.id;
    let a_id = cell_a.id;
    let b_id = cell_b.id;

    let mut agent_with_caps = agent;
    agent_with_caps.capabilities.grant(a_id, AuthRequired::None);
    agent_with_caps.capabilities.grant(b_id, AuthRequired::None);

    ledger.insert_cell(agent_with_caps).unwrap();
    ledger.insert_cell(cell_a).unwrap();
    ledger.insert_cell(cell_b).unwrap();
    (ledger, agent_id, a_id, b_id)
}

// =============================================================================
// Test: Balanced transfer via excess — withdraw from A, deposit to B
// =============================================================================

#[test]
fn test_balanced_transfer_via_excess() {
    let (mut ledger, agent_id, a_id, b_id) = setup_three_open_cells(5000, 1000, 500);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        // Withdraw 200 from A (produces 200 excess).
        let action_a = builder.action(a_id, "withdraw");
        action_a.balance_change(-200);
    }
    {
        // Deposit 200 into B (consumes 200 excess).
        let action_b = builder.action(b_id, "deposit");
        action_b.balance_change(200);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "balanced excess should commit: {result:?}"
    );

    // A lost 200.
    let a = ledger.get(&a_id).unwrap();
    assert_eq!(a.state.balance, 800);

    // B gained 200.
    let b = ledger.get(&b_id).unwrap();
    assert_eq!(b.state.balance, 700);
}

// =============================================================================
// Test: Unbalanced excess rejected — withdraw without matching deposit
// =============================================================================

#[test]
fn test_unbalanced_excess_rejected() {
    let (mut ledger, agent_id, a_id, _b_id) = setup_three_open_cells(5000, 1000, 500);
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        // Withdraw 200 from A, but no matching deposit anywhere.
        let action_a = builder.action(a_id, "withdraw");
        action_a.balance_change(-200);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "unbalanced excess should be rejected");

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::ExcessNotZero { excess } => {
            // Withdrawal of 200 produces +200 excess (excess = -delta = -(-200) = 200).
            assert_eq!(excess, 200);
        }
        other => panic!("expected ExcessNotZero, got {other:?}"),
    }

    // A's balance should be unchanged (atomicity).
    let a = ledger.get(&a_id).unwrap();
    assert_eq!(a.state.balance, 1000);
}

// =============================================================================
// Test: Multiple sources, one sink — A withdraws 50, B withdraws 50, C deposits 100
// =============================================================================

#[test]
fn test_multiple_sources_one_sink() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (cell_a, _) = make_open_cell(2, 500);
    let (cell_b, _) = make_open_cell(3, 500);
    let (cell_c, _) = make_open_cell(4, 0);
    let agent_id = agent.id;
    let a_id = cell_a.id;
    let b_id = cell_b.id;
    let c_id = cell_c.id;

    let mut agent_with_caps = agent;
    agent_with_caps.capabilities.grant(a_id, AuthRequired::None);
    agent_with_caps.capabilities.grant(b_id, AuthRequired::None);
    agent_with_caps.capabilities.grant(c_id, AuthRequired::None);

    ledger.insert_cell(agent_with_caps).unwrap();
    ledger.insert_cell(cell_a).unwrap();
    ledger.insert_cell(cell_b).unwrap();
    ledger.insert_cell(cell_c).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder.action(a_id, "withdraw_a");
        action_a.balance_change(-50);
    }
    {
        let action_b = builder.action(b_id, "withdraw_b");
        action_b.balance_change(-50);
    }
    {
        let action_c = builder.action(c_id, "deposit_c");
        action_c.balance_change(100); // consumes the 100 total excess
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "multi-source single-sink should commit: {result:?}"
    );

    assert_eq!(ledger.get(&a_id).unwrap().state.balance, 450);
    assert_eq!(ledger.get(&b_id).unwrap().state.balance, 450);
    assert_eq!(ledger.get(&c_id).unwrap().state.balance, 100);
}

// =============================================================================
// Test: Proof circuit withdraw without destination — fails alone, succeeds composed
// =============================================================================

#[test]
fn test_proof_circuit_withdraw_without_destination() {
    let (mut ledger, agent_id, a_id, b_id) = setup_three_open_cells(5000, 1000, 0);
    let executor = zero_cost_executor();

    // First: a lone withdrawal should fail (excess not zero).
    {
        let mut builder = TurnBuilder::new(agent_id, 0);
        {
            let action_a = builder.action(a_id, "withdraw");
            action_a.balance_change(-100);
        }
        let turn = builder.fee(100).build();

        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_rejected(), "lone withdrawal should fail");
        let (error, _) = result.unwrap_rejected();
        assert!(matches!(error, TurnError::ExcessNotZero { excess: 100 }));
    }

    // Second: composed with a matching deposit, it succeeds.
    // Note: nonce is now 1 because Phase 1 (fee+nonce) is never rolled back.
    {
        let mut builder = TurnBuilder::new(agent_id, 1);
        {
            let action_a = builder.action(a_id, "withdraw");
            action_a.balance_change(-100);
        }
        {
            let action_b = builder.action(b_id, "deposit");
            action_b.balance_change(100);
        }
        let turn = builder.fee(100).build();

        let result = executor.execute(&turn, &mut ledger);
        assert!(
            result.is_committed(),
            "composed withdrawal+deposit should succeed: {result:?}"
        );

        assert_eq!(ledger.get(&a_id).unwrap().state.balance, 900);
        assert_eq!(ledger.get(&b_id).unwrap().state.balance, 100);
    }
}

// =============================================================================
// Test: Explicit Transfer effect still works (backward compatibility)
// =============================================================================

#[test]
fn test_explicit_transfer_still_works() {
    let (mut ledger, agent_id, a_id, b_id) = setup_three_open_cells(5000, 1000, 500);
    let executor = zero_cost_executor();

    // Use the old-style explicit Transfer effect (no balance_change).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(a_id, "transfer");
        action.transfer(a_id, b_id, 200);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "explicit transfer should still work: {result:?}"
    );

    assert_eq!(ledger.get(&a_id).unwrap().state.balance, 800);
    assert_eq!(ledger.get(&b_id).unwrap().state.balance, 700);
}

// =============================================================================
// Test: balance_change underflow rejected
// =============================================================================

#[test]
fn test_balance_change_underflow_rejected() {
    let (mut ledger, agent_id, a_id, _b_id) = setup_three_open_cells(5000, 100, 500);
    let executor = zero_cost_executor();

    // Try to withdraw 200 from A which only has 100.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder.action(a_id, "overdraw");
        action_a.balance_change(-200);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::BalanceChangeUnderflow {
            cell,
            current,
            delta,
        } => {
            assert_eq!(cell, a_id);
            assert_eq!(current, 100);
            assert_eq!(delta, -200);
        }
        other => panic!("expected BalanceChangeUnderflow, got {other:?}"),
    }

    // A's balance unchanged (atomicity).
    assert_eq!(ledger.get(&a_id).unwrap().state.balance, 100);
}

// =============================================================================
// Test: TurnBuilder.validate_excess catches imbalance before submission
// =============================================================================

#[test]
fn test_validate_excess_catches_imbalance() {
    let agent_id = CellId::from_bytes([1u8; 32]);
    let a_id = CellId::from_bytes([2u8; 32]);
    let b_id = CellId::from_bytes([3u8; 32]);

    // Balanced: should pass validation.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder.action(a_id, "withdraw");
        action_a.balance_change(-100);
    }
    {
        let action_b = builder.action(b_id, "deposit");
        action_b.balance_change(100);
    }
    builder.set_fee(100);
    assert!(builder.validate_excess().is_ok());

    // Unbalanced: should fail validation.
    let mut builder2 = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder2.action(a_id, "withdraw");
        action_a.balance_change(-100);
    }
    builder2.set_fee(100);
    let err = builder2.validate_excess().unwrap_err();
    match err {
        TurnError::ExcessNotZero { excess } => {
            assert_eq!(excess, 100);
        }
        other => panic!("expected ExcessNotZero, got {other:?}"),
    }
}

// =============================================================================
// Test: balance_change combined with explicit effects in same action
// =============================================================================

#[test]
fn test_balance_change_with_effects() {
    let (mut ledger, agent_id, a_id, b_id) = setup_three_open_cells(5000, 1000, 500);
    let executor = zero_cost_executor();

    // Action on A: withdraw 100 via balance_change AND set a state field.
    // Action on B: deposit 100 via balance_change.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder.action(a_id, "withdraw_and_mark");
        action_a.balance_change(-100);
        action_a.set_field(a_id, 0, [0xAA; 32]);
    }
    {
        let action_b = builder.action(b_id, "deposit");
        action_b.balance_change(100);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "balance_change with effects should commit: {result:?}"
    );

    let a = ledger.get(&a_id).unwrap();
    assert_eq!(a.state.balance, 900);
    assert_eq!(a.state.fields[0], [0xAA; 32]);

    let b = ledger.get(&b_id).unwrap();
    assert_eq!(b.state.balance, 600);
}

// =============================================================================
// Test: zero balance_change does not affect excess
// =============================================================================

#[test]
fn test_zero_balance_change_no_effect() {
    let (mut ledger, agent_id, a_id, _b_id) = setup_three_open_cells(5000, 1000, 500);
    let executor = zero_cost_executor();

    // A balance_change of 0 should be a no-op for excess.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action_a = builder.action(a_id, "noop");
        action_a.balance_change(0);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "zero balance_change should commit: {result:?}"
    );

    // Balance unchanged.
    assert_eq!(ledger.get(&a_id).unwrap().state.balance, 1000);
}

// =============================================================================
// Test: Two-phase fee — fee is charged even when turn fails
// =============================================================================

#[test]
fn test_fee_charged_on_failure() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 100);
    let executor = zero_cost_executor();

    let initial_agent_balance = ledger.get(&agent_id).unwrap().state.balance;
    let initial_agent_nonce = ledger.get(&agent_id).unwrap().state.nonce;

    // This turn will FAIL because it tries to transfer more than target has.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "bad_transfer");
        action.transfer(target_id, agent_id, 999_999); // impossible
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InsufficientBalance { .. } => {}
        other => panic!("expected InsufficientBalance, got {other:?}"),
    }

    // TWO-PHASE FEE COMMITMENT: Even though the turn failed, the fee is charged
    // and the nonce is incremented. This prevents DoS via expensive-but-failing turns.
    let agent = ledger.get(&agent_id).unwrap();
    assert_eq!(
        agent.state.balance,
        initial_agent_balance - 500,
        "fee must be charged even on failure"
    );
    assert_eq!(
        agent.state.nonce,
        initial_agent_nonce + 1,
        "nonce must increment even on failure"
    );

    // Target cell should be completely unaffected (Phase 2 rolled back).
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(
        target.state.balance, 100,
        "target balance must not change on failed turn"
    );
}

// =============================================================================
// Test: Permission change does not affect same action (Fix 2)
// =============================================================================

#[test]
fn test_permission_change_doesnt_affect_same_action() {
    // An action that SetPermissions to None (open) and also tries to transfer
    // from the same cell. The transfer should be checked against the ORIGINAL
    // permissions (which require Signature), not the weakened ones.
    //
    // Without Fix 2, an attacker could:
    //   1. SetPermissions { send: None } on the target
    //   2. Transfer from target (now allowed because send=None)
    // With Fix 2, permission effects are applied LAST, so step 2 is checked
    // against the ORIGINAL permissions.

    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    // Target has Signature required for send but open for set_permissions.
    let (mut target, _) = make_open_cell(2, 1000);
    target.permissions = pyana_cell::Permissions {
        send: AuthRequired::Signature,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = zero_cost_executor();

    // Try to SetPermissions (weakening send to None) and Transfer in the same action.
    // The Transfer should be checked against ORIGINAL permissions (send=Signature),
    // so it should be DENIED even though SetPermissions would weaken it.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "exploit_attempt");
        // First effect: weaken permissions.
        action.set_permissions(
            target_id,
            pyana_cell::Permissions {
                send: AuthRequired::None,
                receive: AuthRequired::None,
                set_state: AuthRequired::None,
                set_permissions: AuthRequired::None,
                set_verification_key: AuthRequired::None,
                increment_nonce: AuthRequired::None,
                delegate: AuthRequired::None,
                access: AuthRequired::None,
            },
        );
        // Second effect: try to exploit the weakened permissions.
        action.transfer(target_id, agent_id, 500);
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);

    // The turn should be REJECTED because the authorization check
    // (verify_authorization) checks ALL effects against the ORIGINAL permissions.
    // The action has a Transfer from target, which requires Send permission.
    // The ORIGINAL permissions require Signature for Send, but we have None auth.
    assert!(
        result.is_rejected(),
        "permission exploit should be blocked, got: {result:?}"
    );

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PermissionDenied { action, .. } => {
            assert_eq!(action, "Send", "should fail on Send permission check");
        }
        other => panic!("expected PermissionDenied for Send, got {other:?}"),
    }

    // Verify target balance is unchanged (transfer was blocked).
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(target.state.balance, 1000);

    // Verify permissions were NOT changed (entire action was rejected in Phase 2,
    // since verify_authorization fails before any effects are applied).
    assert_eq!(
        target.permissions.send,
        AuthRequired::Signature,
        "permissions must not be changed when action is rejected"
    );
}

// =============================================================================
// Test: proved_state set to true when all 8 fields set by proof authorization
// =============================================================================

#[test]
fn test_proved_state_set_by_proof() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    // Verify initial proved_state is false.
    assert!(!ledger.get(&target_id).unwrap().state.proved_state);

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Set ALL 8 fields with proof authorization.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "prove_all");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
        for i in 0..STATE_SLOTS {
            action.set_field(target_id, i, [(i + 1) as u8; 32]);
        }
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // proved_state should now be true.
    assert!(ledger.get(&target_id).unwrap().state.proved_state);
}

// =============================================================================
// Test: proved_state cleared to false by signature authorization
// =============================================================================

#[test]
fn test_proved_state_cleared_by_signature() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // First: set all 8 fields by proof -> proved_state = true.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "prove_all");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
        for i in 0..STATE_SLOTS {
            action.set_field(target_id, i, [(i + 1) as u8; 32]);
        }
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
    assert!(ledger.get(&target_id).unwrap().state.proved_state);

    // Now change permissions to allow None auth for set_state so we can test non-proof field set.
    ledger.get_mut(&target_id).unwrap().permissions.set_state = AuthRequired::None;

    // Second: set a field with no authorization (not proof) -> proved_state = false.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "non_proof_set");
        action.set_field(target_id, 0, [0xFF; 32]);
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // proved_state should now be false.
    assert!(!ledger.get(&target_id).unwrap().state.proved_state);
}

// =============================================================================
// Test: proved_state unchanged when no fields are modified
// =============================================================================

#[test]
fn test_proved_state_unchanged_when_no_fields_modified() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 500);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Set all 8 fields by proof -> proved_state = true.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "prove_all");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
        for i in 0..STATE_SLOTS {
            action.set_field(target_id, i, [(i + 1) as u8; 32]);
        }
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
    assert!(ledger.get(&target_id).unwrap().state.proved_state);

    // Now perform an action that doesn't touch any fields (just emit an event).
    // This should NOT clear proved_state.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "emit_only");
        action.authorize_proof(vec![5, 6, 7, 8], "", "");
        action.emit_event(target_id, "hello", vec![[42u8; 32]]);
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // proved_state should still be true (no fields modified).
    assert!(ledger.get(&target_id).unwrap().state.proved_state);
}

// =============================================================================
// Test: precondition proved_state = true passes when true
// =============================================================================

#[test]
fn test_precondition_proved_state_true() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Set all 8 fields by proof -> proved_state = true.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "prove_all");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
        for i in 0..STATE_SLOTS {
            action.set_field(target_id, i, [(i + 1) as u8; 32]);
        }
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Now use a precondition that asserts proved_state = true.
    let mut builder = TurnBuilder::new(agent_id, 1);
    {
        let action = builder.action(target_id, "check_proved");
        action.authorize_proof(vec![9, 10], "", "");
        action.require_proved_state(true);
        action.emit_event(target_id, "checked", vec![]);
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
}

// =============================================================================
// Test: precondition proved_state = true fails when false
// =============================================================================

#[test]
fn test_precondition_proved_state_false_rejects() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(5000, 0);
    let executor = zero_cost_executor();

    // proved_state starts as false for a new cell.
    assert!(!ledger.get(&target_id).unwrap().state.proved_state);

    // Use a precondition that asserts proved_state = true (should fail).
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "check_proved");
        action.require_proved_state(true);
        action.set_field(target_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(500).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::PreconditionFailed { description } => {
            assert!(
                description.contains("ProvedStateMismatch"),
                "got: {description}"
            );
        }
        other => panic!("expected PreconditionFailed, got {other:?}"),
    }
}

// =============================================================================
// Test: partial proof fields (< 8) does not set proved_state
// =============================================================================

#[test]
fn test_partial_proof_fields_doesnt_set_proved() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let agent_id = agent.id;

    let (mut target, _) = make_open_cell(2, 0);
    target.permissions = Permissions::zkapp();
    target.verification_key = Some(VerificationKey::new(vec![1, 2, 3, 4]));
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Set only 3 out of 8 fields with proof authorization.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(target_id, "partial_prove");
        action.authorize_proof(vec![1, 2, 3, 4], "", "");
        action.set_field(target_id, 0, [10u8; 32]);
        action.set_field(target_id, 1, [20u8; 32]);
        action.set_field(target_id, 2, [30u8; 32]);
    }
    let turn = builder.fee(500).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // proved_state should still be false (only 3/8 fields set).
    assert!(!ledger.get(&target_id).unwrap().state.proved_state);
}

// =============================================================================
// Note layer tests
// =============================================================================

#[test]
fn test_note_spend_and_create_conservation() {
    // Spend 100, create 60 + 40 = valid.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let nullifier = pyana_cell::Nullifier([0xAA; 32]);
    let commitment1 = pyana_cell::NoteCommitment([0xBB; 32]);
    let commitment2 = pyana_cell::NoteCommitment([0xCC; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "note_transfer");
        action.effect(Effect::NoteSpend {
            nullifier,
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: commitment1,
            value: 60,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: commitment2,
            value: 40,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "conservation-valid note turn should commit"
    );
}

#[test]
fn test_note_conservation_violated() {
    // Spend 100, create 200 = rejected.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let nullifier = pyana_cell::Nullifier([0xAA; 32]);
    let commitment = pyana_cell::NoteCommitment([0xBB; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "note_inflate");
        action.effect(Effect::NoteSpend {
            nullifier,
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment,
            value: 200,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(
                    reason,
                    TurnError::NoteConservationViolation {
                        asset_type: 1,
                        inputs: 100,
                        outputs: 200
                    }
                ),
                "expected NoteConservationViolation, got: {reason:?}"
            );
        }
        _ => panic!("expected rejection for conservation violation"),
    }
}

#[test]
fn test_note_nft_transfer() {
    // NFT transfer: spend a note with value=0 (NFT), create a note with value=0.
    // Conservation: 0 == 0 for both asset types.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let unique_asset_id: u64 = 0xDEAD_BEEF;
    let nullifier = pyana_cell::Nullifier([0xAA; 32]);
    let commitment = pyana_cell::NoteCommitment([0xBB; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "nft_transfer");
        // Spend the NFT note (value=0 for NFTs, asset_type is the unique ID).
        action.effect(Effect::NoteSpend {
            nullifier,
            note_tree_root: [0xFFu8; 32],
            value: 0,
            asset_type: unique_asset_id,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        // Create a new note for the recipient (same asset_type, value=0).
        action.effect(Effect::NoteCreate {
            commitment,
            value: 0,
            asset_type: unique_asset_id,
            encrypted_note: vec![1, 2, 3], // encrypted for recipient
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "NFT transfer should commit (0==0 conservation)"
    );
}

#[test]
fn test_note_multiple_asset_types_conservation() {
    // Spend asset_type=1 (100) + asset_type=2 (50).
    // Create asset_type=1 (100) + asset_type=2 (50).
    // Should pass.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "multi_asset");
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([1u8; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([2u8; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 50,
            asset_type: 2,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([3u8; 32]),
            value: 100,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([4u8; 32]),
            value: 50,
            asset_type: 2,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "multi-asset conservation should pass"
    );
}

#[test]
fn test_note_cross_asset_conservation_fails() {
    // Spend asset_type=1 (100), create asset_type=2 (100).
    // Should fail: each asset type must independently conserve.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "cross_asset_cheat");
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([1u8; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([2u8; 32]),
            value: 100,
            asset_type: 2, // different asset type!
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            // Either asset 1 or asset 2 conservation will fail.
            assert!(
                matches!(reason, TurnError::NoteConservationViolation { .. }),
                "expected NoteConservationViolation, got: {reason:?}"
            );
        }
        _ => panic!("expected rejection for cross-asset conservation violation"),
    }
}

// =============================================================================
// NoteSpend proof verification tests
// =============================================================================

#[test]
fn test_note_spend_rejected_without_proof() {
    // NoteSpend with empty spending_proof must be rejected.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "note_spend_no_proof");
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([0xAA; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![], // empty = missing
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([0xBB; 32]),
            value: 100,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(reason, TurnError::InvalidEffect { ref reason } if reason.contains("missing spending proof")),
                "expected missing proof error, got: {reason:?}"
            );
        }
        _ => panic!("expected rejection for NoteSpend without proof"),
    }
}

#[test]
fn test_note_spend_rejected_with_invalid_proof() {
    // NoteSpend with a proof that fails verification must be rejected.
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_proof_verifier(Box::new(AlwaysRejectVerifier));

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "note_spend_bad_proof");
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([0xAA; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0xDE, 0xAD, 0xBE, 0xEF], // garbage proof
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([0xBB; 32]),
            value: 100,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(reason, TurnError::InvalidEffect { ref reason } if reason.contains("verification failed")),
                "expected proof verification failure, got: {reason:?}"
            );
        }
        _ => panic!("expected rejection for NoteSpend with invalid proof"),
    }
}

#[test]
fn test_note_spend_rejected_without_verifier() {
    // NoteSpend when no proof verifier is configured must be rejected (fail-closed).
    let kp = TestKeypair::from_seed(1);
    let mut ledger = Ledger::new();
    let agent = Cell::with_balance(kp.public_key, [0u8; 32], 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    // No proof verifier set (fail-closed behavior).
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "note_spend_no_verifier");
        action.effect(Effect::NoteSpend {
            nullifier: pyana_cell::Nullifier([0xAA; 32]),
            note_tree_root: [0xFFu8; 32],
            value: 100,
            asset_type: 1,
            spending_proof: vec![0x01, 0x02, 0x03],
            value_commitment: None,
        });
        action.effect(Effect::NoteCreate {
            commitment: pyana_cell::NoteCommitment([0xBB; 32]),
            value: 100,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: None,
            range_proof: None,
        });
    }
    let turn = builder.fee(10000).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(reason, TurnError::InvalidEffect { ref reason } if reason.contains("no proof verifier")),
                "expected no-verifier error, got: {reason:?}"
            );
        }
        _ => panic!("expected rejection for NoteSpend without configured verifier"),
    }
}

// =============================================================================
// Tests: Three-Party Introduction (Effect::Introduce)
// === Three-Party Introduction Tests ===
fn setup_three_cells_for_introduction() -> (Ledger, CellId, CellId, CellId) {
    let mut ledger = Ledger::new();
    let (alice, _) = make_open_cell(10, 10000);
    let (bob, _) = make_open_cell(20, 1000);
    let (carol, _) = make_open_cell(30, 1000);
    let alice_id = alice.id;
    let bob_id = bob.id;
    let carol_id = carol.id;
    let mut alice_with_caps = alice;
    alice_with_caps
        .capabilities
        .grant(bob_id, AuthRequired::None);
    alice_with_caps
        .capabilities
        .grant(carol_id, AuthRequired::None);
    ledger.insert_cell(alice_with_caps).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    (ledger, alice_id, bob_id, carol_id)
}
#[test]
fn test_introduction_basic_success() {
    let (mut ledger, alice_id, bob_id, carol_id) = setup_three_cells_for_introduction();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "introduction should succeed");
    let bob = ledger.get(&bob_id).unwrap();
    assert!(bob.capabilities.has_access(&carol_id));
    let (_, receipt, _) = result.unwrap_committed();
    assert_eq!(receipt.routing_directives.len(), 1);
    assert_eq!(receipt.routing_directives[0].sender, bob_id);
    assert_eq!(receipt.routing_directives[0].target, carol_id);
}
#[test]
fn test_introduction_fails_without_cap_to_target() {
    let mut ledger = Ledger::new();
    let (alice, _) = make_open_cell(10, 10000);
    let (bob, _) = make_open_cell(20, 1000);
    let (carol, _) = make_open_cell(30, 1000);
    let alice_id = alice.id;
    let bob_id = bob.id;
    let carol_id = carol.id;
    let mut a = alice;
    a.capabilities.grant(bob_id, AuthRequired::None);
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::IntroductionDenied { reason, .. } => {
            assert!(reason.contains("no capability to target"));
        }
        other => panic!("expected IntroductionDenied, got: {:?}", other),
    }
}
#[test]
fn test_introduction_fails_without_cap_to_recipient() {
    let mut ledger = Ledger::new();
    let (alice, _) = make_open_cell(10, 10000);
    let (bob, _) = make_open_cell(20, 1000);
    let (carol, _) = make_open_cell(30, 1000);
    let alice_id = alice.id;
    let bob_id = bob.id;
    let carol_id = carol.id;
    let mut a = alice;
    a.capabilities.grant(carol_id, AuthRequired::None);
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::IntroductionDenied { reason, .. } => {
            assert!(reason.contains("no capability to recipient"));
        }
        other => panic!("expected IntroductionDenied, got: {:?}", other),
    }
}
#[test]
fn test_introduction_fails_with_amplification() {
    let mut ledger = Ledger::new();
    let (alice, _) = make_open_cell(10, 10000);
    let (bob, _) = make_open_cell(20, 1000);
    let (carol, _) = make_open_cell(30, 1000);
    let alice_id = alice.id;
    let bob_id = bob.id;
    let carol_id = carol.id;
    let mut a = alice;
    a.capabilities.grant(bob_id, AuthRequired::None);
    a.capabilities.grant(carol_id, AuthRequired::Signature);
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::IntroductionDenied { reason, .. } => {
            assert!(reason.contains("amplification denied"));
        }
        other => panic!("expected IntroductionDenied, got: {:?}", other),
    }
}
#[test]
fn test_introduction_routing_directive_hash() {
    let (mut ledger, alice_id, bob_id, carol_id) = setup_three_cells_for_introduction();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::None);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    let (_, receipt, _) = result.unwrap_committed();
    let directive = &receipt.routing_directives[0];
    assert_ne!(directive.hash(), [0u8; 32]);
    assert_eq!(directive.authorizing_turn, receipt.turn_hash);
}
#[test]
fn test_introduction_attenuation_preserves_level() {
    let (mut ledger, alice_id, bob_id, carol_id) = setup_three_cells_for_introduction();
    let executor = zero_cost_executor();
    let mut builder = TurnBuilder::new(alice_id, 0);
    {
        let action = builder.action(alice_id, "introduce");
        action.introduce(alice_id, bob_id, carol_id, AuthRequired::Signature);
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
    let bob = ledger.get(&bob_id).unwrap();
    let cap = bob.capabilities.lookup_by_target(&carol_id).unwrap();
    assert_eq!(cap.permissions, AuthRequired::Signature);
}

// =============================================================================
// Tests: BudgetGate integration (Stingray bounded counter)
// =============================================================================

use crate::budget_gate::{BudgetGate, BudgetSlice};

/// Helper: build a simple noop turn with a given fee using TurnBuilder.
/// Uses SetField effect (doesn't add extra nonce increments beyond the Phase 1 commitment).
fn make_noop_turn_with_fee(agent_id: CellId, nonce: u64, fee: u64) -> Turn {
    let mut builder = TurnBuilder::new(agent_id, nonce);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [0u8; 32]);
    }
    builder.fee(fee).build()
}

#[test]
fn test_budget_gate_turn_within_budget_succeeds() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100_000, 0);

    // Budget slice with 10_000 ceiling — more than enough for one turn.
    let slice = BudgetSlice::new(10_000);
    let gate = BudgetGate::new(1, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::zero(), gate);

    let turn = make_noop_turn_with_fee(agent_id, 0, 500);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Verify the slice was debited.
    let gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate_ref.slice.spent, 500);
    assert_eq!(gate_ref.slice.remaining(), 9_500);
    assert_eq!(gate_ref.slice.debits.len(), 1);
}

#[test]
fn test_budget_gate_turn_exceeding_slice_rejected() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100_000, 0);

    // Budget slice with only 100 ceiling — less than the turn fee.
    let slice = BudgetSlice::new(100);
    let gate = BudgetGate::new(42, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::zero(), gate);

    let turn = make_noop_turn_with_fee(agent_id, 0, 500);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::BudgetExhausted {
            silo_id,
            requested,
            remaining,
        } => {
            assert_eq!(silo_id, 42);
            assert_eq!(requested, 500);
            assert_eq!(remaining, 100);
        }
        other => panic!("expected BudgetExhausted, got: {other}"),
    }

    // Verify the slice was NOT debited (rejected before debit).
    let gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate_ref.slice.spent, 0);
    assert_eq!(gate_ref.slice.remaining(), 100);
}

#[test]
fn test_budget_gate_multiple_turns_deplete_slice() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100_000, 0);

    // Budget slice with 1000 ceiling.
    let slice = BudgetSlice::new(1000);
    let gate = BudgetGate::new(1, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::zero(), gate);

    // Execute 4 turns of fee=200 each (total 800, within budget).
    for i in 0..4u64 {
        let turn = make_noop_turn_with_fee(agent_id, i, 200);
        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_committed(), "turn {i} should succeed");
    }

    // Verify progressive depletion.
    {
        let gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
        assert_eq!(gate_ref.slice.spent, 800);
        assert_eq!(gate_ref.slice.remaining(), 200);
        assert_eq!(gate_ref.slice.debits.len(), 4);
    }

    // 5th turn of fee=300 exceeds remaining (200).
    let turn = make_noop_turn_with_fee(agent_id, 4, 300);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());
    match result.unwrap_rejected().0 {
        TurnError::BudgetExhausted { remaining: 200, .. } => {}
        other => panic!("expected BudgetExhausted with remaining=200, got: {other}"),
    }
}

#[test]
fn test_budget_gate_refund_on_turn_failure() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(100_000, 0);

    // Budget slice with 5000 ceiling.
    let slice = BudgetSlice::new(5000);
    let gate = BudgetGate::new(1, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::default_costs(), gate);

    // Create a turn that will fail during execution (transfer more than available on target).
    // The fee is within budget, but the turn fails for a different reason.
    // Use a turn with fee=1000 that tries to transfer from target cell which has 0 balance.
    let mut forest = CallForest::new();
    let action = Action {
        target: target_id,
        method: symbol("transfer"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: target_id,
            to: agent_id,
            amount: 999_999, // Target has 0 balance -- will fail
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };
    forest.add_root(action);
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 1000,
        memo: None,
        valid_until: None,
        depends_on: vec![],
        conservation_proof: None,
        previous_receipt_hash: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    // The budget debit should have been refunded (fast unlock).
    let gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate_ref.slice.spent, 0);
    assert_eq!(gate_ref.slice.remaining(), 5000);
    assert_eq!(gate_ref.slice.debits.len(), 0);
}

#[test]
fn test_budget_gate_fresh_slice_after_rebalance() {
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100_000, 0);

    // Start with a small slice that gets exhausted.
    let slice = BudgetSlice::new(500);
    let gate = BudgetGate::new(1, slice);
    let executor = TurnExecutor::with_budget_gate(ComputronCosts::zero(), gate);

    // First turn exhausts most of the slice.
    let turn = make_noop_turn_with_fee(agent_id, 0, 400);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Next turn with fee=200 would exceed remaining (100).
    let turn = make_noop_turn_with_fee(agent_id, 1, 200);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    // Simulate rebalance: replace the slice with a fresh one.
    {
        let mut gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
        gate_ref.slice = BudgetSlice::new(2000); // Fresh slice from coordinator
    }

    // Now the same turn succeeds with the fresh slice.
    let turn = make_noop_turn_with_fee(agent_id, 1, 200);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Verify new slice state.
    let gate_ref = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate_ref.slice.spent, 200);
    assert_eq!(gate_ref.slice.remaining(), 1800);
}

#[test]
fn test_budget_gate_none_allows_all_turns() {
    // Without a budget gate, all turns execute normally (backward compatible).
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100_000, 0);
    let executor = TurnExecutor::new(ComputronCosts::zero());

    for i in 0..10u64 {
        let turn = make_noop_turn_with_fee(agent_id, i, 1000);
        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_committed());
    }

    // No budget gate means no budget checking.
    assert!(executor.budget_gate.is_none());
}

// =============================================================================
// Tests: Snapshot+Refresh Delegation
// =============================================================================

#[test]
fn test_spawn_with_delegation_child_gets_parent_caps() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    // Give parent capabilities to target cells.
    let (target_a, _) = make_open_cell(10, 0);
    let (target_b, _) = make_open_cell(11, 0);
    let (target_c, _) = make_open_cell(12, 0);
    let target_a_id = target_a.id;
    let target_b_id = target_b.id;
    let target_c_id = target_c.id;

    parent.capabilities.grant(target_a_id, AuthRequired::None);
    parent.capabilities.grant(target_b_id, AuthRequired::None);
    parent.capabilities.grant(target_c_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target_a).unwrap();
    ledger.insert_cell(target_b).unwrap();
    ledger.insert_cell(target_c).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    // Build turn that spawns child with delegation.
    let action = Action {
        target: parent_id,
        method: symbol("spawn_delegated"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(action);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "turn should commit: {:?}", result);

    // Verify the child cell was created with delegation snapshot.
    let child = ledger.get(&child_id).expect("child should exist");
    assert_eq!(child.delegate, Some(parent_id));
    let delegation = child
        .delegation
        .as_ref()
        .expect("child should have delegation");
    assert_eq!(delegation.source, parent_id);
    assert_eq!(delegation.snapshot.len(), 3);
    assert_eq!(delegation.max_staleness, 300);
    assert_eq!(delegation.refreshed_at, 1000);
    assert_eq!(delegation.delegation_epoch, 0);

    // Child can see all 3 parent capabilities.
    assert!(delegation.has_capability(&target_a_id));
    assert!(delegation.has_capability(&target_b_id));
    assert!(delegation.has_capability(&target_c_id));
}

#[test]
fn test_child_acts_via_delegated_caps() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    let (target, _) = make_open_cell(10, 0);
    let target_id = target.id;
    parent.capabilities.grant(target_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    // Spawn child with delegation.
    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    let spawn_action = Action {
        target: parent_id,
        method: symbol("spawn"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn1 = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(spawn_action);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn1, &mut ledger);
    assert!(result.is_committed());

    // Now child acts on target using delegated capability.
    ledger.get_mut(&child_id).unwrap().state.balance = 100_000;

    let value = [99u8; 32];
    let child_action = Action {
        target: target_id,
        method: symbol("set_field"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn2 = Turn {
        agent: child_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(child_action);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn2, &mut ledger);
    assert!(
        result.is_committed(),
        "child should act via delegation: {:?}",
        result
    );

    // Verify the field was set.
    let target_cell = ledger.get(&target_id).unwrap();
    assert_eq!(target_cell.state.fields[0], value);
}

#[test]
fn test_refresh_delegation_updates_snapshot() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    let (target_a, _) = make_open_cell(10, 0);
    let target_a_id = target_a.id;
    parent.capabilities.grant(target_a_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target_a).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    // Spawn child with delegation (parent has 1 cap).
    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    let spawn = Action {
        target: parent_id,
        method: symbol("spawn"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn1 = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(spawn);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    executor.execute(&turn1, &mut ledger);

    // Parent gains a new capability.
    let (target_b, _) = make_open_cell(11, 0);
    let target_b_id = target_b.id;
    ledger.insert_cell(target_b).unwrap();
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .grant(target_b_id, AuthRequired::None);

    // Child doesn't have target_b yet.
    let child = ledger.get(&child_id).unwrap();
    assert!(
        !child
            .delegation
            .as_ref()
            .unwrap()
            .has_capability(&target_b_id)
    );

    // Child refreshes delegation.
    ledger.get_mut(&child_id).unwrap().state.balance = 100_000;
    executor.set_timestamp(2000);

    let refresh = Action {
        target: child_id,
        method: symbol("refresh"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::RefreshDelegation],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn2 = Turn {
        agent: child_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(refresh);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn2, &mut ledger);
    assert!(result.is_committed(), "refresh should work: {:?}", result);

    // Now child has target_b in snapshot.
    let child = ledger.get(&child_id).unwrap();
    let delegation = child.delegation.as_ref().unwrap();
    assert!(delegation.has_capability(&target_a_id));
    assert!(delegation.has_capability(&target_b_id));
    assert_eq!(delegation.snapshot.len(), 2);
    assert_eq!(delegation.refreshed_at, 2000);
}

#[test]
fn test_revoke_delegation_bumps_epoch_and_clears_child() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    let (target, _) = make_open_cell(10, 0);
    let target_id = target.id;
    parent.capabilities.grant(target_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    // Spawn child.
    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    let spawn = Action {
        target: parent_id,
        method: symbol("spawn"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn1 = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(spawn);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    executor.execute(&turn1, &mut ledger);

    // Verify child has delegation.
    assert!(ledger.get(&child_id).unwrap().delegation.is_some());
    assert_eq!(ledger.get(&parent_id).unwrap().state.delegation_epoch, 0);

    // Parent needs capability to child for RevokeDelegation effect.
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .grant(child_id, AuthRequired::None);

    // Parent revokes delegation.
    let revoke = Action {
        target: parent_id,
        method: symbol("revoke"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::RevokeDelegation { child: child_id }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn2 = Turn {
        agent: parent_id,
        nonce: 1,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(revoke);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn2, &mut ledger);
    assert!(result.is_committed(), "revoke should work: {:?}", result);

    // Parent's epoch bumped.
    assert_eq!(ledger.get(&parent_id).unwrap().state.delegation_epoch, 1);
    // Child's delegation is cleared.
    assert!(ledger.get(&child_id).unwrap().delegation.is_none());
}

#[test]
fn test_parent_new_cap_invisible_until_refresh() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    let (target_a, _) = make_open_cell(10, 0);
    let target_a_id = target_a.id;
    parent.capabilities.grant(target_a_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target_a).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    // Spawn child.
    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    let spawn = Action {
        target: parent_id,
        method: symbol("spawn"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn1 = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(spawn);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    executor.execute(&turn1, &mut ledger);

    // Parent gains new cap to target_b.
    let (target_b, _) = make_open_cell(11, 0);
    let target_b_id = target_b.id;
    ledger.insert_cell(target_b).unwrap();
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .grant(target_b_id, AuthRequired::None);

    // Child tries to use target_b via delegation — should fail.
    ledger.get_mut(&child_id).unwrap().state.balance = 100_000;

    let child_action = Action {
        target: target_b_id,
        method: symbol("use"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn2 = Turn {
        agent: child_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(child_action);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn2, &mut ledger);
    assert!(
        !result.is_committed(),
        "child should NOT access target_b without refresh"
    );
}

#[test]
fn test_parent_loses_cap_child_still_has_until_refresh() {
    let mut ledger = Ledger::new();
    let (mut parent, _) = make_open_cell(1, 100_000);
    let parent_id = parent.id;

    let (target, _) = make_open_cell(10, 0);
    let target_id = target.id;
    let slot = parent
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(target).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_timestamp(1000);

    // Spawn child.
    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    let spawn = Action {
        target: parent_id,
        method: symbol("spawn"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn1 = Turn {
        agent: parent_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(spawn);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    executor.execute(&turn1, &mut ledger);

    // Parent revokes its own capability to target.
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .revoke(slot);

    // Child still has target in delegation snapshot — can still act.
    ledger.get_mut(&child_id).unwrap().state.balance = 100_000;

    let value = [77u8; 32];
    let child_action = Action {
        target: target_id,
        method: symbol("set"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target_id,
            index: 0,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn2 = Turn {
        agent: child_id,
        nonce: 0,
        fee: 0,
        call_forest: {
            let mut f = CallForest::new();
            f.add_root(child_action);
            f
        },
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
    };
    let result = executor.execute(&turn2, &mut ledger);
    assert!(
        result.is_committed(),
        "child should still use snapshot even after parent lost cap: {:?}",
        result
    );
}

#[test]
fn test_is_stale_various_timestamps() {
    use pyana_cell::DelegatedRef;

    let source = CellId::derive_raw(&[1u8; 32], &[0u8; 32]);
    let child = CellId::derive_raw(&[2u8; 32], &[0u8; 32]);
    let delegation = DelegatedRef::new(
        source,
        child,
        vec![],
        0,
        1000,      // refreshed_at
        300,       // max_staleness = 300s
        [0u8; 32], // clist_commitment (empty c-list)
        [0u8; 64], // parent_signature (not verified in this test)
    );

    // Not stale: within window.
    assert!(!delegation.is_stale(1000));
    assert!(!delegation.is_stale(1100));
    assert!(!delegation.is_stale(1300));

    // Stale: past the window.
    assert!(delegation.is_stale(1301));
    assert!(delegation.is_stale(2000));

    // max_staleness = 0 means always stale.
    let always_stale = DelegatedRef::new(source, child, vec![], 0, 1000, 0, [0u8; 32], [0u8; 64]);
    assert!(always_stale.is_stale(1000));
    assert!(always_stale.is_stale(0));
}

// =============================================================================
// Tests: ExerciseViaCapability
// =============================================================================

/// Helper: setup a 3-cell ledger where agent has a capability (slot 0) to a
/// third cell (cap_target). Agent also has capability to its own cell (as usual).
fn setup_exercise_via_cap() -> (Ledger, CellId, CellId, CellId) {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (target, _) = make_open_cell(2, 1000);
    let (cap_target, _) = make_open_cell(3, 2000);
    let agent_id = agent.id;
    let target_id = target.id;
    let cap_target_id = cap_target.id;

    // Grant agent capability to target (slot 0) and cap_target (slot 1).
    let mut agent_with_caps = agent;
    agent_with_caps
        .capabilities
        .grant(target_id, AuthRequired::None);
    agent_with_caps
        .capabilities
        .grant(cap_target_id, AuthRequired::None);

    ledger.insert_cell(agent_with_caps).unwrap();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(cap_target).unwrap();
    (ledger, agent_id, target_id, cap_target_id)
}

#[test]
fn test_exercise_via_capability_transfer_succeeds() {
    let (mut ledger, agent_id, _target_id, cap_target_id) = setup_exercise_via_cap();
    let executor = zero_cost_executor();

    // Exercise slot 1 (cap_target) to transfer from cap_target to agent.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "exercise");
        action.effect(Effect::ExerciseViaCapability {
            cap_slot: 1, // slot 1 = capability to cap_target
            inner_effects: vec![Effect::Transfer {
                from: cap_target_id,
                to: agent_id,
                amount: 500,
            }],
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "ExerciseViaCapability should succeed: {:?}",
        result
    );

    // cap_target lost 500, agent gained 500 (minus fee).
    let cap_target = ledger.get(&cap_target_id).unwrap();
    assert_eq!(cap_target.state.balance, 2000 - 500);

    let agent = ledger.get(&agent_id).unwrap();
    // Started at 5000, paid 100 fee, received 500.
    assert_eq!(agent.state.balance, 5000 - 100 + 500);
}

#[test]
fn test_exercise_via_capability_insufficient_permissions() {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 5000);
    let (cap_target, _) = make_open_cell(3, 2000);
    let agent_id = agent.id;
    let cap_target_id = cap_target.id;

    // Grant agent a capability with Impossible permissions (cannot exercise).
    let mut agent_with_caps = agent;
    agent_with_caps
        .capabilities
        .grant(cap_target_id, AuthRequired::Impossible);

    ledger.insert_cell(agent_with_caps).unwrap();
    ledger.insert_cell(cap_target).unwrap();

    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "exercise");
        action.effect(Effect::ExerciseViaCapability {
            cap_slot: 0, // slot 0 = capability to cap_target (Impossible)
            inner_effects: vec![Effect::Transfer {
                from: cap_target_id,
                to: agent_id,
                amount: 100,
            }],
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(reason, TurnError::PermissionDenied { .. }),
                "expected PermissionDenied, got {:?}",
                reason
            );
        }
        _ => panic!("expected Rejected, got {:?}", result),
    }
}

#[test]
fn test_exercise_via_capability_slot_not_found() {
    let (mut ledger, agent_id, _target_id, _cap_target_id) = setup_exercise_via_cap();
    let executor = zero_cost_executor();

    // Try to exercise slot 99 which doesn't exist.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "exercise");
        action.effect(Effect::ExerciseViaCapability {
            cap_slot: 99, // doesn't exist
            inner_effects: vec![Effect::Transfer {
                from: CellId::from_bytes([0xAA; 32]),
                to: agent_id,
                amount: 100,
            }],
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    match result {
        crate::turn::TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(reason, TurnError::CapabilityNotHeld { .. }),
                "expected CapabilityNotHeld, got {:?}",
                reason
            );
        }
        _ => panic!("expected Rejected, got {:?}", result),
    }
}

// =============================================================================
// Tests: Fee distribution (50% proposer / 30% treasury / 20% burned)
// =============================================================================

#[test]
fn test_fee_distribution_basic() {
    // Setup: agent with 10000, proposer and treasury cells with 0.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let (proposer, _) = make_open_cell(2, 0);
    let (treasury, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let proposer_id = proposer.id;
    let treasury_id = treasury.id;

    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(proposer).unwrap();
    ledger.insert_cell(treasury).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proposer_cell(proposer_id);
    executor.set_treasury_cell(treasury_id);

    // Turn with fee=1000: proposer gets 500, treasury gets 300, 200 burned.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(1000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let agent_cell = ledger.get(&agent_id).unwrap();
    assert_eq!(agent_cell.state.balance, 10000 - 1000); // fee deducted

    let proposer_cell = ledger.get(&proposer_id).unwrap();
    assert_eq!(proposer_cell.state.balance, 500); // 50% of 1000

    let treasury_cell = ledger.get(&treasury_id).unwrap();
    assert_eq!(treasury_cell.state.balance, 300); // 30% of 1000

    // Total burned = 1000 - 500 - 300 = 200 (20%)
}

#[test]
fn test_fee_distribution_minimum_fee() {
    // Fee=1: integer division means proposer gets 0, treasury gets 0, all burned.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let (proposer, _) = make_open_cell(2, 0);
    let (treasury, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let proposer_id = proposer.id;
    let treasury_id = treasury.id;

    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(proposer).unwrap();
    ledger.insert_cell(treasury).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proposer_cell(proposer_id);
    executor.set_treasury_cell(treasury_id);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(1).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let agent_cell = ledger.get(&agent_id).unwrap();
    assert_eq!(agent_cell.state.balance, 10000 - 1);

    // fee/2 = 0, fee*3/10 = 0: both get nothing.
    let proposer_cell = ledger.get(&proposer_id).unwrap();
    assert_eq!(proposer_cell.state.balance, 0);

    let treasury_cell = ledger.get(&treasury_id).unwrap();
    assert_eq!(treasury_cell.state.balance, 0);
}

#[test]
fn test_fee_distribution_no_proposer_all_burned() {
    // Backward compat: no proposer/treasury configured -> 100% burned.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let executor = zero_cost_executor(); // no proposer/treasury set

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(1000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let agent_cell = ledger.get(&agent_id).unwrap();
    assert_eq!(agent_cell.state.balance, 10000 - 1000);
    // No other cells received anything (total supply decreased by 1000).
}

#[test]
fn test_fee_distribution_proposer_only() {
    // Only proposer configured, no treasury -> proposer gets 50%, rest burned.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let (proposer, _) = make_open_cell(2, 0);
    let agent_id = agent.id;
    let proposer_id = proposer.id;

    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(proposer).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proposer_cell(proposer_id);
    // treasury_cell left as None

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(1000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let proposer_cell = ledger.get(&proposer_id).unwrap();
    assert_eq!(proposer_cell.state.balance, 500); // 50%
    // Treasury share (300) is burned since no treasury is set.
}

#[test]
fn test_fee_distribution_missing_proposer_cell_in_ledger() {
    // Proposer cell configured but not in ledger -> share is burned gracefully.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let nonexistent_proposer = CellId::from_bytes([0xDE; 32]);

    let mut executor = zero_cost_executor();
    executor.set_proposer_cell(nonexistent_proposer);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "noop");
        action.set_field(agent_id, 0, [1u8; 32]);
    }
    let turn = builder.fee(1000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Agent still pays the full fee.
    let agent_cell = ledger.get(&agent_id).unwrap();
    assert_eq!(agent_cell.state.balance, 10000 - 1000);
    // Proposer share is burned (cell doesn't exist).
}

#[test]
fn test_fee_distribution_not_on_failure() {
    // If the turn fails (Phase 2 rejection), no fee distribution occurs.
    // The fee is still deducted (anti-DoS), but proposer/treasury get nothing.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let (proposer, _) = make_open_cell(2, 0);
    let (treasury, _) = make_open_cell(3, 0);
    let agent_id = agent.id;
    let proposer_id = proposer.id;
    let treasury_id = treasury.id;

    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(proposer).unwrap();
    ledger.insert_cell(treasury).unwrap();

    let mut executor = zero_cost_executor();
    executor.set_proposer_cell(proposer_id);
    executor.set_treasury_cell(treasury_id);

    // Create a turn that targets a non-existent cell (will fail in Phase 2).
    let nonexistent = CellId::from_bytes([0xFF; 32]);
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(nonexistent, "fail");
        action.set_field(nonexistent, 0, [1u8; 32]);
    }
    let turn = builder.fee(1000).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected());

    // Fee still deducted from agent (anti-DoS).
    let agent_cell = ledger.get(&agent_id).unwrap();
    assert_eq!(agent_cell.state.balance, 10000 - 1000);

    // Proposer and treasury get NOTHING on failure.
    let proposer_cell = ledger.get(&proposer_id).unwrap();
    assert_eq!(proposer_cell.state.balance, 0);

    let treasury_cell = ledger.get(&treasury_id).unwrap();
    assert_eq!(treasury_cell.state.balance, 0);
}

// =============================================================================
// Tests: Escrow conditional settlement
// =============================================================================

use crate::escrow::EscrowCondition;

/// Helper: set up a ledger with a sender and recipient cell for escrow tests.
fn setup_escrow_cells(sender_balance: u64, recipient_balance: u64) -> (Ledger, CellId, CellId) {
    let mut ledger = Ledger::new();
    let (sender, _) = make_open_cell(10, sender_balance);
    let (recipient, _) = make_open_cell(11, recipient_balance);
    let sender_id = sender.id;
    let recipient_id = recipient.id;
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(recipient).unwrap();
    (ledger, sender_id, recipient_id)
}

#[test]
fn test_escrow_create_and_release_with_predicate() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(100);

    let escrow_id = [1u8; 32];
    let predicate_hash = *blake3::hash(b"test-predicate").as_bytes();

    // Create escrow.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 5000,
            condition: EscrowCondition::PredicateSatisfied { predicate_hash },
            timeout_height: 200,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "CreateEscrow should succeed: {:?}",
        result
    );

    // Sender should have lost 5000 (escrow) + 100 (fee).
    let sender = ledger.get(&sender_id).unwrap();
    assert_eq!(sender.state.balance, 10000 - 5000 - 100);

    // Recipient still has 0.
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 0);

    // Release escrow with valid predicate proof.
    let mut builder2 = TurnBuilder::new(sender_id, 1);
    {
        let action = builder2.action(sender_id, "release_escrow");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(predicate_hash.to_vec()),
        });
    }
    let turn2 = builder2.fee(100).build();

    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(
        result2.is_committed(),
        "ReleaseEscrow should succeed: {:?}",
        result2
    );

    // Recipient should now have 5000.
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 5000);

    // Sender paid two fees.
    let sender = ledger.get(&sender_id).unwrap();
    assert_eq!(sender.state.balance, 10000 - 5000 - 100 - 100);
}

#[test]
fn test_escrow_create_and_timeout_refund() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(100);

    let escrow_id = [2u8; 32];
    let predicate_hash = [99u8; 32];

    // Create escrow with timeout at block 200.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 3000,
            condition: EscrowCondition::PredicateSatisfied { predicate_hash },
            timeout_height: 200,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Try to refund BEFORE timeout — should fail.
    executor.set_block_height(150);
    let mut builder_early = TurnBuilder::new(sender_id, 1);
    {
        let action = builder_early.action(sender_id, "refund_early");
        action.effect(Effect::RefundEscrow { escrow_id });
    }
    let turn_early = builder_early.fee(100).build();
    let result_early = executor.execute(&turn_early, &mut ledger);
    assert!(
        result_early.is_rejected(),
        "RefundEscrow before timeout should fail"
    );

    // Advance past timeout and refund (nonce is now 2 because the failed attempt still consumed nonce 1).
    executor.set_block_height(201);
    let mut builder_refund = TurnBuilder::new(sender_id, 2);
    {
        let action = builder_refund.action(sender_id, "refund_escrow");
        action.effect(Effect::RefundEscrow { escrow_id });
    }
    let turn_refund = builder_refund.fee(100).build();
    let result_refund = executor.execute(&turn_refund, &mut ledger);
    assert!(
        result_refund.is_committed(),
        "RefundEscrow after timeout should succeed: {:?}",
        result_refund
    );

    // Sender should get the 3000 back (minus fees).
    let sender = ledger.get(&sender_id).unwrap();
    // Started 10000, lost 100 (fee create) + 100 (fee failed refund) + 100 (fee refund)
    // Lost 3000 to escrow, got 3000 back.
    assert_eq!(sender.state.balance, 10000 - 100 - 100 - 100);

    // Recipient still has 0.
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 0);
}

#[test]
fn test_escrow_release_without_valid_proof_fails() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(100);

    let escrow_id = [3u8; 32];
    let predicate_hash = [77u8; 32];

    // Create escrow.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 2000,
            condition: EscrowCondition::PredicateSatisfied { predicate_hash },
            timeout_height: 300,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Try to release with WRONG predicate hash.
    let wrong_hash = [88u8; 32];
    let mut builder_bad = TurnBuilder::new(sender_id, 1);
    {
        let action = builder_bad.action(sender_id, "release_bad");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(wrong_hash.to_vec()),
        });
    }
    let turn_bad = builder_bad.fee(100).build();
    let result_bad = executor.execute(&turn_bad, &mut ledger);
    assert!(
        result_bad.is_rejected(),
        "ReleaseEscrow with wrong proof should fail"
    );

    // Try to release with no proof.
    let mut builder_none = TurnBuilder::new(sender_id, 2);
    {
        let action = builder_none.action(sender_id, "release_none");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: None,
        });
    }
    let turn_none = builder_none.fee(100).build();
    let result_none = executor.execute(&turn_none, &mut ledger);
    assert!(
        result_none.is_rejected(),
        "ReleaseEscrow with no proof should fail"
    );

    // Recipient still has 0.
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 0);
}

#[test]
fn test_escrow_double_release_fails() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(100);

    let escrow_id = [4u8; 32];
    let predicate_hash = [55u8; 32];

    // Create escrow.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 4000,
            condition: EscrowCondition::PredicateSatisfied { predicate_hash },
            timeout_height: 500,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Release escrow (first time — should succeed).
    let mut builder_release = TurnBuilder::new(sender_id, 1);
    {
        let action = builder_release.action(sender_id, "release");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(predicate_hash.to_vec()),
        });
    }
    let turn_release = builder_release.fee(100).build();
    let result_release = executor.execute(&turn_release, &mut ledger);
    assert!(result_release.is_committed());

    // Release escrow AGAIN (second time — should fail: already resolved).
    let mut builder_double = TurnBuilder::new(sender_id, 2);
    {
        let action = builder_double.action(sender_id, "release_again");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(predicate_hash.to_vec()),
        });
    }
    let turn_double = builder_double.fee(100).build();
    let result_double = executor.execute(&turn_double, &mut ledger);
    assert!(
        result_double.is_rejected(),
        "Double release should fail: escrow already resolved"
    );

    // Recipient should only have 4000 (from single release).
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 4000);
}

#[test]
fn test_escrow_create_insufficient_balance() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(1000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(100);

    let escrow_id = [5u8; 32];

    // Try to create escrow with more than the sender has (after fee).
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 950, // sender has 1000, fee is 100, so only 900 available
            condition: EscrowCondition::PredicateSatisfied {
                predicate_hash: [0u8; 32],
            },
            timeout_height: 200,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "CreateEscrow with insufficient balance should fail"
    );
}

#[test]
fn test_escrow_release_with_proof_verifier() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor =
        TurnExecutor::with_proof_verifier(ComputronCosts::zero(), Box::new(AlwaysAcceptVerifier));
    executor.set_block_height(100);

    let escrow_id = [6u8; 32];
    let vk = [42u8; 32];

    // Create escrow with ProofPresented condition.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 5000,
            condition: EscrowCondition::ProofPresented {
                verification_key: vk,
            },
            timeout_height: 300,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Release with proof (AlwaysAcceptVerifier accepts anything).
    let mut builder_release = TurnBuilder::new(sender_id, 1);
    {
        let action = builder_release.action(sender_id, "release");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(vec![1, 2, 3, 4]),
        });
    }
    let turn_release = builder_release.fee(100).build();
    let result_release = executor.execute(&turn_release, &mut ledger);
    assert!(
        result_release.is_committed(),
        "ReleaseEscrow with valid proof should succeed: {:?}",
        result_release
    );

    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 5000);
}

#[test]
fn test_escrow_release_proof_rejected_by_verifier() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor =
        TurnExecutor::with_proof_verifier(ComputronCosts::zero(), Box::new(AlwaysRejectVerifier));
    executor.set_block_height(100);

    let escrow_id = [7u8; 32];
    let vk = [42u8; 32];

    // Create escrow with ProofPresented condition.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 5000,
            condition: EscrowCondition::ProofPresented {
                verification_key: vk,
            },
            timeout_height: 300,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    // Try to release (AlwaysRejectVerifier rejects).
    let mut builder_release = TurnBuilder::new(sender_id, 1);
    {
        let action = builder_release.action(sender_id, "release");
        action.effect(Effect::ReleaseEscrow {
            escrow_id,
            proof: Some(vec![1, 2, 3, 4]),
        });
    }
    let turn_release = builder_release.fee(100).build();
    let result_release = executor.execute(&turn_release, &mut ledger);
    assert!(
        result_release.is_rejected(),
        "ReleaseEscrow with rejected proof should fail"
    );

    // Recipient still 0.
    let recipient = ledger.get(&recipient_id).unwrap();
    assert_eq!(recipient.state.balance, 0);
}

// =============================================================================
// ADVERSARIAL TESTS: Rollback of obligation/escrow/nullifier state (CRITICAL fix)
// =============================================================================

/// Adversarial test: Obligation record must be removed on turn rollback.
///
/// Attack scenario:
/// 1. Create obligation (balance deducted, record inserted into executor's map)
/// 2. Same turn deliberately fails (balance restored by journal rollback)
/// 3. WITHOUT the fix: obligation record survives; attacker submits new turn to fulfill
///    the phantom obligation (balance credited again = inflation)
/// 4. WITH the fix: obligation record is removed on rollback, no phantom exploit possible
#[test]
fn test_adversarial_obligation_rollback_on_turn_failure() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(10000, 5000);
    let mut executor = zero_cost_executor();
    executor.set_block_height(10);

    let stake_commitment = pyana_cell::NoteCommitment([0xAA; 32]);

    // Build a turn that creates an obligation, then FAILS with an invalid field index.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "create_then_fail");
        // First effect: create obligation (will insert into obligations map and deduct balance).
        action.effect(Effect::CreateObligation {
            beneficiary: target_id,
            condition: crate::conditional::ProofCondition::HashPreimage { hash: [0u8; 32] },
            deadline_height: 100,
            stake: stake_commitment,
            stake_amount: 1000,
        });
        // Second effect: invalid field index to force the turn to fail.
        action.effect(Effect::SetField {
            cell: agent_id,
            index: 99, // Invalid index: will fail
            value: [0u8; 32],
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Turn should be rejected due to invalid field index"
    );

    // Verify the obligation was NOT left behind in the executor's map.
    let obligations = executor.obligations.lock().unwrap();
    assert!(
        obligations.is_empty(),
        "Obligation record must be removed on rollback; found {} records",
        obligations.len()
    );
    drop(obligations);

    // Verify balance was fully restored (fee still deducted, but obligation stake returned).
    let agent = ledger.get(&agent_id).unwrap();
    // Fee is always deducted (Phase 1, never rolled back), but stake should be returned.
    assert_eq!(agent.state.balance, 10000 - 100);
}

/// Adversarial test: Escrow record must be removed on turn rollback.
///
/// Same attack pattern as obligation: create escrow, fail turn, exploit phantom record.
#[test]
fn test_adversarial_escrow_rollback_on_turn_failure() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(10);

    let escrow_id = [0xEE; 32];

    // Build a turn that creates an escrow, then FAILS.
    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "create_escrow_then_fail");
        // First effect: create escrow (will insert into escrows map and deduct balance).
        action.effect(Effect::CreateEscrow {
            cell: sender_id,
            recipient: recipient_id,
            amount: 3000,
            condition: crate::escrow::EscrowCondition::PredicateSatisfied {
                predicate_hash: [0x42; 32],
            },
            timeout_height: 200,
            escrow_id,
        });
        // Second effect: invalid field index to force failure.
        action.effect(Effect::SetField {
            cell: sender_id,
            index: 99, // Invalid
            value: [0u8; 32],
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "Turn should be rejected due to invalid field index"
    );

    // Verify the escrow was NOT left behind.
    let escrows = executor.escrows.lock().unwrap();
    assert!(
        escrows.is_empty(),
        "Escrow record must be removed on rollback; found {} records",
        escrows.len()
    );
    drop(escrows);

    // Verify sender's balance was restored (minus fee).
    let sender = ledger.get(&sender_id).unwrap();
    assert_eq!(sender.state.balance, 10000 - 100);
}

// =============================================================================
// ADVERSARIAL TEST: FulfillObligation access control (HIGH fix)
// =============================================================================

/// Adversarial test: Only the obligor can fulfill their own obligation.
///
/// Without the fix, ANY cell could call FulfillObligation and return the stake
/// to the obligor, defeating the obligation's purpose (e.g., a beneficiary would
/// lose their slash opportunity).
#[test]
fn test_adversarial_fulfill_obligation_wrong_caller() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(10000, 5000);
    let mut executor = zero_cost_executor();
    executor.set_block_height(10);

    let stake_commitment = pyana_cell::NoteCommitment([0xBB; 32]);

    // First turn: agent creates an obligation.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "create_obligation");
        action.effect(Effect::CreateObligation {
            beneficiary: target_id,
            condition: crate::conditional::ProofCondition::HashPreimage { hash: [0u8; 32] },
            deadline_height: 100,
            stake: stake_commitment,
            stake_amount: 2000,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "CreateObligation should succeed");

    // Get the obligation_id (same derivation as executor).
    let obligation_id = {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-obligation-id-v1");
        hasher.update(agent_id.as_bytes());
        hasher.update(target_id.as_bytes());
        hasher.update(&100u64.to_le_bytes());
        hasher.update(&stake_commitment.0);
        *hasher.finalize().as_bytes()
    };

    // Second turn: target_id (NOT the obligor) tries to fulfill.
    // target_id acts as agent for this turn.
    let mut builder2 = TurnBuilder::new(target_id, 0);
    {
        let action = builder2.action(target_id, "steal_fulfill");
        action.effect(Effect::FulfillObligation {
            obligation_id,
            proof: crate::conditional::ConditionProof::Preimage([0u8; 32]),
        });
    }
    let turn2 = builder2.fee(100).build();
    let result2 = executor.execute(&turn2, &mut ledger);
    assert!(
        result2.is_rejected(),
        "FulfillObligation by non-obligor must be rejected"
    );
    let (error, _) = result2.unwrap_rejected();
    match error {
        TurnError::InvalidEffect { reason } => {
            assert!(
                reason.contains("only the obligor"),
                "Expected obligor access control error, got: {reason}"
            );
        }
        other => panic!("Expected InvalidEffect, got: {other:?}"),
    }

    // Verify the obligor can still fulfill their own obligation.
    let mut builder3 = TurnBuilder::new(agent_id, 1);
    {
        let action = builder3.action(agent_id, "legitimate_fulfill");
        action.effect(Effect::FulfillObligation {
            obligation_id,
            proof: crate::conditional::ConditionProof::Preimage([0u8; 32]),
        });
    }
    let turn3 = builder3.fee(100).build();
    let result3 = executor.execute(&turn3, &mut ledger);
    assert!(
        result3.is_committed(),
        "FulfillObligation by obligor should succeed"
    );

    // Verify stake was returned to obligor.
    let agent = ledger.get(&agent_id).unwrap();
    // Started with 10000, paid 100 fee (turn1), lost 2000 stake, paid 100 fee (turn3), got 2000 back.
    assert_eq!(agent.state.balance, 10000 - 100 - 2000 - 100 + 2000);
}

// =============================================================================
// ADVERSARIAL TEST: CreateEscrow permission check (MEDIUM-HIGH fix)
// =============================================================================

/// Adversarial test: CreateEscrow cell must match action target.
///
/// Without the fix, an attacker could create an action targeting their own cell
/// but specify someone else's cell in the CreateEscrow effect, locking the victim's
/// funds without authorization.
#[test]
fn test_adversarial_create_escrow_wrong_cell() {
    let (mut ledger, agent_id, target_id) = setup_two_open_cells(10000, 5000);
    let mut executor = zero_cost_executor();
    executor.set_block_height(10);

    let escrow_id = [0xDD; 32];

    // Attacker (agent) targets their own cell but specifies target_id as the
    // escrow cell — attempting to lock target's funds.
    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "steal_lock");
        action.effect(Effect::CreateEscrow {
            cell: target_id, // WRONG: not the action target (agent_id)
            recipient: agent_id,
            amount: 5000,
            condition: crate::escrow::EscrowCondition::PredicateSatisfied {
                predicate_hash: [0x42; 32],
            },
            timeout_height: 200,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "CreateEscrow with cell != action_target must be rejected"
    );
    let (error, _) = result.unwrap_rejected();
    match error {
        TurnError::InvalidEffect { reason } => {
            assert!(
                reason.contains("CreateEscrow cell must match action target"),
                "Expected cell mismatch error, got: {reason}"
            );
        }
        other => panic!("Expected InvalidEffect, got: {other:?}"),
    }

    // Verify target's balance is unchanged.
    let target = ledger.get(&target_id).unwrap();
    assert_eq!(target.state.balance, 5000);
}

/// Test that CreateEscrow succeeds when cell matches action target.
#[test]
fn test_create_escrow_correct_cell_matches_target() {
    let (mut ledger, sender_id, recipient_id) = setup_escrow_cells(10000, 0);
    let mut executor = zero_cost_executor();
    executor.set_block_height(10);

    let escrow_id = [0xCC; 32];

    let mut builder = TurnBuilder::new(sender_id, 0);
    {
        let action = builder.action(sender_id, "valid_escrow");
        action.effect(Effect::CreateEscrow {
            cell: sender_id, // CORRECT: matches action target
            recipient: recipient_id,
            amount: 3000,
            condition: crate::escrow::EscrowCondition::PredicateSatisfied {
                predicate_hash: [0x42; 32],
            },
            timeout_height: 200,
            escrow_id,
        });
    }
    let turn = builder.fee(100).build();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "CreateEscrow with correct cell should succeed"
    );

    // Verify balance was deducted.
    let sender = ledger.get(&sender_id).unwrap();
    assert_eq!(sender.state.balance, 10000 - 100 - 3000);
}

// =============================================================================
// Tests: Committed (Pedersen) conservation path
// =============================================================================

#[test]
fn test_committed_conservation_valid_proof_passes() {
    use curve25519_dalek::scalar::Scalar;
    use pyana_cell::{ValueCommitment, prove_conservation};

    // Setup: single agent cell with open permissions and a proof verifier.
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100000, 0);
    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Create blinding factors.
    let r_in = {
        let mut bytes = [0u8; 64];
        bytes[0] = 10;
        bytes[1] = 37;
        Scalar::from_bytes_mod_order_wide(&bytes)
    };
    let r_out1 = {
        let mut bytes = [0u8; 64];
        bytes[0] = 20;
        bytes[1] = 74;
        Scalar::from_bytes_mod_order_wide(&bytes)
    };
    let r_out2 = {
        let mut bytes = [0u8; 64];
        bytes[0] = 30;
        bytes[1] = 111;
        Scalar::from_bytes_mod_order_wide(&bytes)
    };

    // Commit: input 500, output 300 + 200 (conservation holds).
    let input_vc = ValueCommitment::commit(500, &r_in);
    let output_vc1 = ValueCommitment::commit(300, &r_out1);
    let output_vc2 = ValueCommitment::commit(200, &r_out2);

    let input_vc_bytes = input_vc.to_bytes().0;
    let output_vc1_bytes = output_vc1.to_bytes().0;
    let output_vc2_bytes = output_vc2.to_bytes().0;

    // Build the turn with committed note effects.
    let nullifier = pyana_cell::Nullifier([0xBB; 32]);
    let commitment1 = pyana_cell::NoteCommitment([0xCC; 32]);
    let commitment2 = pyana_cell::NoteCommitment([0xDD; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "committed_transfer");
        action.effect(Effect::NoteSpend {
            nullifier,
            note_tree_root: [0xFFu8; 32],
            value: 500,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: Some(input_vc_bytes),
        });
        action.effect(Effect::NoteCreate {
            commitment: commitment1,
            value: 300,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: Some(output_vc1_bytes),
            range_proof: Some(vec![0x01]), // placeholder range proof
        });
        action.effect(Effect::NoteCreate {
            commitment: commitment2,
            value: 200,
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: Some(output_vc2_bytes),
            range_proof: Some(vec![0x01]), // placeholder range proof
        });
    }
    let mut turn = builder.fee(10000).build();

    // Produce and attach the conservation proof.
    // Excess blinding = sum(input_blindings) - sum(output_blindings).
    let excess_blinding = r_in - (r_out1 + r_out2);
    let turn_hash = turn.hash();
    let conservation_proof = prove_conservation(
        &[input_vc.clone()],
        &[output_vc1.clone(), output_vc2.clone()],
        &excess_blinding,
        &turn_hash,
    );
    let proof_bytes = postcard::to_allocvec(&conservation_proof).unwrap();
    turn.conservation_proof = Some(proof_bytes);

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "committed conservation with valid proof should pass"
    );
}

#[test]
fn test_committed_conservation_inflated_output_fails() {
    use curve25519_dalek::scalar::Scalar;
    use pyana_cell::{ValueCommitment, prove_conservation};

    // Setup: single agent cell with open permissions and a proof verifier.
    let (mut ledger, agent_id, _target_id) = setup_two_open_cells(100000, 0);
    let mut executor = zero_cost_executor();
    executor.set_proof_verifier(Box::new(AlwaysAcceptVerifier));

    // Create blinding factors.
    let r_in = {
        let mut bytes = [0u8; 64];
        bytes[0] = 40;
        bytes[1] = 77;
        Scalar::from_bytes_mod_order_wide(&bytes)
    };
    let r_out = {
        let mut bytes = [0u8; 64];
        bytes[0] = 50;
        bytes[1] = 99;
        Scalar::from_bytes_mod_order_wide(&bytes)
    };

    // Commit: input 500, output 600 (INFLATED -- conservation violated).
    let input_vc = ValueCommitment::commit(500, &r_in);
    let output_vc = ValueCommitment::commit(600, &r_out);

    let input_vc_bytes = input_vc.to_bytes().0;
    let output_vc_bytes = output_vc.to_bytes().0;

    // Build the turn with committed note effects.
    let nullifier = pyana_cell::Nullifier([0xEE; 32]);
    let commitment = pyana_cell::NoteCommitment([0xFF; 32]);

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "inflated_transfer");
        action.effect(Effect::NoteSpend {
            nullifier,
            note_tree_root: [0xFFu8; 32],
            value: 500,
            asset_type: 1,
            spending_proof: vec![0x01],
            value_commitment: Some(input_vc_bytes),
        });
        action.effect(Effect::NoteCreate {
            commitment,
            value: 600, // INFLATED
            asset_type: 1,
            encrypted_note: vec![],
            value_commitment: Some(output_vc_bytes),
            range_proof: Some(vec![0x01]), // placeholder range proof
        });
    }
    let mut turn = builder.fee(10000).build();

    // Try to forge a proof -- use the blinding difference as excess, but since
    // values don't balance, the Schnorr verification will fail.
    let blinding_diff = r_in - r_out;
    let turn_hash = turn.hash();
    let conservation_proof = prove_conservation(
        &[input_vc.clone()],
        &[output_vc.clone()],
        &blinding_diff,
        &turn_hash,
    );
    let proof_bytes = postcard::to_allocvec(&conservation_proof).unwrap();
    turn.conservation_proof = Some(proof_bytes);

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "committed conservation with inflated output should be rejected"
    );
}

// =============================================================================
// Sovereign Cell Tests (Phase 1a)
// =============================================================================

#[test]
fn sovereign_cell_execute_turn_with_valid_witness() {
    // Setup: create a sovereign cell and register its commitment.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10_000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    // Create a cell that will become sovereign.
    let (mut sovereign_cell, _) = make_open_cell(2, 500);
    let sovereign_id = sovereign_cell.id;
    sovereign_cell.mode = pyana_cell::CellMode::Sovereign;

    // Compute the initial commitment and register as sovereign.
    let initial_commitment = sovereign_cell.state_commitment();
    ledger
        .register_sovereign_cell(sovereign_id, initial_commitment)
        .unwrap();

    // Grant agent a capability to the sovereign cell.
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    // Build a turn that targets the sovereign cell (set a field).
    let new_value = [42u8; 32];
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree {
                action: Action {
                    target: sovereign_id,
                    method: symbol("set_field"),
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: CellPreconditions::default(),
                    effects: vec![Effect::SetField {
                        cell: sovereign_id,
                        index: 0,
                        value: new_value,
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: CommitmentMode::Full,
                    balance_change: None,
                },
                children: vec![],
                hash: [0u8; 32],
            }],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: {
            let mut m = std::collections::HashMap::new();
            m.insert(
                sovereign_id,
                crate::turn::SovereignCellWitness {
                    cell_state: sovereign_cell.clone(),
                    state_proof: initial_commitment,
                },
            );
            m
        },
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
    };

    let executor = zero_cost_executor();
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "turn should commit successfully");

    // After execution, the sovereign commitment should be updated.
    let new_commitment = ledger.get_sovereign_commitment(&sovereign_id).unwrap();
    assert_ne!(
        *new_commitment, initial_commitment,
        "commitment should change after state modification"
    );

    // Verify the new commitment matches what we'd expect.
    let mut expected_cell = sovereign_cell.clone();
    expected_cell.state.fields[0] = new_value;
    assert_eq!(
        *new_commitment,
        expected_cell.state_commitment(),
        "new commitment should match the expected post-transition state"
    );

    // The cell should NOT be in the hosted store.
    assert!(
        ledger.get(&sovereign_id).is_none(),
        "sovereign cell should not be in hosted store"
    );
    assert!(
        ledger.is_sovereign(&sovereign_id),
        "cell should still be sovereign"
    );
}

#[test]
fn sovereign_cell_rejected_without_witness() {
    // Setup: create a sovereign cell.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10_000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let (sovereign_cell, _) = make_open_cell(2, 500);
    let sovereign_id = sovereign_cell.id;
    let commitment = sovereign_cell.state_commitment();
    ledger
        .register_sovereign_cell(sovereign_id, commitment)
        .unwrap();

    // Grant agent a capability to the sovereign cell.
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    // Build a turn targeting the sovereign cell WITHOUT providing a witness.
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree {
                action: Action {
                    target: sovereign_id,
                    method: symbol("set_field"),
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: CellPreconditions::default(),
                    effects: vec![Effect::SetField {
                        cell: sovereign_id,
                        index: 0,
                        value: [1u8; 32],
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: CommitmentMode::Full,
                    balance_change: None,
                },
                children: vec![],
                hash: [0u8; 32],
            }],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(), // NO witness!
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
    };

    let executor = zero_cost_executor();
    let result = executor.execute(&turn, &mut ledger);

    // The turn should be rejected because the sovereign cell is not in the
    // hosted store and no witness was provided.
    assert!(
        result.is_rejected(),
        "turn should be rejected without witness"
    );
    let (error, _) = result.unwrap_rejected();
    // Should fail with CellNotFound since the cell isn't in the hosted store.
    assert!(
        matches!(error, TurnError::CellNotFound { .. }),
        "expected CellNotFound, got: {error}"
    );
}

#[test]
fn sovereign_cell_rejected_with_wrong_commitment() {
    // Setup: create a sovereign cell.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10_000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    let (sovereign_cell, _) = make_open_cell(2, 500);
    let sovereign_id = sovereign_cell.id;
    let commitment = sovereign_cell.state_commitment();
    ledger
        .register_sovereign_cell(sovereign_id, commitment)
        .unwrap();

    // Grant agent a capability to the sovereign cell.
    ledger
        .get_mut(&agent_id)
        .unwrap()
        .capabilities
        .grant(sovereign_id, AuthRequired::None);

    // Create a tampered witness: claim a different state than what's committed.
    let mut tampered_cell = sovereign_cell.clone();
    tampered_cell.state.balance = 999_999; // Lie about balance.
    let tampered_commitment = tampered_cell.state_commitment();

    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree {
                action: Action {
                    target: sovereign_id,
                    method: symbol("set_field"),
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: CellPreconditions::default(),
                    effects: vec![Effect::SetField {
                        cell: sovereign_id,
                        index: 0,
                        value: [1u8; 32],
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: CommitmentMode::Full,
                    balance_change: None,
                },
                children: vec![],
                hash: [0u8; 32],
            }],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: {
            let mut m = std::collections::HashMap::new();
            m.insert(
                sovereign_id,
                crate::turn::SovereignCellWitness {
                    cell_state: tampered_cell,
                    state_proof: tampered_commitment, // This won't match stored commitment
                },
            );
            m
        },
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
    };

    let executor = zero_cost_executor();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "turn should be rejected with wrong commitment"
    );
    let (error, _) = result.unwrap_rejected();
    assert!(
        matches!(error, TurnError::SovereignCommitmentMismatch { .. }),
        "expected SovereignCommitmentMismatch, got: {error}"
    );
}

#[test]
fn sovereign_cell_make_sovereign_effect() {
    // Setup: create a hosted cell, then use MakeSovereign to transition it.
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10_000);
    let agent_id = agent.id;

    let (target, _) = make_open_cell(2, 500);
    let target_id = target.id;

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target.clone()).unwrap();

    // Verify the cell starts as hosted.
    assert!(!ledger.is_sovereign(&target_id));
    assert!(ledger.get(&target_id).is_some());

    // Build a turn that makes the target sovereign.
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree {
                action: Action {
                    target: target_id,
                    method: symbol("make_sovereign"),
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: CellPreconditions::default(),
                    effects: vec![Effect::MakeSovereign { cell: target_id }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: CommitmentMode::Full,
                    balance_change: None,
                },
                children: vec![],
                hash: [0u8; 32],
            }],
            forest_hash: [0u8; 32],
        },
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
    };

    let executor = zero_cost_executor();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "MakeSovereign turn should commit: {:?}",
        result
    );

    // After execution, the cell should be sovereign.
    assert!(
        ledger.is_sovereign(&target_id),
        "cell should be sovereign after MakeSovereign"
    );
    assert!(
        ledger.get(&target_id).is_none(),
        "cell should not be in hosted store"
    );

    // The commitment should match the original cell's state commitment.
    let expected_commitment = target.state_commitment();
    let stored = ledger.get_sovereign_commitment(&target_id).unwrap();
    assert_eq!(
        *stored, expected_commitment,
        "stored commitment should match original state"
    );
}

#[test]
fn sovereign_cell_state_commitment_deterministic() {
    // Verify state_commitment is deterministic.
    let (cell1, _) = make_open_cell(5, 1000);
    let (cell2, _) = make_open_cell(5, 1000);
    assert_eq!(cell1.state_commitment(), cell2.state_commitment());

    // Different state => different commitment.
    let (mut cell3, _) = make_open_cell(5, 1000);
    cell3.state.balance = 999;
    assert_ne!(cell1.state_commitment(), cell3.state_commitment());

    // Different nonce => different commitment.
    let (mut cell4, _) = make_open_cell(5, 1000);
    cell4.state.nonce = 42;
    assert_ne!(cell1.state_commitment(), cell4.state_commitment());

    // Different field => different commitment.
    let (mut cell5, _) = make_open_cell(5, 1000);
    cell5.state.fields[0] = [1u8; 32];
    assert_ne!(cell1.state_commitment(), cell5.state_commitment());
}

// =============================================================================
// Tests: Phase 3 — Proof-carrying sovereign turns
// =============================================================================

/// Helper: set up a sovereign cell in the ledger and return (ledger, agent_id, sovereign_cell_id, old_commitment).
fn setup_sovereign_cell_for_proof_test() -> (Ledger, CellId, CellId, [u8; 32]) {
    let mut ledger = Ledger::new();
    let (agent, _) = make_open_cell(1, 10000);
    let agent_id = agent.id;
    ledger.insert_cell(agent).unwrap();

    // Create a cell, then make it sovereign.
    let (sovereign_cell, _) = make_open_cell(10, 5000);
    let sovereign_id = sovereign_cell.id;
    let commitment = sovereign_cell.state_commitment();
    ledger.insert_cell(sovereign_cell).unwrap();
    let _ = ledger.make_sovereign(&sovereign_id).unwrap();

    (ledger, agent_id, sovereign_id, commitment)
}

/// Helper: generate a valid sovereign execution proof for a balance transfer.
///
/// Returns (proof_bytes, new_commitment, effects_hash) where the proof is valid
/// against the SovereignTransitionAir.
fn generate_valid_sovereign_proof(
    old_commitment: &[u8; 32],
    new_commitment: &[u8; 32],
    cell_id: &CellId,
    effects_hash: &[u8; 32],
) -> Vec<u8> {
    use pyana_circuit::sovereign_transition_air::{
        SovereignTransitionAir, generate_sovereign_transition_trace,
    };
    use pyana_circuit::stark::{proof_to_bytes, prove};

    // Compute the cell_id hash the executor will use.
    let cell_id_hash = *blake3::hash(cell_id.as_bytes()).as_bytes();

    // Generate the trace and public inputs for a transfer of 100 outgoing.
    let (trace, public_inputs) = generate_sovereign_transition_trace(
        1000, // old_balance (arbitrary, just needs to satisfy the constraint)
        100,  // transfer_amount
        1,    // direction = outgoing
        old_commitment,
        new_commitment,
        effects_hash,
        &cell_id_hash,
    );

    let air = SovereignTransitionAir;
    let proof = prove(&air, &trace, &public_inputs);
    proof_to_bytes(&proof)
}

#[test]
fn test_proof_carrying_turn_accepted() {
    let (mut ledger, agent_id, sovereign_id, old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    // New commitment (what the sovereign claims as its post-state).
    let new_commitment = [42u8; 32];

    // Build a minimal turn with an empty call forest (the effects are proven, not executed).
    let mut builder = TurnBuilder::new(agent_id, 0);
    // Add a dummy action so the forest isn't empty (required by executor).
    {
        let action = builder.action(agent_id, "noop");
        let _ = action; // no effects
    }
    let mut turn = builder.fee(100).build();

    // Compute effects hash the same way the executor will.
    let effects_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-sovereign-effects-v1:");
        // Hash effects from the turn's call forest (the noop has no effects so just the prefix).
        for root in &turn.call_forest.roots {
            hash_tree_effects_test(root, &mut hasher);
        }
        *hasher.finalize().as_bytes()
    };

    // Generate a valid STARK proof.
    let proof_bytes = generate_valid_sovereign_proof(
        &old_commitment,
        &new_commitment,
        &sovereign_id,
        &effects_hash,
    );

    // Attach the proof to the turn.
    turn.execution_proof = Some(proof_bytes);
    turn.execution_proof_cell = Some(sovereign_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "proof-carrying turn should be committed, got: {:?}",
        match &result {
            crate::turn::TurnResult::Rejected { reason, .. } => format!("{}", reason),
            _ => "non-rejected".to_string(),
        }
    );

    // Verify the sovereign commitment was updated.
    let stored = ledger.get_sovereign_commitment(&sovereign_id).unwrap();
    assert_eq!(*stored, new_commitment);
}

#[test]
fn test_proof_carrying_turn_wrong_old_commitment() {
    let (mut ledger, agent_id, sovereign_id, _old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    // Use a WRONG old_commitment in the proof (doesn't match what's stored).
    let wrong_old_commitment = [99u8; 32];
    let new_commitment = [42u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let _action = builder.action(agent_id, "noop");
    }
    let mut turn = builder.fee(100).build();

    let effects_hash = {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-sovereign-effects-v1:");
        for root in &turn.call_forest.roots {
            hash_tree_effects_test(root, &mut hasher);
        }
        *hasher.finalize().as_bytes()
    };

    // Generate proof with WRONG old_commitment.
    let proof_bytes = generate_valid_sovereign_proof(
        &wrong_old_commitment,
        &new_commitment,
        &sovereign_id,
        &effects_hash,
    );

    turn.execution_proof = Some(proof_bytes);
    turn.execution_proof_cell = Some(sovereign_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_rejected(),
        "should reject: old commitment mismatch"
    );
    let (err, _) = result.unwrap_rejected();
    assert!(
        matches!(err, TurnError::SovereignCommitmentMismatch { .. }),
        "expected SovereignCommitmentMismatch, got: {}",
        err
    );
}

#[test]
fn test_proof_carrying_turn_wrong_effects_hash() {
    let (mut ledger, agent_id, sovereign_id, old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    let new_commitment = [42u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let _action = builder.action(agent_id, "noop");
    }
    let mut turn = builder.fee(100).build();

    // Use a WRONG effects hash in the proof.
    let wrong_effects_hash = [77u8; 32];
    let proof_bytes = generate_valid_sovereign_proof(
        &old_commitment,
        &new_commitment,
        &sovereign_id,
        &wrong_effects_hash, // doesn't match what executor computes
    );

    turn.execution_proof = Some(proof_bytes);
    turn.execution_proof_cell = Some(sovereign_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "should reject: effects hash mismatch");
    let (err, _) = result.unwrap_rejected();
    assert!(
        matches!(err, TurnError::EffectsHashMismatch { .. }),
        "expected EffectsHashMismatch, got: {}",
        err
    );
}

#[test]
fn test_proof_carrying_turn_invalid_proof_bytes() {
    let (mut ledger, agent_id, sovereign_id, _old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    let new_commitment = [42u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let _action = builder.action(agent_id, "noop");
    }
    let mut turn = builder.fee(100).build();

    // Invalid proof bytes (garbage).
    turn.execution_proof = Some(vec![0xDE, 0xAD, 0xBE, 0xEF]);
    turn.execution_proof_cell = Some(sovereign_id);
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "should reject: invalid proof bytes");
    let (err, _) = result.unwrap_rejected();
    assert!(
        matches!(err, TurnError::InvalidExecutionProof(_)),
        "expected InvalidExecutionProof, got: {}",
        err
    );
}

#[test]
fn test_proof_carrying_turn_requires_sovereign_cell() {
    let (mut ledger, agent_id, _sovereign_id, _old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    // Target a NON-sovereign cell (the agent itself is hosted, not sovereign).
    let new_commitment = [42u8; 32];

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let _action = builder.action(agent_id, "noop");
    }
    let mut turn = builder.fee(100).build();

    turn.execution_proof = Some(vec![1, 2, 3, 4]);
    turn.execution_proof_cell = Some(agent_id); // agent is NOT sovereign
    turn.execution_proof_new_commitment = Some(new_commitment);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "should reject: non-sovereign target");
    let (err, _) = result.unwrap_rejected();
    assert!(
        matches!(err, TurnError::ProofCarryingRequiresSovereign { .. }),
        "expected ProofCarryingRequiresSovereign, got: {}",
        err
    );
}

#[test]
fn test_proof_carrying_turn_no_cell_specified() {
    let (mut ledger, agent_id, _sovereign_id, _old_commitment) =
        setup_sovereign_cell_for_proof_test();
    let executor = zero_cost_executor();

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let _action = builder.action(agent_id, "noop");
    }
    let mut turn = builder.fee(100).build();

    // execution_proof is set but execution_proof_cell is None.
    turn.execution_proof = Some(vec![1, 2, 3, 4]);
    turn.execution_proof_cell = None;
    turn.execution_proof_new_commitment = Some([42u8; 32]);

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_rejected(), "should reject: no cell specified");
    let (err, _) = result.unwrap_rejected();
    assert!(
        matches!(err, TurnError::InvalidExecutionProof(_)),
        "expected InvalidExecutionProof, got: {}",
        err
    );
}

/// Helper: hash effects from a tree (matches the executor's internal method).
fn hash_tree_effects_test(tree: &crate::forest::CallTree, hasher: &mut blake3::Hasher) {
    for effect in &tree.action.effects {
        hasher.update(&effect.hash());
    }
    for child in &tree.children {
        hash_tree_effects_test(child, hasher);
    }
}
