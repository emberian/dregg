//! High-level escrow lifecycle helpers built on `pyana-turn` effects.
//!
//! Wraps the low-level `Effect::CreateEscrow`, `Effect::ReleaseEscrow`, and
//! `Effect::RefundEscrow` into a managed workflow that submits turns to a
//! `PyanaEngine`.

use pyana_cell::CellId;
use pyana_sdk::embed::PyanaEngine;
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::escrow::EscrowCondition;
use pyana_turn::turn::Turn;
use pyana_turn::{CallForest, CallTree};

/// Errors from escrow lifecycle operations.
#[derive(Debug)]
pub enum EscrowError {
    /// Turn execution was rejected by the engine.
    TurnRejected(String),
    /// The escrow has already been resolved.
    AlreadyResolved,
    /// The escrow timeout has not yet passed (cannot refund).
    NotExpired {
        timeout_height: u64,
        current_height: u64,
    },
}

impl std::fmt::Display for EscrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TurnRejected(reason) => write!(f, "turn rejected: {reason}"),
            Self::AlreadyResolved => write!(f, "escrow already resolved"),
            Self::NotExpired {
                timeout_height,
                current_height,
            } => write!(
                f,
                "escrow not expired: timeout at height {timeout_height}, current {current_height}"
            ),
        }
    }
}

impl std::error::Error for EscrowError {}

/// Manages escrow creation, release, and refund via a `PyanaEngine`.
///
/// # Example
///
/// ```ignore
/// use pyana_app_framework::escrow::EscrowManager;
/// use pyana_sdk::embed::{PyanaEngine, EngineConfig};
/// use pyana_turn::escrow::EscrowCondition;
///
/// let mut engine = PyanaEngine::new(EngineConfig::for_testing());
/// let mut mgr = EscrowManager::new(&mut engine);
///
/// let escrow_id = mgr.create_payment_escrow(
///     from_cell, to_cell, 1000,
///     EscrowCondition::ProofPresented { verification_key: [0u8; 32] },
///     100,
/// ).unwrap();
/// ```
pub struct EscrowManager<'a> {
    engine: &'a mut PyanaEngine,
}

impl<'a> EscrowManager<'a> {
    /// Create a new escrow manager wrapping an engine.
    pub fn new(engine: &'a mut PyanaEngine) -> Self {
        Self { engine }
    }

    /// Create a payment escrow that locks `amount` from `from` for `to`.
    ///
    /// The escrow is released when `condition` is satisfied, or refundable
    /// after `timeout_height` blocks.
    ///
    /// Returns the escrow ID on success.
    pub fn create_payment_escrow(
        &mut self,
        from: CellId,
        to: CellId,
        amount: u64,
        condition: EscrowCondition,
        timeout: u64,
    ) -> Result<[u8; 32], EscrowError> {
        // Derive a deterministic escrow ID from parameters.
        let escrow_id = compute_escrow_id(&from, &to, amount, timeout);

        let action = Action {
            target: from,
            method: symbol("create_escrow"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::CreateEscrow {
                cell: from,
                recipient: to,
                amount,
                condition,
                timeout_height: timeout,
                escrow_id,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = Turn {
            agent: from,
            nonce: timeout,
            call_forest: CallForest {
                roots: vec![CallTree::new(action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some(format!(
                "create escrow: {amount} locked until height {timeout}"
            )),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        self.engine
            .execute_turn(&turn)
            .map_err(|e| EscrowError::TurnRejected(e.to_string()))?;

        Ok(escrow_id)
    }

    /// Release an escrow by providing a proof that satisfies its condition.
    ///
    /// The escrowed amount transfers to the recipient.
    pub fn release_with_proof(
        &mut self,
        escrow_id: [u8; 32],
        proof: &[u8],
    ) -> Result<(), EscrowError> {
        // We use a sentinel agent for the release turn (the executor validates
        // the proof against the escrow condition, not the agent identity).
        let agent = CellId::from_bytes(escrow_id);

        let action = Action {
            target: agent,
            method: symbol("release_escrow"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::ReleaseEscrow {
                escrow_id,
                proof: Some(proof.to_vec()),
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = Turn {
            agent,
            nonce: 0,
            call_forest: CallForest {
                roots: vec![CallTree::new(action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some("release escrow with proof".to_string()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        self.engine
            .execute_turn(&turn)
            .map_err(|e| EscrowError::TurnRejected(e.to_string()))?;

        Ok(())
    }

    /// Refund an escrow after its timeout height has passed.
    ///
    /// The escrowed amount returns to the original creator.
    pub fn refund_expired(
        &mut self,
        escrow_id: [u8; 32],
        current_height: u64,
    ) -> Result<(), EscrowError> {
        let agent = CellId::from_bytes(escrow_id);

        let action = Action {
            target: agent,
            method: symbol("refund_escrow"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::RefundEscrow { escrow_id }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = Turn {
            agent,
            nonce: current_height,
            call_forest: CallForest {
                roots: vec![CallTree::new(action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some(format!("refund expired escrow at height {current_height}")),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        self.engine
            .execute_turn(&turn)
            .map_err(|e| EscrowError::TurnRejected(e.to_string()))?;

        Ok(())
    }
}

/// Compute a deterministic escrow ID from its creation parameters.
fn compute_escrow_id(from: &CellId, to: &CellId, amount: u64, timeout: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-app-framework-escrow-id-v1");
    hasher.update(from.as_bytes());
    hasher.update(to.as_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(&timeout.to_le_bytes());
    *hasher.finalize().as_bytes()
}
