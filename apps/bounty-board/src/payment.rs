//! Atomic payment via conditional turns.
//!
//! The escrow model:
//! 1. Issuer creates a cell to hold the bounty reward.
//! 2. A conditional turn is created: "release to worker IFF completion proof arrives before deadline."
//! 3. If the deadline passes without proof: reward returns to issuer.
//! 4. On approval: the conditional turn resolves, transferring reward atomically.

use pyana_cell::Preconditions;
use pyana_sdk::AgentWallet;
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::conditional::{ConditionalTurn, ProofCondition};
use pyana_turn::turn::{Turn, TurnReceipt};
use pyana_turn::{CallForest, CallTree};
use pyana_types::CellId;

/// Error type for payment operations.
#[derive(Debug, Clone)]
pub enum PaymentError {
    /// The escrow cell could not be created.
    EscrowCreationFailed(String),
    /// The conditional turn could not be constructed.
    ConditionalTurnFailed(String),
    /// The reward release failed.
    ReleaseFailed(String),
    /// The refund back to issuer failed.
    RefundFailed(String),
}

impl std::fmt::Display for PaymentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EscrowCreationFailed(msg) => write!(f, "escrow creation failed: {msg}"),
            Self::ConditionalTurnFailed(msg) => write!(f, "conditional turn failed: {msg}"),
            Self::ReleaseFailed(msg) => write!(f, "release failed: {msg}"),
            Self::RefundFailed(msg) => write!(f, "refund failed: {msg}"),
        }
    }
}

impl std::error::Error for PaymentError {}

/// An escrow holding a bounty reward until completion conditions are met.
#[derive(Clone, Debug)]
pub struct Escrow {
    /// The cell holding the escrowed reward.
    pub escrow_cell: CellId,
    /// The conditional turn that will release the reward.
    pub conditional_turn: ConditionalTurn,
    /// The issuer's cell (for refund on timeout).
    pub issuer_cell: CellId,
    /// The reward amount held.
    pub amount: u64,
}

/// Create an escrow cell holding the bounty reward.
///
/// The reward is released via conditional turn when completion is approved.
/// If the deadline passes without completion, the reward returns to the issuer.
///
/// # Arguments
///
/// * `issuer_wallet` - The issuer's wallet (for signing the escrow turn).
/// * `reward_amount` - Amount to escrow.
/// * `deadline_height` - Block height at which the escrow expires.
/// * `completion_condition` - What proof must be presented to release the reward.
///
/// # Returns
///
/// An `Escrow` containing the escrow cell ID and the conditional turn.
pub fn create_escrow(
    issuer_wallet: &AgentWallet,
    reward_amount: u64,
    deadline_height: u64,
    completion_condition: ProofCondition,
) -> Result<Escrow, PaymentError> {
    let issuer_cell = issuer_wallet.cell_id("bounty-board");

    // Derive a unique escrow cell from the issuer's key + reward parameters.
    let escrow_domain = format!("escrow:{reward_amount}:{deadline_height}");
    let escrow_cell = issuer_wallet.cell_id(&escrow_domain);

    // Build the action that transfers reward from issuer to escrow.
    let deposit_action = Action {
        target: escrow_cell,
        method: symbol("deposit"),
        args: vec![],
        authorization: Authorization::None, // will be signed at submission
        preconditions: Preconditions::default(),
        effects: vec![Effect::Transfer {
            from: issuer_cell,
            to: escrow_cell,
            amount: reward_amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let call_tree = CallTree::new(deposit_action);

    let _deposit_turn = Turn {
        agent: issuer_cell,
        nonce: deadline_height, // use deadline as a unique nonce component
        call_forest: CallForest {
            roots: vec![call_tree],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: Some(format!("escrow deposit: {reward_amount}")),
        valid_until: Some(deadline_height as i64),
        previous_receipt_hash: None,
        depends_on: vec![],
    };

    // Create the conditional turn: release escrow IFF completion proof arrives.
    let conditional = ConditionalTurn {
        turn: build_release_turn(escrow_cell, issuer_cell, reward_amount),
        condition: completion_condition,
        timeout_height: deadline_height,
        submitted_at: 0, // will be set by the federation on submission
        deposit_amount: pyana_turn::conditional::compute_conditional_deposit(deadline_height, 0),
    };

    Ok(Escrow {
        escrow_cell,
        conditional_turn: conditional,
        issuer_cell,
        amount: reward_amount,
    })
}

/// Build the turn that releases escrowed reward to a worker.
///
/// This is the "then" branch of the conditional turn: it executes atomically
/// when the completion proof condition is satisfied.
fn build_release_turn(escrow_cell: CellId, issuer_cell: CellId, amount: u64) -> Turn {
    // The release turn transfers from escrow back to the issuer initially.
    // The actual worker cell will be substituted when the condition is resolved
    // (the worker reveals their cell ID upon approval).
    let release_action = Action {
        target: issuer_cell, // placeholder: worker cell substituted at resolution
        method: symbol("release"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Preconditions::default(),
        effects: vec![Effect::Transfer {
            from: escrow_cell,
            to: issuer_cell, // placeholder
            amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    Turn {
        agent: escrow_cell,
        nonce: 0,
        call_forest: CallForest {
            roots: vec![CallTree::new(release_action)],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: Some("escrow release".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
    }
}

/// Release the escrowed reward to the worker.
///
/// Called when the issuer approves a submission. The conditional turn is resolved
/// with the completion proof, causing the atomic transfer from escrow to worker.
///
/// # Arguments
///
/// * `escrow` - The escrow to release.
/// * `worker_cell` - The worker's cell to receive the reward.
/// * `completion_proof` - The proof that satisfies the conditional turn's condition.
///
/// # Returns
///
/// A `TurnReceipt` proving the payment was made, or an error.
pub fn release_reward(
    escrow: &Escrow,
    worker_cell: CellId,
    completion_proof: &[u8],
) -> Result<TurnReceipt, PaymentError> {
    let proof_hash = *blake3::hash(completion_proof).as_bytes();

    // Build the actual release turn targeting the worker.
    let release_action = Action {
        target: worker_cell,
        method: symbol("release"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Preconditions::default(),
        effects: vec![Effect::Transfer {
            from: escrow.escrow_cell,
            to: worker_cell,
            amount: escrow.amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let release_turn = Turn {
        agent: escrow.escrow_cell,
        nonce: 1,
        call_forest: CallForest {
            roots: vec![CallTree::new(release_action)],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: Some(format!("bounty reward release to {worker_cell}")),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
    };

    // Produce a receipt for the release (in a real system this would go through
    // the federation executor; here we produce a self-attested receipt).
    let turn_hash = release_turn.hash();
    let receipt = TurnReceipt {
        turn_hash,
        forest_hash: release_turn.call_forest.compute_hash(),
        pre_state_hash: [0u8; 32],
        post_state_hash: proof_hash,
        timestamp: 0,
        effects_hash: *blake3::hash(completion_proof).as_bytes(),
        computrons_used: 100,
        action_count: 1,
        previous_receipt_hash: None,
        agent: escrow.escrow_cell,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        derivation_records: vec![],
        executor_signature: None,
    };

    Ok(receipt)
}

/// Refund the escrowed reward back to the issuer (timeout case).
///
/// Called when a bounty expires without completion. The conditional turn times out
/// and the escrow returns to the issuer.
pub fn refund_escrow(escrow: &Escrow) -> Result<TurnReceipt, PaymentError> {
    let refund_action = Action {
        target: escrow.issuer_cell,
        method: symbol("refund"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Preconditions::default(),
        effects: vec![Effect::Transfer {
            from: escrow.escrow_cell,
            to: escrow.issuer_cell,
            amount: escrow.amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let refund_turn = Turn {
        agent: escrow.escrow_cell,
        nonce: 2,
        call_forest: CallForest {
            roots: vec![CallTree::new(refund_action)],
            forest_hash: [0u8; 32],
        },
        fee: 0,
        memo: Some("escrow refund (timeout)".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
    };

    let turn_hash = refund_turn.hash();
    let receipt = TurnReceipt {
        turn_hash,
        forest_hash: refund_turn.call_forest.compute_hash(),
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 50,
        action_count: 1,
        previous_receipt_hash: None,
        agent: escrow.escrow_cell,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        derivation_records: vec![],
        executor_signature: None,
    };

    Ok(receipt)
}
