//! Turn: the full atomic transaction unit.
//!
//! A Turn wraps a CallForest with metadata: who initiated it, replay protection
//! via nonce, fee payment, and optional memo/expiration.

use pyana_cell::{CellId, LedgerDelta};
use serde::{Deserialize, Serialize};

use crate::error::TurnError;
use crate::forest::CallForest;

/// A Turn is the atomic unit of agent execution.
///
/// It packages a call forest (the tree of actions) with metadata needed for
/// transaction processing: agent identity, replay protection, fee, and validity.
///
/// Analogous to Mina's ZkappCommand.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Turn {
    /// The agent cell that initiated this turn.
    pub agent: CellId,
    /// The agent's nonce (monotonically increasing, for replay protection).
    pub nonce: u64,
    /// The call forest containing all actions.
    pub call_forest: CallForest,
    /// Computron fee for this turn (paid by the agent cell).
    pub fee: u64,
    /// Optional human-readable memo.
    pub memo: Option<String>,
    /// Optional expiration timestamp (unix seconds). If set, the turn is invalid
    /// after this time.
    pub valid_until: Option<i64>,
}

impl Turn {
    /// Compute the BLAKE3 hash of this turn (includes all fields).
    pub fn hash(&mut self) -> [u8; 32] {
        let forest_hash = self.call_forest.hash();
        let mut hasher = blake3::Hasher::new();
        hasher.update(self.agent.as_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        hasher.update(&forest_hash);
        hasher.update(&self.fee.to_le_bytes());
        if let Some(ref memo) = self.memo {
            hasher.update(memo.as_bytes());
        }
        if let Some(valid_until) = self.valid_until {
            hasher.update(&valid_until.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// Get the total number of actions in this turn.
    pub fn action_count(&self) -> usize {
        self.call_forest.action_count()
    }
}

/// The result of applying a turn to a ledger.
#[derive(Clone, Debug)]
pub enum TurnResult {
    /// The turn was successfully committed.
    Committed {
        /// The delta describing all ledger changes.
        ledger_delta: LedgerDelta,
        /// A receipt containing hashes and metadata about the committed turn.
        receipt: TurnReceipt,
        /// Total computrons consumed by this turn.
        computrons_used: u64,
    },
    /// The turn was rejected (no state changes).
    Rejected {
        /// What went wrong.
        reason: TurnError,
        /// Path in the call forest to the failing action (indices at each level).
        /// Empty if the failure is at the turn level (e.g., expired, bad nonce).
        at_action: Vec<usize>,
    },
}

impl TurnResult {
    /// Returns true if the turn committed successfully.
    pub fn is_committed(&self) -> bool {
        matches!(self, TurnResult::Committed { .. })
    }

    /// Returns true if the turn was rejected.
    pub fn is_rejected(&self) -> bool {
        matches!(self, TurnResult::Rejected { .. })
    }

    /// Unwrap a committed result, panicking if rejected.
    pub fn unwrap_committed(self) -> (LedgerDelta, TurnReceipt, u64) {
        match self {
            TurnResult::Committed { ledger_delta, receipt, computrons_used } => {
                (ledger_delta, receipt, computrons_used)
            }
            TurnResult::Rejected { reason, at_action } => {
                panic!("turn was rejected at {:?}: {}", at_action, reason)
            }
        }
    }

    /// Unwrap a rejected result, panicking if committed.
    pub fn unwrap_rejected(self) -> (TurnError, Vec<usize>) {
        match self {
            TurnResult::Rejected { reason, at_action } => (reason, at_action),
            TurnResult::Committed { .. } => {
                panic!("turn was committed, expected rejection")
            }
        }
    }
}

/// A receipt produced when a turn is committed, providing cryptographic evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnReceipt {
    /// Hash of the full turn (agent + nonce + forest + fee + memo + valid_until).
    pub turn_hash: [u8; 32],
    /// Hash of the call forest alone.
    pub forest_hash: [u8; 32],
    /// Ledger Merkle root before this turn was applied.
    pub pre_state_hash: [u8; 32],
    /// Ledger Merkle root after this turn was applied.
    pub post_state_hash: [u8; 32],
    /// Timestamp when this turn was processed.
    pub timestamp: i64,
    /// Hash of all effects that were applied.
    pub effects_hash: [u8; 32],
    /// Total computrons consumed.
    pub computrons_used: u64,
    /// Number of actions in the forest.
    pub action_count: usize,
    /// Hash of the previous receipt in this agent's chain, or None for the first receipt.
    /// This links receipts into a per-agent chain for proof-carrying state.
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// The agent cell that produced this receipt (for chain attribution).
    pub agent: CellId,
}

impl TurnReceipt {
    /// Compute the BLAKE3 hash of this receipt (for chaining/inclusion proofs).
    pub fn receipt_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-receipt-v1");
        hasher.update(&self.turn_hash);
        hasher.update(&self.forest_hash);
        hasher.update(&self.pre_state_hash);
        hasher.update(&self.post_state_hash);
        hasher.update(&self.timestamp.to_le_bytes());
        hasher.update(&self.effects_hash);
        hasher.update(&self.computrons_used.to_le_bytes());
        hasher.update(&(self.action_count as u64).to_le_bytes());
        hasher.update(self.agent.as_bytes());
        match &self.previous_receipt_hash {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }
}
