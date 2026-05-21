//! Turn: the full atomic transaction unit.
//!
//! A Turn wraps a CallForest with metadata: who initiated it, replay protection
//! via nonce, fee payment, and optional memo/expiration.

use pyana_cell::{CellId, DerivationRecord, LedgerDelta};
use serde::{Deserialize, Serialize};

use crate::error::TurnError;
use crate::forest::CallForest;
use crate::routing::RoutingDirective;

/// A Turn is the atomic unit of agent execution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Turn {
    pub agent: CellId,
    pub nonce: u64,
    pub call_forest: CallForest,
    pub fee: u64,
    pub memo: Option<String>,
    pub valid_until: Option<i64>,
    #[serde(default)]
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// Hashes of turns this turn depends on (for pipeline/eventual-send semantics).
    #[serde(default)]
    pub depends_on: Vec<[u8; 32]>,
}

impl Turn {
    pub fn hash(&self) -> [u8; 32] {
        let forest_hash = self.call_forest.compute_hash();
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"pyana-turn-v2:");
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
        // Include depends_on to prevent dependency malleability.
        hasher.update(&(self.depends_on.len() as u64).to_le_bytes());
        for dep in &self.depends_on {
            hasher.update(dep);
        }
        // Include previous_receipt_hash to bind to causal ordering.
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

    pub fn action_count(&self) -> usize {
        self.call_forest.action_count()
    }
}

/// The result of applying a turn to a ledger.
#[derive(Clone, Debug)]
pub enum TurnResult {
    Committed {
        ledger_delta: LedgerDelta,
        receipt: TurnReceipt,
        computrons_used: u64,
    },
    Rejected {
        reason: TurnError,
        at_action: Vec<usize>,
    },
    /// The conditional turn's timeout height has been exceeded.
    /// No state change occurs and no fee is charged.
    Expired,
    /// The conditional turn's condition has not yet been satisfied.
    /// The turn remains in the pending pool.
    Pending,
}

impl TurnResult {
    pub fn is_committed(&self) -> bool {
        matches!(self, TurnResult::Committed { .. })
    }
    pub fn is_rejected(&self) -> bool {
        matches!(self, TurnResult::Rejected { .. })
    }
    pub fn is_expired(&self) -> bool {
        matches!(self, TurnResult::Expired)
    }
    pub fn is_pending(&self) -> bool {
        matches!(self, TurnResult::Pending)
    }

    pub fn unwrap_committed(self) -> (LedgerDelta, TurnReceipt, u64) {
        match self {
            TurnResult::Committed {
                ledger_delta,
                receipt,
                computrons_used,
            } => (ledger_delta, receipt, computrons_used),
            TurnResult::Rejected { reason, at_action } => {
                panic!("turn was rejected at {:?}: {}", at_action, reason)
            }
            TurnResult::Expired => panic!("turn was expired, expected committed"),
            TurnResult::Pending => panic!("turn is pending, expected committed"),
        }
    }

    pub fn unwrap_rejected(self) -> (TurnError, Vec<usize>) {
        match self {
            TurnResult::Rejected { reason, at_action } => (reason, at_action),
            TurnResult::Committed { .. } => panic!("turn was committed, expected rejection"),
            TurnResult::Expired => panic!("turn was expired, expected rejection"),
            TurnResult::Pending => panic!("turn is pending, expected rejection"),
        }
    }
}

/// A receipt produced when a turn is committed, providing cryptographic evidence.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnReceipt {
    pub turn_hash: [u8; 32],
    pub forest_hash: [u8; 32],
    pub pre_state_hash: [u8; 32],
    pub post_state_hash: [u8; 32],
    pub timestamp: i64,
    pub effects_hash: [u8; 32],
    pub computrons_used: u64,
    pub action_count: usize,
    pub previous_receipt_hash: Option<[u8; 32]>,
    pub agent: CellId,
    /// Routing directives emitted by three-party introductions in this turn.
    #[serde(default)]
    pub routing_directives: Vec<RoutingDirective>,
    /// Capability derivation records emitted by Grant, Introduce, SpawnWithDelegation,
    /// and Unseal effects in this turn. Verifiers use these to reconstruct the CDT.
    #[serde(default)]
    pub derivation_records: Vec<DerivationRecord>,
    /// Ed25519 signature from the executor over the receipt hash.
    /// When present, this cryptographically binds the receipt to a known executor,
    /// making the federation exit path verifiable (not just a self-reported chain).
    /// Contains exactly 64 bytes when set.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub executor_signature: Option<Vec<u8>>,
}

impl TurnReceipt {
    /// Compute the BLAKE3 hash of this receipt (for chaining/inclusion proofs).
    /// Note: executor_signature is NOT included (it signs the hash, not vice versa).
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
        hasher.update(&(self.routing_directives.len() as u64).to_le_bytes());
        for rd in &self.routing_directives {
            hasher.update(&rd.hash());
        }
        hasher.update(&(self.derivation_records.len() as u64).to_le_bytes());
        for dr in &self.derivation_records {
            hasher.update(&dr.hash());
        }
        *hasher.finalize().as_bytes()
    }
}
