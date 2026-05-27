//! Bridge between the blocklace data structure and dregg's turn execution model.
//!
//! This module classifies turns into execution tiers and processes finalized blocks
//! into turn receipts that the dregg executor can apply.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::finality::{BlockId, Blocklace, Payload, TurnArtifactBundle};

// ─── Execution Tiers ─────────────────────────────────────────────────────────

/// The execution tier determines how a turn is processed.
///
/// Sovereign turns execute immediately (single-cell, no cross-cell effects).
/// Optimistic turns execute speculatively (COD budget permits).
/// Ordered turns require total ordering from consensus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExecutionTier {
    /// Single-cell turn with no cross-cell reads/writes. Executes immediately
    /// at the submitter's node without waiting for consensus.
    Sovereign,
    /// Multi-cell turn within COD budget. Executes optimistically with rollback
    /// if a conflict is later detected.
    Optimistic,
    /// Turn that requires total ordering from the blocklace consensus layer.
    /// Either exceeds COD budget or touches contested state.
    Ordered,
}

/// Classify a turn payload into an execution tier.
///
/// The classification examines the serialized turn to determine whether it
/// touches only sovereign state, fits within optimistic COD budget, or needs
/// full ordering.
pub fn classify_turn(turn_bytes: &[u8], cod_manager: &CodManager) -> ExecutionTier {
    // A turn that's too small to be valid needs ordering (conservative).
    if turn_bytes.len() < 8 {
        return ExecutionTier::Ordered;
    }

    // Check if the turn is marked as sovereign (first byte marker).
    // This is a simplified classification; real implementation would deserialize
    // the Turn and inspect its call forest.
    match turn_bytes[0] {
        0x01 => ExecutionTier::Sovereign,
        0x02 if cod_manager.has_budget() => ExecutionTier::Optimistic,
        _ => ExecutionTier::Ordered,
    }
}

// ─── COD (Concurrent Optimistic Debits) ──────────────────────────────────────

/// Budget for a single COD slot.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CodBudget {
    /// Maximum outstanding optimistic turns before requiring confirmation.
    pub max_outstanding: usize,
    /// Current number of outstanding (unconfirmed) optimistic turns.
    pub outstanding: usize,
}

/// Manages COD budgets for optimistic turn execution.
///
/// COD allows turns to execute speculatively without waiting for total ordering,
/// as long as the potential rollback cost stays within budget.
#[derive(Clone, Debug, Default)]
pub struct CodManager {
    /// Per-cell COD budgets.
    budgets: HashMap<[u8; 32], CodBudget>,
    /// Default budget for cells without explicit configuration.
    default_max: usize,
}

impl CodManager {
    /// Create a new COD manager with the given default max outstanding turns.
    pub fn new(default_max: usize) -> Self {
        CodManager {
            budgets: HashMap::new(),
            default_max,
        }
    }

    /// Check if any budget remains for optimistic execution.
    pub fn has_budget(&self) -> bool {
        self.default_max > 0
    }

    /// Check if a specific cell has COD budget remaining.
    pub fn has_budget_for(&self, cell_id: &[u8; 32]) -> bool {
        match self.budgets.get(cell_id) {
            Some(budget) => budget.outstanding < budget.max_outstanding,
            None => true, // Default: allow if under default max
        }
    }

    /// Consume one unit of COD budget for a cell.
    pub fn consume(&mut self, cell_id: &[u8; 32]) {
        let budget = self.budgets.entry(*cell_id).or_insert(CodBudget {
            max_outstanding: self.default_max,
            outstanding: 0,
        });
        budget.outstanding += 1;
    }

    /// Release one unit of COD budget (turn confirmed or rolled back).
    pub fn release(&mut self, cell_id: &[u8; 32]) {
        if let Some(budget) = self.budgets.get_mut(cell_id) {
            budget.outstanding = budget.outstanding.saturating_sub(1);
        }
    }
}

// ─── Turn Receipts ───────────────────────────────────────────────────────────

/// Receipt produced when a blocklace block containing a turn reaches finality.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceTurnReceipt {
    /// The block ID that contained this turn.
    pub block_id: BlockId,
    /// The creator who submitted this turn.
    pub submitter: [u8; 32],
    /// Sequence number in the submitter's virtual chain.
    pub seq: u64,
    /// The serialized turn data.
    pub turn_data: Vec<u8>,
    /// The execution tier that was assigned.
    pub tier: ExecutionTier,
    /// The finality height at which this turn was confirmed.
    pub finality_height: u64,
}

// ─── Bridge ──────────────────────────────────────────────────────────────────

/// Bridge between the blocklace consensus layer and dregg's turn executor.
///
/// Responsibilities:
/// - Classify incoming turns into execution tiers
/// - Submit turns as blocks to the blocklace
/// - Process finalized blocks into turn receipts
pub struct DreggBlocklaceBridge {
    /// COD manager for optimistic execution budgeting.
    pub cod: CodManager,
    /// Finality height counter.
    finality_height: u64,
    /// Number of ordered blocks already processed (cursor into the ordered list).
    processed_cursor: usize,
}

impl DreggBlocklaceBridge {
    /// Create a new bridge with the given COD budget.
    pub fn new(cod_budget: usize) -> Self {
        DreggBlocklaceBridge {
            cod: CodManager::new(cod_budget),
            finality_height: 0,
            processed_cursor: 0,
        }
    }

    /// Submit a turn to the blocklace.
    ///
    /// The turn is wrapped in a `Payload::Turn` block and added to the blocklace.
    /// Returns the block ID assigned to this turn.
    pub fn submit_turn(&self, blocklace: &mut Blocklace, turn_data: Vec<u8>) -> BlockId {
        let block = blocklace.add_block(Payload::Turn(turn_data));
        block.id()
    }

    /// Submit a turn plus receipt/witness material to the blocklace.
    pub fn submit_turn_bundle(
        &self,
        blocklace: &mut Blocklace,
        bundle: TurnArtifactBundle,
    ) -> BlockId {
        let block = blocklace.add_block(Payload::TurnBundle(bundle));
        block.id()
    }

    /// Process finalized blocks and produce turn receipts.
    ///
    /// Examines the ordered sequence in the finality tracker and produces
    /// receipts for any newly-ordered Turn-payload blocks since the last call.
    /// Only processes blocks that haven't been processed yet (idempotent cursor).
    pub fn process_finalized(&mut self, blocklace: &Blocklace) -> Vec<BlocklaceTurnReceipt> {
        let ordered = &blocklace.finality.ordering.ordered;
        let mut receipts = Vec::new();

        // Only process blocks we haven't seen yet.
        let new_blocks = &ordered[self.processed_cursor..];

        for block_id in new_blocks {
            if let Some(block) = blocklace.get(block_id) {
                if let Some(data) = match &block.payload {
                    Payload::Turn(data) => Some(data),
                    Payload::TurnBundle(bundle) => Some(&bundle.signed_turn),
                    _ => None,
                } {
                    self.finality_height += 1;
                    let tier = classify_turn(data, &self.cod);
                    receipts.push(BlocklaceTurnReceipt {
                        block_id: *block_id,
                        submitter: block.creator,
                        seq: block.seq,
                        turn_data: data.clone(),
                        tier,
                        finality_height: self.finality_height,
                    });
                }
            }
        }

        self.processed_cursor = ordered.len();
        receipts
    }

    /// Get the current finality height (number of turns processed so far).
    pub fn finality_height(&self) -> u64 {
        self.finality_height
    }
}
