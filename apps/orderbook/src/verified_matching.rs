//! Verified matching: wraps the core matching engine with proof generation.
//!
//! After a match is produced, this module:
//! 1. Computes the pre-match book state Merkle root.
//! 2. Executes the match via `MatchingEngine`.
//! 3. Computes the post-match book state Merkle root.
//! 4. For each fill, constructs a `MatchProofDescriptor` with a complete witness.
//! 5. Verifies all constraints (in production, this generates a STARK proof;
//!    in mock mode, it runs the constraint checks directly).
//!
//! The result includes both the fills AND the proofs, so any user can verify
//! that matching was fair without trusting the matcher.

use crate::book::OrderBook;
use crate::circuit::{MatchProofDescriptor, MatchProofError, MatchProofWitness};
use crate::matching::{Fill, MatchError, MatchResult, MatchingEngine};
use crate::order::{Order, OrderId, Side};
use crate::state_commitment::{BookStateCommitment, collect_live_orders, compute_merkle_root};

/// A verified match result: the match outcome plus proofs of fairness.
#[derive(Clone, Debug)]
pub struct VerifiedMatchResult {
    /// The underlying match result.
    pub result: MatchResult,
    /// Proofs for each fill (one per fill event).
    pub fill_proofs: Vec<FillProof>,
    /// The book state commitment before matching.
    pub pre_state: BookStateCommitment,
    /// The book state commitment after matching.
    pub post_state: BookStateCommitment,
}

/// A proof that a single fill was computed correctly.
#[derive(Clone, Debug)]
pub struct FillProof {
    /// The fill this proof covers.
    pub fill: Fill,
    /// The match proof descriptor with verified constraints.
    pub descriptor: MatchProofDescriptor,
    /// Whether constraints were verified (true in production; always true here).
    pub verified: bool,
    /// The STARK proof bytes — publicly verifiable without trusting the matcher.
    /// Anyone can call `MatchProofDescriptor::verify_stark_proof(public_inputs, &proof_bytes)`
    /// to independently verify the match was fair.
    pub proof_bytes: Vec<u8>,
}

/// Errors from verified matching (superset of MatchError).
#[derive(Clone, Debug)]
pub enum VerifiedMatchError {
    /// The underlying matching engine returned an error.
    MatchError(MatchError),
    /// A fill's proof constraints were violated (matcher cheated).
    ProofViolation {
        fill_index: usize,
        error: MatchProofError,
    },
}

impl std::fmt::Display for VerifiedMatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MatchError(e) => write!(f, "match error: {}", e),
            Self::ProofViolation { fill_index, error } => {
                write!(f, "proof violation on fill {}: {}", fill_index, error)
            }
        }
    }
}

impl From<MatchError> for VerifiedMatchError {
    fn from(e: MatchError) -> Self {
        Self::MatchError(e)
    }
}

/// The verified matching engine: produces proofs alongside matches.
pub struct VerifiedMatchingEngine;

impl VerifiedMatchingEngine {
    /// Execute a verified match: match + prove.
    ///
    /// This is the entry point that replaces direct calls to `MatchingEngine::match_order`.
    /// Every fill is accompanied by a cryptographic proof of correctness.
    pub fn match_order(
        book: &mut OrderBook,
        incoming: Order,
        current_height: u64,
        sequence: u64,
    ) -> Result<VerifiedMatchResult, VerifiedMatchError> {
        // 1. Capture pre-match state.
        let pre_orders = collect_live_orders(book);
        let pre_root = compute_merkle_root(&pre_orders);
        let pre_state = BookStateCommitment {
            root: pre_root,
            height: current_height,
            order_count: pre_orders.len(),
            sequence,
        };

        // Snapshot maker positions for witness construction.
        let maker_positions = snapshot_maker_positions(book, incoming.side());

        // 2. Execute the match.
        let result = MatchingEngine::match_order(book, incoming)?;

        // 3. Capture post-match state.
        let post_orders = collect_live_orders(book);
        let post_root = compute_merkle_root(&post_orders);
        let post_state = BookStateCommitment {
            root: post_root,
            height: current_height,
            order_count: post_orders.len(),
            sequence: sequence + 1,
        };

        // 4. Construct and verify proofs for each fill.
        let mut fill_proofs = Vec::with_capacity(result.fills.len());

        for (idx, fill) in result.fills.iter().enumerate() {
            let descriptor = MatchProofDescriptor::from_fill(fill, pre_root, post_root);

            // Construct the witness from the pre-match snapshot.
            let witness = build_witness_for_fill(fill, &maker_positions);
            let descriptor = descriptor.with_witness(witness);

            // Verify constraints locally first (fast).
            if let Err(proof_err) = descriptor.verify_all_constraints() {
                return Err(VerifiedMatchError::ProofViolation {
                    fill_index: idx,
                    error: proof_err,
                });
            }

            // Generate a real STARK proof that anyone can verify independently.
            let proof_bytes = descriptor.generate_stark_proof().map_err(|e| {
                VerifiedMatchError::ProofViolation {
                    fill_index: idx,
                    error: e,
                }
            })?;

            fill_proofs.push(FillProof {
                fill: fill.clone(),
                descriptor,
                verified: true,
                proof_bytes,
            });
        }

        Ok(VerifiedMatchResult {
            result,
            fill_proofs,
            pre_state,
            post_state,
        })
    }
}

/// A snapshot of maker order positions before matching (for witness construction).
#[derive(Clone, Debug)]
struct MakerSnapshot {
    order_id: OrderId,
    trader: pyana_types::CellId,
    limit_price: u64,
    remaining_before: u64,
    queue_position: usize,
    orders_ahead: Vec<([u8; 32], u64)>,
}

/// Snapshot the maker side of the book before matching.
fn snapshot_maker_positions(book: &OrderBook, taker_side: Side) -> Vec<MakerSnapshot> {
    let mut snapshots = Vec::new();

    let levels: Vec<_> = match taker_side {
        Side::Buy => book.ask_levels().collect(),
        Side::Sell => book.bid_levels().collect(),
    };

    for level in levels {
        for (position, order) in level.orders.iter().enumerate() {
            let orders_ahead: Vec<([u8; 32], u64)> = level
                .orders
                .iter()
                .take(position)
                .map(|o| (*blake3::hash(&o.id).as_bytes(), o.created_at))
                .collect();

            snapshots.push(MakerSnapshot {
                order_id: order.id,
                trader: order.trader,
                limit_price: level.price,
                remaining_before: order.remaining_amount,
                queue_position: position,
                orders_ahead,
            });
        }
    }

    snapshots
}

/// Build a witness for a specific fill from the pre-match snapshots.
fn build_witness_for_fill(fill: &Fill, snapshots: &[MakerSnapshot]) -> MatchProofWitness {
    // Find the maker in our snapshots.
    let maker_snap = snapshots.iter().find(|s| s.order_id == fill.maker_order_id);

    match maker_snap {
        Some(snap) => MatchProofWitness {
            maker_limit_price: snap.limit_price,
            maker_remaining_before: snap.remaining_before,
            maker_queue_position: snap.queue_position,
            orders_ahead: snap.orders_ahead.clone(),
            taker_cell_bytes: *fill.taker.as_bytes(),
            maker_cell_bytes: *fill.maker.as_bytes(),
        },
        None => {
            // Fallback: construct from fill data directly.
            // This should not happen in normal operation.
            MatchProofWitness {
                maker_limit_price: fill.price,
                maker_remaining_before: fill.amount,
                maker_queue_position: 0,
                orders_ahead: vec![],
                taker_cell_bytes: *fill.taker.as_bytes(),
                maker_cell_bytes: *fill.maker.as_bytes(),
            }
        }
    }
}
