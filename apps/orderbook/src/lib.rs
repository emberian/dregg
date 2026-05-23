//! # pyana-orderbook
//!
//! A decentralized financial trading orderbook matching engine built on Pyana primitives.
//!
//! ## Security Properties
//!
//! - **Provably fair matching**: Every fill is accompanied by a STARK proof that
//!   price-time priority was respected and no orders were skipped.
//! - **Book state commitment**: Merkle root of all live orders is committed to the
//!   federation, allowing any user to verify their order's inclusion.
//! - **Pre-trade escrow**: Orders must lock collateral via `CreateEscrow` before
//!   going live — settlement is guaranteed once a match occurs.
//! - **Commit-reveal order submission**: Orders are submitted as blinded commitments
//!   first, then revealed after a window — prevents frontrunning by the matcher.
//! - **Federation-backed execution**: The matching engine runs as a cell program
//!   on the federation, verified by consensus (not a single trusted process).
//! - **Dark pool privacy**: Committed orders hide amounts from the matcher; matching
//!   uses homomorphic range proofs for conservation without revealing values.
//!
//! ## Architecture
//!
//! Orders are posted as Pyana Intents. The commit-reveal protocol prevents MEV.
//! Pre-trade escrow guarantees settlement. The verified matching engine produces
//! proofs alongside every fill. Settlement is atomic via TurnComposer. The book
//! state Merkle root is committed to the federation after each state change.

pub mod blinded_queue;
pub mod book;
pub mod circuit;
pub mod commit_reveal;
pub mod escrow;
pub mod matching;
pub mod order;
pub mod private_order;
pub mod ring_trade;
pub mod server;
pub mod settlement;
pub mod state_commitment;
#[cfg(test)]
mod tests;
pub mod verified_matching;

// Re-export primary types for convenience.
pub use book::{OrderBook, TradingPair};
pub use matching::{Fill, MatchError, MatchResult, MatchingEngine};
pub use order::{Order, OrderId, OrderStatus, OrderType, Side, TimeInForce};
pub use verified_matching::{VerifiedMatchResult, VerifiedMatchingEngine};

/// The top-level engine that ties together the book, matching, settlement,
/// escrow, commit-reveal, and state commitment.
///
/// This is a "verified" engine: every match produces a cryptographic proof,
/// every order is collateralized, and the book state is committed to a Merkle
/// root that users can verify against.
pub struct OrderbookEngine {
    /// The order book.
    pub book: OrderBook,
    /// Current block height (for GTD expiration, escrow timeouts, and commit-reveal).
    pub current_height: u64,
    /// Oracle price for the trading pair (for stop-loss triggering).
    pub oracle_price: Option<u64>,
    /// Escrow registry: tracks collateral locks for live orders.
    pub escrows: escrow::EscrowRegistry,
    /// Commit-reveal registry: tracks blinded order commitments.
    pub commit_reveal: commit_reveal::CommitRevealRegistry,
    /// State sequence number (monotonically increasing).
    pub sequence: u64,
    /// The latest book state commitment (published to the federation).
    pub state_commitment: Option<state_commitment::BookStateCommitment>,
}

impl OrderbookEngine {
    /// Create a new engine for a trading pair.
    pub fn new(pair: TradingPair) -> Self {
        OrderbookEngine {
            book: OrderBook::new(pair),
            current_height: 0,
            oracle_price: None,
            escrows: escrow::EscrowRegistry::new(),
            commit_reveal: commit_reveal::CommitRevealRegistry::new(),
            sequence: 0,
            state_commitment: None,
        }
    }

    /// Submit an order commitment (commit phase of commit-reveal).
    ///
    /// The order content is hidden until the reveal phase. This prevents
    /// the matcher from frontrunning or reordering.
    pub fn commit_order(
        &mut self,
        commitment: commit_reveal::OrderCommitment,
    ) -> Result<(), commit_reveal::CommitRevealError> {
        self.commit_reveal.commit(commitment)
    }

    /// Reveal a previously committed order (reveal phase).
    ///
    /// After the commit window elapses, the order content is revealed and
    /// queued for batch matching.
    pub fn reveal_order(
        &mut self,
        reveal: commit_reveal::OrderReveal,
    ) -> Result<(), commit_reveal::CommitRevealError> {
        self.commit_reveal.reveal(reveal, self.current_height)
    }

    /// Submit an order directly (bypassing commit-reveal for testing/GTC resting orders).
    ///
    /// REQUIRES: the order must have a backing escrow already registered.
    /// This enforces the "no unfunded orders" invariant.
    pub fn submit_order(&mut self, order: Order) -> Result<VerifiedMatchResult, SubmitError> {
        // Verify escrow backing (orders must be collateralized).
        self.escrows
            .verify_collateral(&order)
            .map_err(SubmitError::EscrowError)?;

        match &order.order_type {
            OrderType::StopLoss { .. } => {
                // Stop-loss: store as pending, don't match yet.
                let result = MatchResult {
                    fills: vec![],
                    residual: Some(order),
                    fully_filled: false,
                    total_filled: 0,
                };
                Ok(VerifiedMatchResult {
                    result,
                    fill_proofs: vec![],
                    pre_state: self.current_state_commitment(),
                    post_state: self.current_state_commitment(),
                })
            }
            _ => {
                let verified = VerifiedMatchingEngine::match_order(
                    &mut self.book,
                    order,
                    self.current_height,
                    self.sequence,
                )
                .map_err(SubmitError::MatchError)?;

                // Update sequence and state commitment.
                self.sequence = verified.post_state.sequence;
                self.state_commitment = Some(verified.post_state.clone());

                Ok(verified)
            }
        }
    }

    /// Submit an order without requiring escrow (legacy path for testing).
    ///
    /// WARNING: This is the unverified path. In production, always use
    /// `submit_order` which enforces collateral.
    pub fn submit_order_unverified(&mut self, order: Order) -> Result<MatchResult, MatchError> {
        match &order.order_type {
            OrderType::StopLoss { .. } => Ok(MatchResult {
                fills: vec![],
                residual: Some(order),
                fully_filled: false,
                total_filled: 0,
            }),
            _ => MatchingEngine::match_order(&mut self.book, order),
        }
    }

    /// Process the reveal batch: match all revealed orders in commitment-time order.
    ///
    /// This is the fair matching entry point. Orders are processed in the order
    /// they were committed (first-committed = first-matched), preventing the
    /// matcher from reordering them.
    pub fn process_reveal_batch(&mut self) -> Vec<Result<VerifiedMatchResult, SubmitError>> {
        let orders = self.commit_reveal.drain_batch();
        let mut results = Vec::with_capacity(orders.len());

        for order in orders {
            results.push(self.submit_order(order));
        }

        results
    }

    /// Register an escrow for an order (called before submit_order).
    pub fn register_escrow(&mut self, escrow_record: escrow::OrderEscrow) {
        self.escrows.register(escrow_record);
    }

    /// Cancel an order. Returns the removed order and the escrow refund effect.
    ///
    /// Cancellation:
    /// 1. Verifies ownership via cancel proof.
    /// 2. Removes the order from the book.
    /// 3. Marks the escrow as consumed and returns a refund effect.
    pub fn cancel_order(
        &mut self,
        order_id: &OrderId,
        canceller: &pyana_types::CellId,
    ) -> Result<(Order, pyana_turn::action::Effect), CancelError> {
        // Verify ownership via cancel proof.
        let cancel_hash = circuit::compute_cancel_proof_hash(canceller, order_id);
        if !circuit::verify_cancel_proof(canceller, order_id, &cancel_hash) {
            return Err(CancelError::NotOwner);
        }

        // Check the order is actually on the book.
        let order = self.book.get_order(order_id).ok_or(CancelError::NotFound)?;

        // Verify the canceller is actually the owner.
        if order.trader != *canceller {
            return Err(CancelError::NotOwner);
        }

        let mut removed = self
            .book
            .remove_order(order_id)
            .ok_or(CancelError::NotFound)?;
        removed.status = OrderStatus::Cancelled;

        // Refund the escrow.
        let refund_effect = if let Ok(escrow_record) = self.escrows.consume(order_id) {
            escrow::build_cancel_refund_effect(&escrow_record)
        } else {
            // No escrow to refund (legacy order).
            pyana_turn::action::Effect::RefundEscrow {
                escrow_id: [0u8; 32],
            }
        };

        // Update state commitment.
        self.sequence += 1;
        self.state_commitment = Some(self.current_state_commitment());

        Ok((removed, refund_effect))
    }

    /// Update the oracle price and trigger any stop-loss orders that should activate.
    pub fn update_oracle_price(&mut self, new_price: u64) {
        self.oracle_price = Some(new_price);
        // In production, this would scan pending stop-loss orders and convert
        // triggered ones into market orders via ConditionalTurn resolution.
    }

    /// Advance the block height and expire GTD orders and stale commitments.
    pub fn advance_height(&mut self, new_height: u64) -> Vec<Order> {
        self.current_height = new_height;
        self.commit_reveal.expire_stale(new_height);
        let expired = self.book.expire_orders(new_height);

        if !expired.is_empty() {
            self.sequence += 1;
            self.state_commitment = Some(self.current_state_commitment());
        }

        expired
    }

    /// Get the current book state commitment.
    pub fn current_state_commitment(&self) -> state_commitment::BookStateCommitment {
        let orders = state_commitment::collect_live_orders(&self.book);
        let root = state_commitment::compute_merkle_root(&orders);
        state_commitment::BookStateCommitment {
            root,
            height: self.current_height,
            order_count: orders.len(),
            sequence: self.sequence,
        }
    }

    /// Generate an inclusion proof for a specific order (user verification).
    ///
    /// Users call this to get a proof that their order is included in the
    /// committed book state. They verify it against the published Merkle root.
    pub fn prove_order_inclusion(
        &self,
        order_id: &OrderId,
    ) -> Option<state_commitment::OrderInclusionProof> {
        let orders = state_commitment::collect_live_orders(&self.book);
        state_commitment::generate_inclusion_proof(&orders, order_id)
    }

    /// Verify an inclusion proof against the current state root.
    pub fn verify_order_inclusion(&self, proof: &state_commitment::OrderInclusionProof) -> bool {
        let commitment = self.current_state_commitment();
        state_commitment::verify_inclusion_proof(proof, &commitment.root)
    }
}

/// Errors from order submission (combines escrow and matching errors).
#[derive(Clone, Debug)]
pub enum SubmitError {
    /// The order does not have sufficient collateral backing.
    EscrowError(escrow::EscrowError),
    /// The matching or proof generation failed.
    MatchError(verified_matching::VerifiedMatchError),
}

impl std::fmt::Display for SubmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EscrowError(e) => write!(f, "escrow: {}", e),
            Self::MatchError(e) => write!(f, "match: {}", e),
        }
    }
}

/// Errors from order cancellation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CancelError {
    /// The order was not found on the book.
    NotFound,
    /// The canceller is not the owner of the order.
    NotOwner,
}

impl std::fmt::Display for CancelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound => write!(f, "order not found"),
            Self::NotOwner => write!(f, "canceller is not the order owner"),
        }
    }
}
