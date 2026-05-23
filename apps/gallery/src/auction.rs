//! Auction engine: manages the full lifecycle of artwork auctions.
//!
//! Lifecycle: Open → Bidding → Reveal → Settlement → Settled
//!
//! The auction engine coordinates between the bidding module (commit-reveal),
//! the settlement module (atomic transfer via TurnComposer), and the provenance
//! module (ownership chain updates).

use std::sync::Arc;

use tokio::sync::RwLock;

use pyana_app_framework::store::ContentStore;
use pyana_app_framework::{CellId, PyanaEngine};

use crate::bidding::{BiddingError, CommitRevealBidding};
use crate::settlement::{AtomicSettlement, SettlementError};
use crate::{
    Auction, AuctionId, AuctionPhase, AuctionResponse, BidCommitment, RevealedBid,
    compute_auction_id, id_to_hex, phase_label,
};

/// Errors from auction operations.
#[derive(Debug, Clone)]
pub enum AuctionError {
    /// Artwork not found.
    ArtworkNotFound(String),
    /// Auction not found.
    AuctionNotFound(String),
    /// Not the artwork owner.
    NotOwner,
    /// Artwork already has an active auction.
    AlreadyActive(String),
    /// Bidding error.
    Bidding(BiddingError),
    /// Settlement error.
    Settlement(String),
    /// Invalid phase transition.
    InvalidPhase { expected: String, actual: String },
    /// Duration too short.
    DurationTooShort { min_blocks: u64, given: u64 },
}

impl std::fmt::Display for AuctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ArtworkNotFound(id) => write!(f, "artwork not found: {id}"),
            Self::AuctionNotFound(id) => write!(f, "auction not found: {id}"),
            Self::NotOwner => write!(f, "caller is not the artwork owner"),
            Self::AlreadyActive(id) => write!(f, "artwork already has active auction: {id}"),
            Self::Bidding(e) => write!(f, "bidding error: {e}"),
            Self::Settlement(msg) => write!(f, "settlement error: {msg}"),
            Self::InvalidPhase { expected, actual } => {
                write!(f, "expected phase {expected}, got {actual}")
            }
            Self::DurationTooShort { min_blocks, given } => {
                write!(
                    f,
                    "duration too short: minimum {min_blocks} blocks, given {given}"
                )
            }
        }
    }
}

impl std::error::Error for AuctionError {}

impl From<BiddingError> for AuctionError {
    fn from(e: BiddingError) -> Self {
        AuctionError::Bidding(e)
    }
}

impl From<SettlementError> for AuctionError {
    fn from(e: SettlementError) -> Self {
        AuctionError::Settlement(e.to_string())
    }
}

/// Minimum bidding phase duration (blocks).
pub const MIN_BIDDING_DURATION: u64 = 5;

/// Minimum reveal phase duration (blocks).
pub const MIN_REVEAL_DURATION: u64 = 3;

/// The auction engine manages all active and completed auctions.
#[derive(Clone)]
pub struct AuctionEngine {
    /// All auctions indexed by ID.
    auctions: ContentStore<Auction>,
    /// Mapping from artwork_id -> active auction_id.
    active_by_artwork: Arc<RwLock<std::collections::HashMap<[u8; 32], [u8; 32]>>>,
    /// Current simulated block height.
    current_height: Arc<RwLock<u64>>,
}

impl AuctionEngine {
    /// Create a new auction engine.
    pub fn new() -> Self {
        Self {
            auctions: ContentStore::new(),
            active_by_artwork: Arc::new(RwLock::new(std::collections::HashMap::new())),
            current_height: Arc::new(RwLock::new(0)),
        }
    }

    /// Get the current block height.
    pub async fn current_height(&self) -> u64 {
        *self.current_height.read().await
    }

    /// Advance the block height.
    pub async fn advance_height(&self, delta: u64) {
        let mut h = self.current_height.write().await;
        *h += delta;
    }

    /// Set the block height explicitly.
    pub async fn set_height(&self, height: u64) {
        let mut h = self.current_height.write().await;
        *h = height;
    }

    /// Create a new auction for an artwork.
    pub async fn create_auction(
        &self,
        artwork_id: [u8; 32],
        artist: CellId,
        reserve_price: u64,
        bidding_duration: u64,
        reveal_duration: u64,
    ) -> Result<AuctionId, AuctionError> {
        // Validate durations.
        if bidding_duration < MIN_BIDDING_DURATION {
            return Err(AuctionError::DurationTooShort {
                min_blocks: MIN_BIDDING_DURATION,
                given: bidding_duration,
            });
        }
        if reveal_duration < MIN_REVEAL_DURATION {
            return Err(AuctionError::DurationTooShort {
                min_blocks: MIN_REVEAL_DURATION,
                given: reveal_duration,
            });
        }

        // Check no active auction for this artwork.
        let active = self.active_by_artwork.read().await;
        if active.contains_key(&artwork_id) {
            return Err(AuctionError::AlreadyActive(id_to_hex(&artwork_id)));
        }
        drop(active);

        let current_height = self.current_height().await;
        let auction_id = compute_auction_id(&artwork_id, current_height);

        let auction = Auction {
            id: auction_id,
            artwork_id,
            artist,
            phase: AuctionPhase::Bidding,
            bidding_end_height: current_height + bidding_duration,
            reveal_end_height: current_height + bidding_duration + reveal_duration,
            reserve_price,
            commitments: Vec::new(),
            revealed_bids: Vec::new(),
            created_at: current_height,
        };

        self.auctions.insert(auction_id, auction).await;
        self.active_by_artwork
            .write()
            .await
            .insert(artwork_id, auction_id);

        Ok(auction_id)
    }

    /// Submit a bid commitment to an auction.
    pub async fn submit_bid(
        &self,
        auction_id: &AuctionId,
        commitment: [u8; 32],
        bidder: CellId,
        escrow_id: [u8; 32],
    ) -> Result<(), AuctionError> {
        let auction = self
            .auctions
            .get(auction_id)
            .await
            .ok_or_else(|| AuctionError::AuctionNotFound(id_to_hex(auction_id)))?;

        // Check phase.
        if auction.phase != AuctionPhase::Bidding {
            return Err(AuctionError::InvalidPhase {
                expected: "bidding".to_string(),
                actual: phase_label(&auction.phase).to_string(),
            });
        }

        let current_height = self.current_height().await;
        if current_height >= auction.bidding_end_height {
            return Err(AuctionError::InvalidPhase {
                expected: "bidding".to_string(),
                actual: "bidding_expired".to_string(),
            });
        }

        // Use bidding engine to validate.
        let mut bidding = CommitRevealBidding::from_state(
            auction.commitments.clone(),
            Vec::new(),
            auction.reserve_price,
        );

        bidding.submit_commitment(commitment, bidder, escrow_id, current_height)?;

        // Update auction state.
        let new_commitment = BidCommitment {
            commitment,
            bidder,
            escrow_id,
            submitted_at: current_height,
        };

        self.auctions
            .update(auction_id, |a| {
                a.commitments.push(new_commitment);
            })
            .await;

        Ok(())
    }

    /// Reveal a bid during the reveal phase.
    pub async fn reveal_bid(
        &self,
        auction_id: &AuctionId,
        commitment: [u8; 32],
        bidder: CellId,
        amount: u64,
        nonce: [u8; 32],
    ) -> Result<(), AuctionError> {
        let mut auction = self
            .auctions
            .get(auction_id)
            .await
            .ok_or_else(|| AuctionError::AuctionNotFound(id_to_hex(auction_id)))?;

        // Auto-advance phase if needed.
        let current_height = self.current_height().await;
        if auction.phase == AuctionPhase::Bidding && current_height >= auction.bidding_end_height {
            auction.phase = AuctionPhase::Reveal;
            self.auctions
                .update(auction_id, |a| {
                    a.phase = AuctionPhase::Reveal;
                })
                .await;
        }

        if auction.phase != AuctionPhase::Reveal {
            return Err(AuctionError::InvalidPhase {
                expected: "reveal".to_string(),
                actual: phase_label(&auction.phase).to_string(),
            });
        }

        if current_height >= auction.reveal_end_height {
            return Err(AuctionError::InvalidPhase {
                expected: "reveal".to_string(),
                actual: "reveal_expired".to_string(),
            });
        }

        // Use bidding engine to validate reveal.
        let mut bidding = CommitRevealBidding::from_state(
            auction.commitments.clone(),
            auction.revealed_bids.clone(),
            auction.reserve_price,
        );

        bidding.reveal_bid(commitment, bidder, amount, nonce)?;

        // Update auction state.
        let revealed = RevealedBid {
            commitment,
            bidder,
            amount,
            nonce,
        };

        self.auctions
            .update(auction_id, |a| {
                a.revealed_bids.push(revealed);
            })
            .await;

        Ok(())
    }

    /// Advance the auction phase (call this when block heights advance).
    ///
    /// Returns the new phase if a transition occurred.
    pub async fn advance_phase(&self, auction_id: &AuctionId) -> Option<AuctionPhase> {
        let auction = self.auctions.get(auction_id).await?;
        let current_height = self.current_height().await;

        let new_phase = match auction.phase {
            AuctionPhase::Bidding if current_height >= auction.bidding_end_height => {
                if auction.commitments.is_empty() {
                    AuctionPhase::NoBids
                } else {
                    AuctionPhase::Reveal
                }
            }
            AuctionPhase::Reveal if current_height >= auction.reveal_end_height => {
                AuctionPhase::Settling
            }
            _ => return None,
        };

        self.auctions
            .update(auction_id, |a| {
                a.phase = new_phase.clone();
            })
            .await;

        // Remove from active if terminal.
        if matches!(new_phase, AuctionPhase::NoBids) {
            self.active_by_artwork
                .write()
                .await
                .remove(&auction.artwork_id);
        }

        Some(new_phase)
    }

    /// Settle an auction: determine winner, execute atomic transfer, refund losers.
    pub async fn settle(
        &self,
        auction_id: &AuctionId,
        engine: &mut PyanaEngine,
    ) -> Result<AuctionPhase, AuctionError> {
        let auction = self
            .auctions
            .get(auction_id)
            .await
            .ok_or_else(|| AuctionError::AuctionNotFound(id_to_hex(auction_id)))?;

        if auction.phase != AuctionPhase::Settling {
            return Err(AuctionError::InvalidPhase {
                expected: "settling".to_string(),
                actual: phase_label(&auction.phase).to_string(),
            });
        }

        let bidding = CommitRevealBidding::from_state(
            auction.commitments.clone(),
            auction.revealed_bids.clone(),
            auction.reserve_price,
        );

        let winner = bidding.determine_winner();
        if winner.is_none() {
            // No valid bids above reserve.
            let phase = AuctionPhase::NoBids;
            self.auctions
                .update(auction_id, |a| {
                    a.phase = phase.clone();
                })
                .await;
            self.active_by_artwork
                .write()
                .await
                .remove(&auction.artwork_id);
            return Ok(phase);
        }

        let winner = winner.unwrap();
        let winning_bid = winner.amount;
        let winner_cell = winner.bidder;
        let winner_commitment = winner.commitment;

        // Find the winner's escrow.
        let winner_escrow = auction
            .commitments
            .iter()
            .find(|c| c.commitment == winner_commitment)
            .map(|c| c.escrow_id)
            .unwrap_or([0u8; 32]);

        // Execute atomic settlement: artwork ownership transfer + payment.
        let settlement = AtomicSettlement {
            artwork_id: auction.artwork_id,
            artist: auction.artist,
            winner: winner_cell,
            winning_bid,
            winner_escrow_id: winner_escrow,
        };

        let receipt_hash = settlement.execute(engine)?;

        // Refund losing bidders.
        let losers = bidding.losing_bids();
        for loser in &losers {
            let loser_escrow = auction
                .commitments
                .iter()
                .find(|c| c.commitment == loser.commitment)
                .map(|c| c.escrow_id)
                .unwrap_or([0u8; 32]);

            // Best-effort refund; log but don't fail settlement.
            if let Err(e) = AtomicSettlement::refund_loser(engine, loser_escrow) {
                tracing::warn!(
                    escrow_id = %id_to_hex(&loser_escrow),
                    error = %e,
                    "failed to refund losing bidder"
                );
            }
        }

        let settled_phase = AuctionPhase::Settled {
            winner: winner_cell,
            winning_bid,
            receipt_hash,
        };

        self.auctions
            .update(auction_id, |a| {
                a.phase = settled_phase.clone();
            })
            .await;

        self.active_by_artwork
            .write()
            .await
            .remove(&auction.artwork_id);

        Ok(settled_phase)
    }

    /// Get an auction by ID.
    pub async fn get(&self, id: &AuctionId) -> Option<Auction> {
        self.auctions.get(id).await
    }

    /// List all auctions as raw (id, Auction) pairs (for persistence).
    pub async fn list_raw(&self) -> Vec<([u8; 32], Auction)> {
        self.auctions.list().await
    }

    /// Insert a raw auction (for persistence restore).
    pub async fn insert_raw(&self, auction: Auction) {
        let id = auction.id;
        let artwork_id = auction.artwork_id;
        let is_active = matches!(
            auction.phase,
            crate::AuctionPhase::Bidding
                | crate::AuctionPhase::Reveal
                | crate::AuctionPhase::Settling
        );
        self.auctions.insert(id, auction).await;
        if is_active {
            self.active_by_artwork.write().await.insert(artwork_id, id);
        }
    }

    /// List all auctions as responses.
    pub async fn list_all(&self) -> Vec<AuctionResponse> {
        self.auctions
            .list()
            .await
            .into_iter()
            .map(|(_, a)| self.auction_to_response(&a))
            .collect()
    }

    /// List active auctions (bidding or reveal phase).
    pub async fn list_active(&self) -> Vec<AuctionResponse> {
        self.auctions
            .find(|a| matches!(a.phase, AuctionPhase::Bidding | AuctionPhase::Reveal))
            .await
            .into_iter()
            .map(|(_, a)| self.auction_to_response(&a))
            .collect()
    }

    /// Convert an Auction to its API response form.
    pub fn auction_to_response(&self, auction: &Auction) -> AuctionResponse {
        let (winner, winning_bid) = match &auction.phase {
            AuctionPhase::Settled {
                winner,
                winning_bid,
                ..
            } => (Some(id_to_hex(winner.as_bytes())), Some(*winning_bid)),
            _ => (None, None),
        };

        let highest_revealed = auction.revealed_bids.iter().map(|r| r.amount).max();

        AuctionResponse {
            id: id_to_hex(&auction.id),
            artwork_id: id_to_hex(&auction.artwork_id),
            artist: id_to_hex(auction.artist.as_bytes()),
            phase: phase_label(&auction.phase).to_string(),
            bidding_end_height: auction.bidding_end_height,
            reveal_end_height: auction.reveal_end_height,
            reserve_price: auction.reserve_price,
            commitment_count: auction.commitments.len(),
            revealed_count: auction.revealed_bids.len(),
            highest_revealed_bid: highest_revealed,
            winner,
            winning_bid,
        }
    }
}
