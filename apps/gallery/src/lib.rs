//! Federated art gallery with commit-reveal auctions on the pyana protocol.
//!
//! # Architecture
//!
//! ```text
//! Federation nodes (3-node devnet)
//!     ↕ wire protocol
//! Gallery Backend (axum API server using pyana-sdk)
//!     ↕ REST/WebSocket
//! Browser Frontend (vanilla JS/HTML using WASM SDK + browser extension)
//! ```
//!
//! # Features
//!
//! - **Artwork Registration** — Artists register pieces with metadata and image hashes
//! - **Commit-Reveal Bidding** — Bid amounts hidden via BLAKE3 commitments until reveal
//! - **Auction Lifecycle** — Open → Bidding → Reveal → Settlement → Claimed
//! - **Atomic Settlement** — Winner's funds transferred to artist via TurnComposer
//! - **Provenance Chain** — Ownership history stored as capability delegations
//! - **Escrow** — Bidder's funds locked during auction
//! - **Live Updates** — WebSocket push for bid events and state changes

pub mod artwork;
pub mod auction;
pub mod bidding;
pub mod blinded_bids;
pub mod handlers;
pub mod notification_inbox;
pub mod persistence;
pub mod private_vickrey;
pub mod provenance;
pub mod server;
pub mod settlement;
pub mod tests;
pub mod ws;

use pyana_app_framework::CellId;
use pyana_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use serde::{Deserialize, Serialize};

// =============================================================================
// Core Types
// =============================================================================

/// Unique identifier for an artwork (content-addressed).
pub type ArtworkId = [u8; 32];

/// Unique identifier for an auction.
pub type AuctionId = [u8; 32];

/// A registered artwork in the gallery.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Artwork {
    /// Content-addressed artwork ID (BLAKE3 hash of creation parameters).
    pub id: ArtworkId,
    /// Human-readable title.
    pub title: String,
    /// Full description of the artwork.
    pub description: String,
    /// BLAKE3 hash of the artwork image (for IPFS/content-addressed lookup).
    pub image_hash: [u8; 32],
    /// The artist's cell identity.
    pub artist: CellId,
    /// The current owner's cell identity (initially the artist).
    pub current_owner: CellId,
    /// Reserve price (minimum acceptable bid).
    pub reserve_price: u64,
    /// Block height at which this artwork was registered.
    pub registered_at: u64,
    /// Tags for discovery.
    pub tags: Vec<String>,
}

/// The lifecycle status of an auction.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum AuctionPhase {
    /// Auction is open for bid commitments.
    Bidding,
    /// Bidding closed; bidders must reveal their bids.
    Reveal,
    /// All bids revealed; settlement in progress.
    Settling,
    /// Auction settled; artwork transferred to winner.
    Settled {
        winner: CellId,
        winning_bid: u64,
        receipt_hash: [u8; 32],
    },
    /// Auction ended with no valid bids (artwork returned to artist).
    NoBids,
    /// Auction was cancelled by the artist.
    Cancelled,
}

/// An auction for an artwork.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Auction {
    /// Unique auction ID.
    pub id: AuctionId,
    /// The artwork being auctioned.
    pub artwork_id: ArtworkId,
    /// The artist (seller) cell.
    pub artist: CellId,
    /// Current phase of the auction.
    pub phase: AuctionPhase,
    /// Block height at which bidding ends.
    pub bidding_end_height: u64,
    /// Block height at which reveal phase ends.
    pub reveal_end_height: u64,
    /// Reserve price (minimum acceptable bid).
    pub reserve_price: u64,
    /// All bid commitments received (BLAKE3 hashes).
    pub commitments: Vec<BidCommitment>,
    /// Revealed bids (populated during reveal phase).
    pub revealed_bids: Vec<RevealedBid>,
    /// Block height at which this auction was created.
    pub created_at: u64,
}

/// A committed (hidden) bid.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BidCommitment {
    /// The commitment hash: BLAKE3(bidder_cell || amount || nonce).
    pub commitment: [u8; 32],
    /// The bidder's cell (public — needed for escrow).
    pub bidder: CellId,
    /// Escrow ID locking the bidder's funds.
    pub escrow_id: [u8; 32],
    /// Block height at which this commitment was submitted.
    pub submitted_at: u64,
}

/// A revealed bid (after the reveal phase opens).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevealedBid {
    /// The original commitment hash (must match a BidCommitment).
    pub commitment: [u8; 32],
    /// The bidder's cell.
    pub bidder: CellId,
    /// The revealed bid amount.
    pub amount: u64,
    /// The nonce used in the commitment.
    pub nonce: [u8; 32],
}

/// An entry in the provenance (ownership history) chain.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProvenanceEntry {
    /// Previous owner's cell.
    pub from: CellId,
    /// New owner's cell.
    pub to: CellId,
    /// Sale price (0 for initial registration).
    pub price: u64,
    /// Block height of the transfer.
    pub block_height: u64,
    /// Hash of the turn receipt that effected this transfer.
    pub receipt_hash: [u8; 32],
}

// =============================================================================
// Request / Response Types
// =============================================================================

/// Request to register a new artwork.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RegisterArtworkRequest {
    pub title: String,
    pub description: String,
    /// Hex-encoded BLAKE3 hash of the image data.
    pub image_hash: String,
    /// Hex-encoded artist cell ID.
    pub artist_cell: String,
    pub reserve_price: u64,
    pub tags: Vec<String>,
}

/// Request to create a new auction.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CreateAuctionRequest {
    /// Hex-encoded artwork ID.
    pub artwork_id: String,
    /// Hex-encoded artist cell ID (must be current owner).
    pub artist_cell: String,
    /// Number of blocks the bidding phase lasts.
    pub bidding_duration: u64,
    /// Number of blocks the reveal phase lasts.
    pub reveal_duration: u64,
}

/// Request to submit a bid commitment.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubmitBidRequest {
    /// Hex-encoded commitment: BLAKE3(bidder_cell || amount || nonce).
    pub commitment: String,
    /// Hex-encoded bidder cell ID.
    pub bidder_cell: String,
    /// Amount to escrow (must be >= commitment amount for valid reveal).
    pub escrow_amount: u64,
}

/// Request to reveal a bid.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevealBidRequest {
    /// Hex-encoded commitment (must match a submitted commitment).
    pub commitment: String,
    /// Hex-encoded bidder cell ID.
    pub bidder_cell: String,
    /// The actual bid amount.
    pub amount: u64,
    /// Hex-encoded nonce used in the commitment.
    pub nonce: String,
}

/// Summary of an artwork for list responses.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArtworkSummary {
    pub id: String,
    pub title: String,
    pub image_hash: String,
    pub artist: String,
    pub current_owner: String,
    pub reserve_price: u64,
    pub tags: Vec<String>,
}

/// Detailed auction response.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuctionResponse {
    pub id: String,
    pub artwork_id: String,
    pub artist: String,
    pub phase: String,
    pub bidding_end_height: u64,
    pub reveal_end_height: u64,
    pub reserve_price: u64,
    pub commitment_count: usize,
    pub revealed_count: usize,
    pub highest_revealed_bid: Option<u64>,
    pub winner: Option<String>,
    pub winning_bid: Option<u64>,
}

/// WebSocket event sent to connected clients.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WsEvent {
    /// A new bid commitment was submitted.
    NewBid {
        auction_id: String,
        bidder: String,
        commitment: String,
    },
    /// A bid was revealed.
    BidRevealed {
        auction_id: String,
        bidder: String,
        amount: u64,
    },
    /// Auction phase changed.
    PhaseChange {
        auction_id: String,
        new_phase: String,
    },
    /// Auction settled.
    AuctionSettled {
        auction_id: String,
        winner: String,
        winning_bid: u64,
    },
    /// New artwork registered.
    NewArtwork {
        artwork_id: String,
        title: String,
        artist: String,
    },
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute an artwork ID from its creation parameters.
pub fn compute_artwork_id(artist: &CellId, title: &str, image_hash: &[u8; 32]) -> ArtworkId {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-gallery-artwork-id-v1");
    hasher.update(artist.as_bytes());
    hasher.update(title.as_bytes());
    hasher.update(image_hash);
    *hasher.finalize().as_bytes()
}

/// Compute an auction ID from its creation parameters.
pub fn compute_auction_id(artwork_id: &ArtworkId, created_at: u64) -> AuctionId {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-gallery-auction-id-v1");
    hasher.update(artwork_id);
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute a bid commitment: BLAKE3(bidder_cell || amount || nonce).
pub fn compute_bid_commitment(bidder: &CellId, amount: u64, nonce: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-gallery-bid-commitment-v1");
    hasher.update(bidder.as_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(nonce);
    *hasher.finalize().as_bytes()
}

/// Verify a bid reveal against its commitment.
pub fn verify_bid_reveal(
    commitment: &[u8; 32],
    bidder: &CellId,
    amount: u64,
    nonce: &[u8; 32],
) -> bool {
    let expected = compute_bid_commitment(bidder, amount, nonce);
    expected == *commitment
}

/// Encode a 32-byte ID as hex string.
pub fn id_to_hex(id: &[u8; 32]) -> String {
    bytes32_to_hex(id)
}

/// Decode a hex string to a 32-byte ID.
pub fn id_from_hex(hex: &str) -> Option<[u8; 32]> {
    hex_to_bytes32(hex).ok()
}

/// Format an AuctionPhase as a simple string label.
pub fn phase_label(phase: &AuctionPhase) -> &'static str {
    match phase {
        AuctionPhase::Bidding => "bidding",
        AuctionPhase::Reveal => "reveal",
        AuctionPhase::Settling => "settling",
        AuctionPhase::Settled { .. } => "settled",
        AuctionPhase::NoBids => "no_bids",
        AuctionPhase::Cancelled => "cancelled",
    }
}
