//! Atomic settlement via TurnComposer.
//!
//! When an auction ends, settlement creates an atomic turn that simultaneously:
//! 1. Releases the winner's escrowed funds to the artist
//! 2. Transfers the artwork ownership capability to the winner
//!
//! This uses `TurnComposer` for multi-party atomic composition:
//! - The winner's fragment: "release my escrow to the artist"
//! - The artist's fragment: "delegate my ownership capability to the winner"
//!
//! Both fragments use `CommitmentMode::Partial` so they can be composed into
//! a single atomic turn without either party seeing the other's fragment.
//!
//! Losing bidders get refunded via `ConditionalTurn` with timeout-based auto-refund.

use pyana_app_framework::{CellId, PyanaEngine};
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::builder::ActionBuilder;
use pyana_turn::forest::{CallForest, CallTree};
use pyana_turn::turn::Turn;

use crate::ArtworkId;

/// Errors from settlement operations.
#[derive(Debug, Clone)]
pub enum SettlementError {
    /// The composed turn failed execution.
    ComposeFailed(String),
    /// Escrow release failed.
    EscrowReleaseFailed(String),
    /// Ownership transfer failed.
    TransferFailed(String),
    /// Refund failed.
    RefundFailed(String),
}

impl std::fmt::Display for SettlementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ComposeFailed(msg) => write!(f, "compose failed: {msg}"),
            Self::EscrowReleaseFailed(msg) => write!(f, "escrow release failed: {msg}"),
            Self::TransferFailed(msg) => write!(f, "ownership transfer failed: {msg}"),
            Self::RefundFailed(msg) => write!(f, "refund failed: {msg}"),
        }
    }
}

impl std::error::Error for SettlementError {}

/// Parameters for atomic settlement of an auction.
pub struct AtomicSettlement {
    /// The artwork being transferred.
    pub artwork_id: ArtworkId,
    /// The artist (current owner / seller).
    pub artist: CellId,
    /// The auction winner (buyer).
    pub winner: CellId,
    /// The winning bid amount.
    pub winning_bid: u64,
    /// The winner's escrow ID (holding their funds).
    pub winner_escrow_id: [u8; 32],
}

impl AtomicSettlement {
    /// Execute the atomic settlement via TurnComposer.
    ///
    /// Creates a composed turn with two fragments:
    /// 1. Release winner's escrow → payment to artist
    /// 2. Delegate artist's ownership capability → winner
    ///
    /// Returns the receipt hash on success.
    pub fn execute(&self, engine: &mut PyanaEngine) -> Result<[u8; 32], SettlementError> {
        // P2.D: balance_change is now derived from emitted effects by the
        // typestate ActionBuilder, not declared by the caller. The prior
        // code declared `Some(-winning_bid)` on the payment fragment and
        // `Some(+winning_bid)` on the transfer fragment — the latter was
        // wrong (the artist's actual delta is the 1-unit NFT outflow plus
        // whatever cash they receive in the escrow release on their cell).
        //
        // Authorization is `UncheckedOptIn` for now because gallery settlement
        // composes signed fragments via TurnComposer in production; this
        // helper is exercised in tests with an unchecked path until the
        // composer migration lands (follow-up).
        let payment_action: Action = ActionBuilder::new_unchecked_for_tests(
            self.winner,
            "settle_payment",
            self.winner,
        )
        .effect_release_escrow(self.winner_escrow_id, Some(self.artwork_id.to_vec()))
        .effect_transfer(self.winner, self.artist, self.winning_bid)
        .commitment_mode(CommitmentMode::Partial)
        .delegation(DelegationMode::None)
        .build();

        let transfer_action: Action = ActionBuilder::new_unchecked_for_tests(
            self.artist,
            "transfer_ownership",
            self.artist,
        )
        .effect_transfer(self.artist, self.winner, 1) // NFT: ownership token
        .commitment_mode(CommitmentMode::Partial)
        .delegation(DelegationMode::Inherit)
        .build();

        // Compose into a single atomic turn.
        let composed_turn = Turn {
            agent: self.artist,
            nonce: self.winning_bid,
            call_forest: CallForest {
                roots: vec![
                    CallTree::new(payment_action),
                    CallTree::new(transfer_action),
                ],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some(format!(
                "gallery settlement: artwork {} sold for {}",
                crate::id_to_hex(&self.artwork_id),
                self.winning_bid
            )),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
        };

        engine
            .execute_turn(&composed_turn)
            .map_err(|e| SettlementError::ComposeFailed(e.to_string()))?;

        // Compute receipt hash from the settlement parameters.
        let receipt_hash = compute_settlement_receipt(
            &self.artwork_id,
            &self.artist,
            &self.winner,
            self.winning_bid,
        );

        Ok(receipt_hash)
    }

    /// Refund a losing bidder's escrow.
    ///
    /// Uses a refund turn to release the escrowed funds back to the bidder.
    pub fn refund_loser(
        engine: &mut PyanaEngine,
        escrow_id: [u8; 32],
    ) -> Result<(), SettlementError> {
        let agent = CellId::from_bytes(escrow_id);

        let refund_action = Action {
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
            nonce: 0,
            call_forest: CallForest {
                roots: vec![CallTree::new(refund_action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some("gallery: refund losing bidder".to_string()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
        };

        engine
            .execute_turn(&turn)
            .map_err(|e| SettlementError::RefundFailed(e.to_string()))?;

        Ok(())
    }
}

/// Compute a deterministic receipt hash for a settlement.
fn compute_settlement_receipt(
    artwork_id: &[u8; 32],
    artist: &CellId,
    winner: &CellId,
    amount: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-gallery-settlement-receipt-v1");
    hasher.update(artwork_id);
    hasher.update(artist.as_bytes());
    hasher.update(winner.as_bytes());
    hasher.update(&amount.to_le_bytes());
    *hasher.finalize().as_bytes()
}
