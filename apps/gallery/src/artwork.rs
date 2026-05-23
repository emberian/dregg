//! Artwork registration, metadata management, and cell representation.
//!
//! Each artwork is represented as a pyana cell with fields:
//! - title, artist, current_owner, image_hash
//!
//! Registration creates the cell and mints an ownership capability.

use pyana_app_framework::store::ContentStore;
use pyana_app_framework::{CellId, PyanaEngine};
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::forest::{CallForest, CallTree};
use pyana_turn::turn::Turn;

use crate::{Artwork, ArtworkId, ArtworkSummary, compute_artwork_id, id_to_hex};

/// In-memory artwork registry backed by ContentStore.
#[derive(Clone)]
pub struct ArtworkRegistry {
    artworks: ContentStore<Artwork>,
}

impl ArtworkRegistry {
    /// Create a new empty artwork registry.
    pub fn new() -> Self {
        Self {
            artworks: ContentStore::new(),
        }
    }

    /// Register a new artwork, creating its cell via the engine.
    ///
    /// Returns the artwork ID on success.
    pub async fn register(
        &self,
        engine: &mut PyanaEngine,
        title: String,
        description: String,
        image_hash: [u8; 32],
        artist: CellId,
        reserve_price: u64,
        tags: Vec<String>,
        current_height: u64,
    ) -> Result<ArtworkId, ArtworkError> {
        let artwork_id = compute_artwork_id(&artist, &title, &image_hash);

        // Check for duplicate registration.
        if self.artworks.get(&artwork_id).await.is_some() {
            return Err(ArtworkError::AlreadyRegistered(id_to_hex(&artwork_id)));
        }

        // Create the artwork cell via the engine.
        // The cell represents the artwork's on-chain identity.
        // Transfer 1 unit to self (NFT minting: ownership token).
        let action = Action {
            target: artist,
            method: symbol("register_artwork"),
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::Transfer {
                from: artist,
                to: artist,
                amount: 1, // NFT: exactly one ownership token
            }],
            may_delegate: DelegationMode::Inherit,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = Turn {
            agent: artist,
            nonce: current_height,
            call_forest: CallForest {
                roots: vec![CallTree::new(action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some(format!("register artwork: {title}")),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        engine
            .execute_turn(&turn)
            .map_err(|e| ArtworkError::RegistrationFailed(e.to_string()))?;

        let artwork = Artwork {
            id: artwork_id,
            title,
            description,
            image_hash,
            artist,
            current_owner: artist,
            reserve_price,
            registered_at: current_height,
            tags,
        };

        self.artworks.insert(artwork_id, artwork).await;
        Ok(artwork_id)
    }

    /// Get an artwork by ID.
    pub async fn get(&self, id: &ArtworkId) -> Option<Artwork> {
        self.artworks.get(id).await
    }

    /// Update the owner of an artwork (after settlement).
    pub async fn transfer_ownership(&self, id: &ArtworkId, new_owner: CellId) -> bool {
        self.artworks
            .update(id, |artwork| {
                artwork.current_owner = new_owner;
            })
            .await
    }

    /// List all artworks as summaries.
    pub async fn list_all(&self) -> Vec<ArtworkSummary> {
        self.artworks
            .list()
            .await
            .into_iter()
            .map(|(_, a)| ArtworkSummary {
                id: id_to_hex(&a.id),
                title: a.title,
                image_hash: id_to_hex(&a.image_hash),
                artist: id_to_hex(a.artist.as_bytes()),
                current_owner: id_to_hex(a.current_owner.as_bytes()),
                reserve_price: a.reserve_price,
                tags: a.tags,
            })
            .collect()
    }

    /// List all artworks as raw (id, Artwork) pairs (for persistence).
    pub async fn list_raw(&self) -> Vec<([u8; 32], Artwork)> {
        self.artworks.list().await
    }

    /// Insert a raw artwork (for persistence restore).
    pub async fn insert_raw(&self, id: ArtworkId, artwork: Artwork) {
        self.artworks.insert(id, artwork).await;
    }

    /// List artworks filtered by tag.
    pub async fn list_by_tag(&self, tag: &str) -> Vec<ArtworkSummary> {
        let tag = tag.to_string();
        self.artworks
            .find(move |a| a.tags.iter().any(|t| t == &tag))
            .await
            .into_iter()
            .map(|(_, a)| ArtworkSummary {
                id: id_to_hex(&a.id),
                title: a.title,
                image_hash: id_to_hex(&a.image_hash),
                artist: id_to_hex(a.artist.as_bytes()),
                current_owner: id_to_hex(a.current_owner.as_bytes()),
                reserve_price: a.reserve_price,
                tags: a.tags,
            })
            .collect()
    }
}

/// Errors from artwork operations.
#[derive(Debug, Clone)]
pub enum ArtworkError {
    /// Artwork with this ID already exists.
    AlreadyRegistered(String),
    /// Turn execution failed during registration.
    RegistrationFailed(String),
    /// Artwork not found.
    NotFound(String),
}

impl std::fmt::Display for ArtworkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyRegistered(id) => write!(f, "artwork already registered: {id}"),
            Self::RegistrationFailed(msg) => write!(f, "registration failed: {msg}"),
            Self::NotFound(id) => write!(f, "artwork not found: {id}"),
        }
    }
}

impl std::error::Error for ArtworkError {}
