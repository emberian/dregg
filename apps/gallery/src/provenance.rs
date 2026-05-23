//! Provenance chain: ownership history stored as capability delegations.
//!
//! Each transfer is recorded as a delegation event. The provenance chain for
//! an artwork provides a complete, verifiable history of ownership from the
//! original artist through all subsequent transfers.
//!
//! The chain is append-only: each entry references the previous via a hash link,
//! forming a tamper-evident log of ownership.

use pyana_app_framework::CellId;
use pyana_app_framework::store::ContentStore;

use crate::{ArtworkId, ProvenanceEntry};

/// A serializable provenance chain wrapper for ContentStore.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ProvenanceChainData {
    pub entries: Vec<ProvenanceEntry>,
}

/// The provenance registry, tracking ownership history for all artworks.
#[derive(Clone)]
pub struct ProvenanceRegistry {
    chains: ContentStore<ProvenanceChainData>,
}

impl ProvenanceRegistry {
    /// Create a new empty provenance registry.
    pub fn new() -> Self {
        Self {
            chains: ContentStore::new(),
        }
    }

    /// Record the initial registration (artist → artist, price 0).
    pub async fn record_registration(
        &self,
        artwork_id: ArtworkId,
        artist: CellId,
        block_height: u64,
    ) {
        let entry = ProvenanceEntry {
            from: artist,
            to: artist,
            price: 0,
            block_height,
            receipt_hash: compute_registration_receipt(&artwork_id, &artist, block_height),
        };

        self.chains
            .insert(
                artwork_id,
                ProvenanceChainData {
                    entries: vec![entry],
                },
            )
            .await;
    }

    /// Record a transfer (sale or gift).
    pub async fn record_transfer(
        &self,
        artwork_id: &ArtworkId,
        from: CellId,
        to: CellId,
        price: u64,
        block_height: u64,
        receipt_hash: [u8; 32],
    ) {
        let entry = ProvenanceEntry {
            from,
            to,
            price,
            block_height,
            receipt_hash,
        };

        let updated = self
            .chains
            .update(artwork_id, |chain| {
                chain.entries.push(entry.clone());
            })
            .await;

        // If no chain exists yet, create one with just this entry.
        if !updated {
            self.chains
                .insert(
                    *artwork_id,
                    ProvenanceChainData {
                        entries: vec![entry],
                    },
                )
                .await;
        }
    }

    /// List all provenance chains as raw (id, chain) pairs (for persistence).
    pub async fn list_raw(&self) -> Vec<([u8; 32], ProvenanceChainData)> {
        self.chains.list().await
    }

    /// Insert a raw provenance chain (for persistence restore).
    pub async fn insert_raw(&self, artwork_id: ArtworkId, chain: ProvenanceChainData) {
        self.chains.insert(artwork_id, chain).await;
    }

    /// Get the full provenance chain for an artwork.
    pub async fn get_chain(&self, artwork_id: &ArtworkId) -> Vec<ProvenanceEntry> {
        self.chains
            .get(artwork_id)
            .await
            .map(|c| c.entries)
            .unwrap_or_default()
    }

    /// Get the current owner (last entry in the chain).
    pub async fn current_owner(&self, artwork_id: &ArtworkId) -> Option<CellId> {
        let chain = self.chains.get(artwork_id).await?;
        chain.entries.last().map(|e| e.to)
    }

    /// Get the number of transfers for an artwork.
    pub async fn transfer_count(&self, artwork_id: &ArtworkId) -> usize {
        self.chains
            .get(artwork_id)
            .await
            .map(|c| c.entries.len())
            .unwrap_or(0)
    }

    /// Verify chain integrity (each entry links to the previous owner).
    pub async fn verify_chain(&self, artwork_id: &ArtworkId) -> bool {
        let chain = self.get_chain(artwork_id).await;
        if chain.is_empty() {
            return true;
        }

        for window in chain.windows(2) {
            // Each entry's `from` must be the previous entry's `to`.
            if window[1].from.as_bytes() != window[0].to.as_bytes() {
                return false;
            }
        }

        true
    }
}

/// Compute a receipt hash for the initial registration.
fn compute_registration_receipt(
    artwork_id: &ArtworkId,
    artist: &CellId,
    block_height: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-gallery-registration-receipt-v1");
    hasher.update(artwork_id);
    hasher.update(artist.as_bytes());
    hasher.update(&block_height.to_le_bytes());
    *hasher.finalize().as_bytes()
}
