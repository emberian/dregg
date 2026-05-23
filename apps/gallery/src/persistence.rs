//! File-based state persistence for the gallery.
//!
//! Serializes all artworks, auctions, and provenance chains to a JSON file.
//! On startup, the server can restore from this file to survive restarts.

use std::io;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::Artwork;
use crate::Auction;
use crate::artwork::ArtworkRegistry;
use crate::auction::AuctionEngine;
use crate::provenance::{ProvenanceChainData, ProvenanceRegistry};

/// A complete snapshot of gallery state, serializable to JSON.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateSnapshot {
    /// All registered artworks.
    pub artworks: Vec<Artwork>,
    /// All auctions (active and completed).
    pub auctions: Vec<Auction>,
    /// Provenance chains keyed by artwork ID (hex).
    pub provenance: Vec<ProvenanceEntry>,
    /// Current block height.
    pub block_height: u64,
}

/// A provenance chain entry for serialization (includes the artwork ID key).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProvenanceEntry {
    /// Hex-encoded artwork ID.
    pub artwork_id: [u8; 32],
    /// The chain data.
    pub chain: ProvenanceChainData,
}

impl StateSnapshot {
    /// Capture the current state from all registries.
    pub async fn capture(
        artwork_registry: &ArtworkRegistry,
        auction_engine: &AuctionEngine,
        provenance_registry: &ProvenanceRegistry,
    ) -> Self {
        // Collect artworks.
        let artwork_entries = artwork_registry.list_raw().await;
        let artworks: Vec<Artwork> = artwork_entries.into_iter().map(|(_, a)| a).collect();

        // Collect auctions.
        let auction_entries = auction_engine.list_raw().await;
        let auctions: Vec<Auction> = auction_entries.into_iter().map(|(_, a)| a).collect();

        // Collect provenance chains.
        let provenance_entries = provenance_registry.list_raw().await;
        let provenance: Vec<ProvenanceEntry> = provenance_entries
            .into_iter()
            .map(|(id, chain)| ProvenanceEntry {
                artwork_id: id,
                chain,
            })
            .collect();

        let block_height = auction_engine.current_height().await;

        Self {
            artworks,
            auctions,
            provenance,
            block_height,
        }
    }

    /// Restore state into the registries.
    pub async fn restore(
        &self,
        artwork_registry: &ArtworkRegistry,
        auction_engine: &AuctionEngine,
        provenance_registry: &ProvenanceRegistry,
    ) {
        // Restore artworks.
        for artwork in &self.artworks {
            artwork_registry
                .insert_raw(artwork.id, artwork.clone())
                .await;
        }

        // Restore auctions.
        for auction in &self.auctions {
            auction_engine.insert_raw(auction.clone()).await;
        }

        // Restore provenance.
        for entry in &self.provenance {
            provenance_registry
                .insert_raw(entry.artwork_id, entry.chain.clone())
                .await;
        }

        // Restore block height.
        auction_engine.set_height(self.block_height).await;
    }

    /// Save the snapshot to a JSON file.
    pub fn save(&self, path: &str) -> io::Result<()> {
        // Write to a temp file first, then rename for atomicity.
        let tmp_path = format!("{path}.tmp");
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

        // Ensure parent directory exists.
        if let Some(parent) = Path::new(path).parent() {
            std::fs::create_dir_all(parent)?;
        }

        std::fs::write(&tmp_path, json)?;
        std::fs::rename(&tmp_path, path)?;
        Ok(())
    }

    /// Load a snapshot from a JSON file.
    pub fn load(path: &str) -> io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        let snapshot: Self = serde_json::from_str(&json)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        Ok(snapshot)
    }
}
