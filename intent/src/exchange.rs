//! Exchange-specific types for multi-asset ring trade solving.
//!
//! These types extend the intent engine's capability-shaped matching with
//! asset exchange semantics needed for the CoW (Coincidence of Wants) solver.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Asset identifier (content-addressed from token metadata).
pub type AssetId = [u8; 32];

/// A well-known asset registry (for computing compatibility).
pub struct AssetRegistry {
    /// Known assets with metadata.
    assets: HashMap<AssetId, AssetInfo>,
}

/// Metadata for a registered asset.
#[derive(Clone, Debug)]
pub struct AssetInfo {
    pub name: String,
    pub decimals: u8,
    pub asset_type: AssetType,
}

/// Classification of asset types for compatibility checking.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AssetType {
    /// Standard fungible token (divisible, interchangeable units).
    Fungible,
    /// Non-fungible token from a specific collection.
    NonFungible { collection: [u8; 32] },
    /// A capability token bound to a specific cell.
    Capability { cell_id: [u8; 32] },
}

impl AssetRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        Self {
            assets: HashMap::new(),
        }
    }

    /// Register an asset.
    pub fn register(&mut self, id: AssetId, info: AssetInfo) {
        self.assets.insert(id, info);
    }

    /// Look up an asset by ID.
    pub fn get(&self, id: &AssetId) -> Option<&AssetInfo> {
        self.assets.get(id)
    }

    /// Check if two assets are of the same type (both fungible, both from same NFT collection, etc.).
    pub fn same_type(&self, a: &AssetId, b: &AssetId) -> bool {
        match (self.assets.get(a), self.assets.get(b)) {
            (Some(info_a), Some(info_b)) => info_a.asset_type == info_b.asset_type,
            _ => false,
        }
    }
}

impl Default for AssetRegistry {
    fn default() -> Self {
        Self::new()
    }
}
