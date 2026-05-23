//! Reverse index: CellId/owner → names.
//!
//! Given an owner key or a target URI, find all names pointing to it.
//! Maintained as a secondary index built from the registry's entries.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::registry::{NameEntry, NameRegistry};

// =============================================================================
// Types
// =============================================================================

/// A reverse lookup result.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReverseEntry {
    /// The name that points to the target.
    pub name: String,
    /// The owner of this name.
    pub owner: [u8; 32],
    /// When the name was registered.
    pub registered_at: u64,
    /// When the name expires.
    pub expires_at: u64,
}

// =============================================================================
// Reverse Index
// =============================================================================

/// Reverse name index: maps owner keys and target URIs to names.
#[derive(Clone)]
pub struct ReverseIndex {
    /// Maps owner [u8; 32] → set of names they own.
    by_owner: Arc<RwLock<HashMap<[u8; 32], Vec<String>>>>,
    /// Maps target URI → set of names pointing to it.
    by_target: Arc<RwLock<HashMap<String, Vec<String>>>>,
}

impl ReverseIndex {
    /// Create a new empty reverse index.
    pub fn new() -> Self {
        Self {
            by_owner: Arc::new(RwLock::new(HashMap::new())),
            by_target: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Record a name registration in the reverse index.
    pub async fn on_register(&self, entry: &NameEntry) {
        self.by_owner
            .write()
            .await
            .entry(entry.owner)
            .or_default()
            .push(entry.name.clone());

        self.by_target
            .write()
            .await
            .entry(entry.target.clone())
            .or_default()
            .push(entry.name.clone());
    }

    /// Remove a name from the reverse index.
    pub async fn on_release(&self, entry: &NameEntry) {
        if let Some(names) = self.by_owner.write().await.get_mut(&entry.owner) {
            names.retain(|n| n != &entry.name);
        }

        if let Some(names) = self.by_target.write().await.get_mut(&entry.target) {
            names.retain(|n| n != &entry.name);
        }
    }

    /// Look up all names owned by a given key.
    pub async fn whois_by_owner(&self, owner: &[u8; 32]) -> Vec<String> {
        self.by_owner
            .read()
            .await
            .get(owner)
            .cloned()
            .unwrap_or_default()
    }

    /// Look up all names pointing to a given target URI.
    pub async fn whois_by_target(&self, target: &str) -> Vec<String> {
        self.by_target
            .read()
            .await
            .get(target)
            .cloned()
            .unwrap_or_default()
    }
}

/// Build the reverse index from the current registry state.
pub async fn build_reverse_index(registry: &NameRegistry) -> ReverseIndex {
    let index = ReverseIndex::new();
    for entry in registry.all_entries().await {
        index.on_register(&entry).await;
    }
    index
}

/// Perform a "whois" query: given a cell_id (as hex or raw bytes), find names.
///
/// This queries the registry directly for all entries matching the given owner
/// or target pattern.
pub async fn whois(registry: &NameRegistry, cell_id_hex: &str) -> Vec<ReverseEntry> {
    let entries = registry.all_entries().await;
    let mut results = Vec::new();

    // Try matching by owner (hex-encoded cell_id).
    let owner_bytes = hex_to_bytes(cell_id_hex);

    for entry in &entries {
        let matches = if let Some(ref owner) = owner_bytes {
            &entry.owner == owner
        } else {
            // Also try matching by target URI containing the cell_id.
            entry.target.contains(cell_id_hex)
        };

        if matches {
            results.push(ReverseEntry {
                name: entry.name.clone(),
                owner: entry.owner,
                registered_at: entry.registered_at,
                expires_at: entry.expires_at,
            });
        }
    }

    results
}

/// Try to decode a hex string into a 32-byte array.
fn hex_to_bytes(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for i in 0..32 {
        bytes[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

/// Encode bytes as hex.
pub fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::DelegationAuthority;

    #[tokio::test]
    async fn reverse_lookup_by_owner() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        registry
            .register(
                "alice",
                "pyana://a".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();
        registry
            .register(
                "alice-service",
                "pyana://b".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let owner_hex = hex_encode(&owner);
        let results = whois(&registry, &owner_hex).await;
        assert_eq!(results.len(), 2);

        let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
        assert!(names.contains(&"alice"));
        assert!(names.contains(&"alice-service"));
    }

    #[tokio::test]
    async fn reverse_index_tracks_registrations() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        let entry = registry
            .register(
                "myname",
                "pyana://target".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let index = ReverseIndex::new();
        index.on_register(&entry).await;

        let by_owner = index.whois_by_owner(&owner).await;
        assert_eq!(by_owner, vec!["myname"]);

        let by_target = index.whois_by_target("pyana://target").await;
        assert_eq!(by_target, vec!["myname"]);
    }

    #[tokio::test]
    async fn reverse_index_release() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        let entry = registry
            .register(
                "temp",
                "pyana://t".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let index = ReverseIndex::new();
        index.on_register(&entry).await;
        index.on_release(&entry).await;

        let by_owner = index.whois_by_owner(&owner).await;
        assert!(by_owner.is_empty());
    }
}
