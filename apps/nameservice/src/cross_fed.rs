//! Cross-federation resolution via CapTP.
//!
//! When a name cannot be resolved locally, check if it refers to another federation.
//! The meta-directory maps federation names to sturdy refs pointing to their name
//! services. Resolution proceeds by establishing a CapTP session to the remote
//! federation and querying their /names/resolve endpoint.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::registry::PyanaUri;
use crate::resolution::{ResolutionError, ResolutionProvenance, ResolvedName};

// =============================================================================
// Types
// =============================================================================

/// An entry in the cross-federation meta-directory.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FederationEntry {
    /// Human-readable federation name.
    pub name: String,
    /// Sturdy ref to that federation's name directory service.
    pub nameservice_ref: PyanaUri,
    /// Optional description.
    pub description: Option<String>,
    /// When this entry was last verified.
    pub last_verified: u64,
}

/// The meta-directory: maps federation names to their nameservice endpoints.
#[derive(Clone)]
pub struct MetaDirectory {
    /// Federation name → entry.
    entries: Arc<RwLock<HashMap<String, FederationEntry>>>,
}

impl MetaDirectory {
    /// Create a new empty meta-directory.
    pub fn new() -> Self {
        Self {
            entries: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Register a federation in the meta-directory.
    pub async fn register_federation(&self, entry: FederationEntry) {
        self.entries.write().await.insert(entry.name.clone(), entry);
    }

    /// Look up a federation by name.
    pub async fn lookup(&self, federation_name: &str) -> Option<FederationEntry> {
        self.entries.read().await.get(federation_name).cloned()
    }

    /// List all known federations.
    pub async fn list_federations(&self) -> Vec<FederationEntry> {
        self.entries.read().await.values().cloned().collect()
    }

    /// Remove a federation from the directory.
    pub async fn remove_federation(&self, name: &str) -> Option<FederationEntry> {
        self.entries.write().await.remove(name)
    }
}

// =============================================================================
// Cross-Federation Resolver
// =============================================================================

/// Cross-federation resolution result.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrossFedResolution {
    /// The resolved name.
    pub resolved: ResolvedName,
    /// Which federation the name was resolved from.
    pub federation: String,
    /// The nameservice URI that was queried.
    pub via_nameservice: PyanaUri,
}

/// Attempt cross-federation resolution for a hierarchical name.
///
/// Algorithm:
/// 1. Split the name on dots from RIGHT
/// 2. Check if the rightmost segment matches a known federation
/// 3. If so, the remaining segments are the name to resolve in that federation
///
/// For example: "alice.other-fed" → look up "other-fed" in meta-directory,
/// then resolve "alice" via that federation's nameservice.
///
/// Note: In a real implementation, step 3 would establish a CapTP session to the
/// remote federation and query their nameservice. Here we return the resolution
/// metadata; actual CapTP transport is handled by the wire layer.
pub async fn resolve_cross_federation(
    meta_directory: &MetaDirectory,
    name: &str,
) -> Result<CrossFedResolution, ResolutionError> {
    // Split on dots, rightmost segment is the potential federation name.
    let segments: Vec<&str> = name.rsplitn(2, '.').collect();

    if segments.len() < 2 {
        return Err(ResolutionError::NotFound(name.to_string()));
    }

    let federation_name = segments[0];
    let _leaf_name = segments[1];

    // Look up the federation in the meta-directory.
    let federation = meta_directory
        .lookup(federation_name)
        .await
        .ok_or_else(|| {
            ResolutionError::NotFound(format!("federation not found: {federation_name}"))
        })?;

    // In a real system, we would:
    // 1. Establish/reuse a CapTP session to federation.nameservice_ref
    // 2. Send a resolve request for leaf_name
    // 3. Return the result
    //
    // For now, we return a resolution stub that includes the federation metadata.
    // The actual CapTP session establishment is handled by the wire layer.
    Ok(CrossFedResolution {
        resolved: ResolvedName {
            target: federation.nameservice_ref.clone(),
            name: name.to_string(),
            provenance: ResolutionProvenance::CrossFederation {
                federation: federation_name.to_string(),
            },
        },
        federation: federation_name.to_string(),
        via_nameservice: federation.nameservice_ref,
    })
}

/// Check if a name might be a cross-federation reference.
///
/// A name is potentially cross-federation if its rightmost segment
/// matches a known federation name in the meta-directory.
pub async fn is_cross_federation(meta_directory: &MetaDirectory, name: &str) -> bool {
    if !name.contains('.') {
        return false;
    }

    let segments: Vec<&str> = name.rsplitn(2, '.').collect();
    if segments.len() < 2 {
        return false;
    }

    meta_directory.lookup(segments[0]).await.is_some()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn register_and_lookup_federation() {
        let meta = MetaDirectory::new();

        meta.register_federation(FederationEntry {
            name: "other-fed".into(),
            nameservice_ref: "pyana://other-fed/nameservice/swiss123".into(),
            description: Some("Another federation".into()),
            last_verified: 100,
        })
        .await;

        let entry = meta.lookup("other-fed").await.unwrap();
        assert_eq!(
            entry.nameservice_ref,
            "pyana://other-fed/nameservice/swiss123"
        );
    }

    #[tokio::test]
    async fn cross_federation_resolution() {
        let meta = MetaDirectory::new();

        meta.register_federation(FederationEntry {
            name: "remote".into(),
            nameservice_ref: "pyana://remote/ns/abc".into(),
            description: None,
            last_verified: 100,
        })
        .await;

        let result = resolve_cross_federation(&meta, "alice.remote")
            .await
            .unwrap();
        assert_eq!(result.federation, "remote");
        assert_eq!(result.resolved.name, "alice.remote");
        assert!(matches!(
            result.resolved.provenance,
            ResolutionProvenance::CrossFederation { .. }
        ));
    }

    #[tokio::test]
    async fn unknown_federation_fails() {
        let meta = MetaDirectory::new();

        let err = resolve_cross_federation(&meta, "alice.unknown")
            .await
            .unwrap_err();
        assert!(matches!(err, ResolutionError::NotFound(_)));
    }

    #[tokio::test]
    async fn is_cross_federation_check() {
        let meta = MetaDirectory::new();

        meta.register_federation(FederationEntry {
            name: "known".into(),
            nameservice_ref: "pyana://known/ns/x".into(),
            description: None,
            last_verified: 100,
        })
        .await;

        assert!(is_cross_federation(&meta, "alice.known").await);
        assert!(!is_cross_federation(&meta, "alice.unknown").await);
        assert!(!is_cross_federation(&meta, "alice").await);
    }
}
