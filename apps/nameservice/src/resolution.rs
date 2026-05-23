//! Hierarchical name resolution protocol.
//!
//! Resolves names through the local registry and hierarchical dotted-name paths.
//! Names with dots are split into segments and resolved right-to-left:
//!   "oracle.alice" → look up "alice", then resolve "oracle" under alice's sub-namespace.

use serde::{Deserialize, Serialize};

use crate::registry::{NameRegistry, PyanaUri, RegistryError};

// =============================================================================
// Types
// =============================================================================

/// How a name was resolved (provenance tracking).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "source")]
pub enum ResolutionProvenance {
    /// Resolved from the local federation registry.
    Local,
    /// Resolved via hierarchical sub-name traversal.
    Hierarchical { parent: String },
    /// Resolved via cross-federation lookup.
    CrossFederation { federation: String },
}

/// The result of a name resolution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ResolvedName {
    /// The target URI this name resolved to.
    pub target: PyanaUri,
    /// The full name that was resolved.
    pub name: String,
    /// How the resolution was achieved.
    pub provenance: ResolutionProvenance,
}

/// Errors during resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolutionError {
    /// Name not found in any source.
    NotFound(String),
    /// Intermediate segment in a hierarchical name is not a delegated namespace.
    NotANamespace { segment: String },
    /// Registry error during lookup.
    Registry(RegistryError),
}

impl std::fmt::Display for ResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(name) => write!(f, "name not found: {name}"),
            Self::NotANamespace { segment } => {
                write!(f, "segment is not a delegated namespace: {segment}")
            }
            Self::Registry(e) => write!(f, "registry error: {e}"),
        }
    }
}

// =============================================================================
// Resolver
// =============================================================================

/// The name resolver: handles both flat and hierarchical resolution.
#[derive(Clone)]
pub struct NameResolver {
    registry: NameRegistry,
}

impl NameResolver {
    /// Create a new resolver backed by the given registry.
    pub fn new(registry: NameRegistry) -> Self {
        Self { registry }
    }

    /// Resolve a name (flat or hierarchical).
    ///
    /// If the name contains dots, it is treated as hierarchical:
    /// "oracle.alice" means "resolve alice first, then oracle under alice".
    ///
    /// Hierarchical names are resolved RIGHT-to-LEFT (rightmost segment is the
    /// parent/root, leftmost is the leaf).
    pub async fn resolve(
        &self,
        name: &str,
        current_epoch: u64,
    ) -> Result<ResolvedName, ResolutionError> {
        if name.contains('.') {
            self.resolve_hierarchical(name, current_epoch).await
        } else {
            self.resolve_flat(name, current_epoch).await
        }
    }

    /// Flat resolution: direct lookup in the local registry.
    async fn resolve_flat(
        &self,
        name: &str,
        current_epoch: u64,
    ) -> Result<ResolvedName, ResolutionError> {
        let target = self
            .registry
            .resolve(name, current_epoch)
            .await
            .ok_or_else(|| ResolutionError::NotFound(name.to_string()))?;

        Ok(ResolvedName {
            target,
            name: name.to_string(),
            provenance: ResolutionProvenance::Local,
        })
    }

    /// Hierarchical resolution: split on dots, resolve right-to-left.
    ///
    /// For "oracle.alice":
    ///   1. Resolve "alice" in the registry → get alice's entry
    ///   2. Verify alice has delegation authority
    ///   3. Look up "oracle.alice" as a sub-name in the registry
    async fn resolve_hierarchical(
        &self,
        name: &str,
        current_epoch: u64,
    ) -> Result<ResolvedName, ResolutionError> {
        let segments: Vec<&str> = name.split('.').collect();

        // The rightmost segment is the parent (root of the hierarchy).
        // e.g., for "oracle.alice" → parent = "alice", child = "oracle"
        let parent_name = segments.last().unwrap();

        // Verify the parent exists and has delegation authority.
        let parent = self
            .registry
            .lookup(parent_name, current_epoch)
            .await
            .ok_or_else(|| ResolutionError::NotFound(parent_name.to_string()))?;

        // Check that parent has delegation authority.
        match &parent.delegation {
            crate::registry::DelegationAuthority::None => {
                return Err(ResolutionError::NotANamespace {
                    segment: parent_name.to_string(),
                });
            }
            _ => {}
        }

        // Try to resolve the full dotted name as a single entry.
        // Sub-names are stored as "child.parent" in the registry.
        if let Some(target) = self.registry.resolve(name, current_epoch).await {
            return Ok(ResolvedName {
                target,
                name: name.to_string(),
                provenance: ResolutionProvenance::Hierarchical {
                    parent: parent_name.to_string(),
                },
            });
        }

        Err(ResolutionError::NotFound(name.to_string()))
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::DelegationAuthority;

    #[tokio::test]
    async fn flat_resolution() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        registry
            .register(
                "bob",
                "pyana://fed/bob/swiss".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let resolver = NameResolver::new(registry);
        let result = resolver.resolve("bob", 100).await.unwrap();
        assert_eq!(result.target, "pyana://fed/bob/swiss");
        assert_eq!(result.provenance, ResolutionProvenance::Local);
    }

    #[tokio::test]
    async fn hierarchical_resolution() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        // Register "alice" with sub-prefix delegation.
        registry
            .register(
                "alice",
                "pyana://fed/alice/swiss".into(),
                owner,
                DelegationAuthority::SubPrefix {
                    prefix: "alice".into(),
                },
                100,
                50,
                10,
            )
            .await
            .unwrap();

        // Register "oracle.alice" as a sub-name.
        registry
            .register(
                "oracle.alice",
                "pyana://fed/oracle-alice/swiss".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let resolver = NameResolver::new(registry);
        let result = resolver.resolve("oracle.alice", 100).await.unwrap();
        assert_eq!(result.target, "pyana://fed/oracle-alice/swiss");
        assert!(matches!(
            result.provenance,
            ResolutionProvenance::Hierarchical { .. }
        ));
    }

    #[tokio::test]
    async fn hierarchical_fails_without_delegation() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        // Register "bob" WITHOUT delegation.
        registry
            .register(
                "bob",
                "pyana://fed/bob/swiss".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let resolver = NameResolver::new(registry);
        let err = resolver.resolve("service.bob", 100).await.unwrap_err();
        assert!(matches!(err, ResolutionError::NotANamespace { .. }));
    }

    #[tokio::test]
    async fn not_found() {
        let registry = NameRegistry::new();
        let resolver = NameResolver::new(registry);
        let err = resolver.resolve("nonexistent", 100).await.unwrap_err();
        assert!(matches!(err, ResolutionError::NotFound(_)));
    }
}
