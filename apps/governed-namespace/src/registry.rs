//! Capability registry and service mesh: mount, discover, and resolve live services.
//!
//! Directories don't just store file blobs -- they store CAPABILITIES (sturdy refs to
//! any kind of service). A directory is a programmable introduction service. Registering
//! yourself in a directory = making your services discoverable. The DFA router controls
//! WHO can register WHERE.
//!
//! ## Mount semantics (CAS = compare-and-swap)
//!
//! - `mount(path, service_entry, expected_version)` -- fails if version doesn't match
//! - A new mount has version=1; updates increment
//! - Mount path must be within a route prefix the caller has authority for
//! - DFA classification determines: can this caller mount here?
//!
//! ## Discovery
//!
//! - `discover(tags=["compute", "gpu"])` returns all entries matching ALL tags
//! - Discovery is scoped to routes the caller can see (DFA classification)
//! - This IS the "scoped intent pool" but for live services rather than one-shot intents
//!
//! ## Join and mount flow
//!
//! 1. Alice joins the federation (governance)
//! 2. Alice has an oracle service running externally
//! 3. Alice mounts it at `/services/alice/price-oracle`
//! 4. Bob discovers it via tags: `discover(tags=["oracle", "prices"])`
//! 5. Bob enlivens the sturdy ref and starts querying

use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::namespace::{AuthLevel, Namespace, NamespaceError};

// =============================================================================
// Types
// =============================================================================

/// What kind of capability a service entry represents.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ServiceKind {
    /// Can store/retrieve blobs.
    Storage,
    /// Can execute computations.
    Compute,
    /// Provides external data.
    Oracle,
    /// Creates new capabilities.
    Factory,
    /// Recursive namespace (sub-directory).
    SubDirectory,
    /// Application-defined kind.
    Custom(String),
}

/// A service entry in the registry -- richer than a file hash.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ServiceEntry {
    /// Human-readable service name.
    pub name: String,
    /// What kind of capability this provides.
    pub kind: ServiceKind,
    /// The sturdy reference URI (e.g. `pyana://federation/cell/swiss`).
    pub sturdy_ref: String,
    /// Who registered this service (32-byte public key / identity).
    pub owner: [u8; 32],
    /// CAS version -- increments on each update. Starts at 1.
    pub version: u64,
    /// Discovery tags (e.g. ["oracle", "prices", "defi"]).
    pub tags: Vec<String>,
    /// Human-readable description of what this service does.
    pub description: String,
    /// Block height (or timestamp) when registered.
    pub registered_at: u64,
    /// Optional expiry (block height or timestamp). Auto-GC after this.
    pub expires_at: Option<u64>,
    /// Optional health check endpoint path.
    pub health_endpoint: Option<String>,
}

/// Health status of a mounted service.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HealthStatus {
    /// Service is reachable and healthy.
    Healthy,
    /// Service is unreachable or returned an error.
    Unhealthy,
    /// Health has not been checked yet.
    Unknown,
    /// Service has no health endpoint declared.
    NoEndpoint,
}

/// Internal record combining the service entry with its health state.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MountedService {
    /// The mount path (e.g. "/services/alice/price-oracle").
    pub path: String,
    /// The service entry.
    pub entry: ServiceEntry,
    /// Last known health status.
    pub health: HealthStatus,
    /// Timestamp of last health check.
    pub last_health_check: Option<u64>,
}

// =============================================================================
// Registry errors
// =============================================================================

/// Errors from registry operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// The mount path already exists and the expected version didn't match (CAS failure).
    VersionMismatch {
        path: String,
        current: u64,
        expected: u64,
    },
    /// The mount path does not exist (for update/unmount/resolve).
    NotFound(String),
    /// The caller is not authorized for this path (DFA classification denied).
    Unauthorized(NamespaceError),
    /// The path is invalid (empty, doesn't start with /, etc.).
    InvalidPath(String),
    /// The service entry is invalid.
    InvalidEntry(String),
}

impl std::fmt::Display for RegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegistryError::VersionMismatch {
                path,
                current,
                expected,
            } => {
                write!(
                    f,
                    "CAS conflict at {path}: current version {current}, expected {expected}"
                )
            }
            RegistryError::NotFound(path) => write!(f, "no service mounted at: {path}"),
            RegistryError::Unauthorized(e) => write!(f, "unauthorized: {e}"),
            RegistryError::InvalidPath(msg) => write!(f, "invalid path: {msg}"),
            RegistryError::InvalidEntry(msg) => write!(f, "invalid entry: {msg}"),
        }
    }
}

// =============================================================================
// Registry
// =============================================================================

/// The capability registry: a governed service mesh overlay on the namespace.
///
/// Services are mounted at paths governed by the DFA routing table. The routing
/// table determines which prefixes exist and who can use them. The DFA router
/// is the ACL for the registry, not just for file access.
#[derive(Clone)]
pub struct Registry {
    /// Mounted services keyed by their path.
    services: Arc<RwLock<BTreeMap<String, MountedService>>>,
}

impl Registry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }

    /// Mount a service at a named path (CAS semantics).
    ///
    /// - If no service exists at `path`, mounts with version=1. `expected_version` must be 0.
    /// - If a service already exists, `expected_version` must match its current version.
    ///   On success, the version increments.
    ///
    /// The namespace is consulted to verify the caller has authority to mount at this path.
    pub async fn mount(
        &self,
        namespace: &Namespace,
        path: &str,
        mut entry: ServiceEntry,
        expected_version: u64,
        auth: &AuthLevel,
    ) -> Result<MountedService, RegistryError> {
        // Validate path.
        if path.is_empty() || !path.starts_with('/') {
            return Err(RegistryError::InvalidPath(
                "path must start with '/'".to_string(),
            ));
        }

        // Validate entry.
        if entry.name.is_empty() {
            return Err(RegistryError::InvalidEntry(
                "name must not be empty".to_string(),
            ));
        }
        if entry.sturdy_ref.is_empty() {
            return Err(RegistryError::InvalidEntry(
                "sturdy_ref must not be empty".to_string(),
            ));
        }

        // Authorize via DFA classification.
        namespace
            .authorize(path, auth)
            .await
            .map_err(RegistryError::Unauthorized)?;

        let mut services = self.services.write().await;

        if let Some(existing) = services.get(path) {
            // CAS check: expected version must match current.
            if existing.entry.version != expected_version {
                return Err(RegistryError::VersionMismatch {
                    path: path.to_string(),
                    current: existing.entry.version,
                    expected: expected_version,
                });
            }
            // Update: increment version.
            entry.version = existing.entry.version + 1;
        } else {
            // New mount: expected_version must be 0.
            if expected_version != 0 {
                return Err(RegistryError::VersionMismatch {
                    path: path.to_string(),
                    current: 0,
                    expected: expected_version,
                });
            }
            entry.version = 1;
        }

        // Set registration timestamp if not already set.
        if entry.registered_at == 0 {
            entry.registered_at = now_timestamp();
        }

        let mounted = MountedService {
            path: path.to_string(),
            entry,
            health: HealthStatus::Unknown,
            last_health_check: None,
        };

        services.insert(path.to_string(), mounted.clone());
        Ok(mounted)
    }

    /// Unmount a service at the given path.
    ///
    /// Authorization is checked via the namespace DFA.
    pub async fn unmount(
        &self,
        namespace: &Namespace,
        path: &str,
        auth: &AuthLevel,
    ) -> Result<MountedService, RegistryError> {
        // Authorize.
        namespace
            .authorize(path, auth)
            .await
            .map_err(RegistryError::Unauthorized)?;

        let mut services = self.services.write().await;
        services
            .remove(path)
            .ok_or_else(|| RegistryError::NotFound(path.to_string()))
    }

    /// Resolve a path to the mounted service's sturdy ref (the "introduction").
    ///
    /// Authorization is checked -- the caller must be able to see this path.
    pub async fn resolve(
        &self,
        namespace: &Namespace,
        path: &str,
        auth: &AuthLevel,
    ) -> Result<MountedService, RegistryError> {
        // Authorize.
        namespace
            .authorize(path, auth)
            .await
            .map_err(RegistryError::Unauthorized)?;

        let services = self.services.read().await;
        services
            .get(path)
            .cloned()
            .ok_or_else(|| RegistryError::NotFound(path.to_string()))
    }

    /// Update a mounted service (CAS semantics with version check).
    ///
    /// This is equivalent to mount with the correct expected_version, but
    /// requires the service to already exist.
    pub async fn update(
        &self,
        namespace: &Namespace,
        path: &str,
        entry: ServiceEntry,
        expected_version: u64,
        auth: &AuthLevel,
    ) -> Result<MountedService, RegistryError> {
        // Verify the service exists first.
        {
            let services = self.services.read().await;
            if !services.contains_key(path) {
                return Err(RegistryError::NotFound(path.to_string()));
            }
        }

        // Delegate to mount (which handles CAS).
        self.mount(namespace, path, entry, expected_version, auth)
            .await
    }

    /// Discover services by tags. Returns all services matching ALL provided tags,
    /// scoped to paths the caller can see.
    ///
    /// Discovery is scoped: only services mounted at paths the caller has authority
    /// for (per DFA classification) are returned.
    pub async fn discover(
        &self,
        namespace: &Namespace,
        tags: &[String],
        auth: &AuthLevel,
    ) -> Vec<MountedService> {
        let services = self.services.read().await;
        let mut results = Vec::new();

        for (_path, mounted) in services.iter() {
            // Check if entry matches ALL tags.
            let matches_tags = tags.iter().all(|tag| mounted.entry.tags.contains(tag));
            if !matches_tags {
                continue;
            }

            // Check if caller can see this path (authorization scope).
            if namespace.authorize(&mounted.path, auth).await.is_ok() {
                results.push(mounted.clone());
            }
        }

        results
    }

    /// Check health of a mounted service.
    ///
    /// In a real system this would make an HTTP call to the health endpoint.
    /// For now, we just return the current health status and mark the check time.
    pub async fn health(
        &self,
        namespace: &Namespace,
        path: &str,
        auth: &AuthLevel,
    ) -> Result<HealthStatus, RegistryError> {
        // Authorize.
        namespace
            .authorize(path, auth)
            .await
            .map_err(RegistryError::Unauthorized)?;

        let mut services = self.services.write().await;
        let mounted = services
            .get_mut(path)
            .ok_or_else(|| RegistryError::NotFound(path.to_string()))?;

        if mounted.entry.health_endpoint.is_none() {
            mounted.health = HealthStatus::NoEndpoint;
            return Ok(HealthStatus::NoEndpoint);
        }

        // In a real implementation, we'd make an HTTP request here.
        // For the demo, mark as healthy if a health endpoint is declared.
        mounted.health = HealthStatus::Healthy;
        mounted.last_health_check = Some(now_timestamp());

        Ok(mounted.health.clone())
    }

    /// Get all mounted services (admin view, no auth scoping).
    pub async fn all_services(&self) -> Vec<MountedService> {
        self.services.read().await.values().cloned().collect()
    }

    /// Get the count of mounted services.
    pub async fn service_count(&self) -> usize {
        self.services.read().await.len()
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn now_timestamp() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::governance::Participant;

    fn test_participants() -> Vec<Participant> {
        vec![
            Participant {
                id: "alice".into(),
                name: None,
                weight: 1,
            },
            Participant {
                id: "bob".into(),
                name: None,
                weight: 1,
            },
            Participant {
                id: "carol".into(),
                name: None,
                weight: 1,
            },
        ]
    }

    fn oracle_entry(owner: [u8; 32]) -> ServiceEntry {
        ServiceEntry {
            name: "price-oracle".to_string(),
            kind: ServiceKind::Oracle,
            sturdy_ref: "pyana://alice-fed/oracle-cell/abc123".to_string(),
            owner,
            version: 0, // will be set by mount
            tags: vec![
                "oracle".to_string(),
                "prices".to_string(),
                "defi".to_string(),
            ],
            description: "Real-time price feeds for ETH, BTC, SOL".to_string(),
            registered_at: 0, // will be set by mount
            expires_at: None,
            health_endpoint: Some("/health".to_string()),
        }
    }

    /// The "join and mount" flow from the spec.
    #[tokio::test]
    async fn join_and_mount_flow() {
        let ns = Namespace::new(test_participants(), [0xaa; 32]);
        let registry = Registry::new();

        let alice_key = [0x01; 32];

        // Alice mounts her oracle at /public/services/alice/price-oracle
        // (public route so anyone can discover it)
        let mounted = registry
            .mount(
                &ns,
                "/public/services/alice/price-oracle",
                oracle_entry(alice_key),
                0, // new mount
                &AuthLevel::Member,
            )
            .await
            .unwrap();

        assert_eq!(mounted.entry.version, 1);
        assert_eq!(mounted.entry.name, "price-oracle");
        assert_eq!(mounted.entry.kind, ServiceKind::Oracle);

        // Bob discovers it by tags
        let found = registry
            .discover(
                &ns,
                &["oracle".to_string(), "prices".to_string()],
                &AuthLevel::Anonymous,
            )
            .await;

        assert_eq!(found.len(), 1);
        assert_eq!(
            found[0].entry.sturdy_ref,
            "pyana://alice-fed/oracle-cell/abc123"
        );

        // Bob resolves the path to get the sturdy ref
        let resolved = registry
            .resolve(
                &ns,
                "/public/services/alice/price-oracle",
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();

        assert_eq!(
            resolved.entry.sturdy_ref,
            "pyana://alice-fed/oracle-cell/abc123"
        );
    }

    #[tokio::test]
    async fn cas_version_check() {
        let ns = Namespace::new(test_participants(), [0xbb; 32]);
        let registry = Registry::new();

        let owner = [0x02; 32];
        let entry = ServiceEntry {
            name: "compute-node".to_string(),
            kind: ServiceKind::Compute,
            sturdy_ref: "pyana://compute/cell/xyz".to_string(),
            owner,
            version: 0,
            tags: vec!["compute".to_string(), "gpu".to_string()],
            description: "GPU compute service".to_string(),
            registered_at: 0,
            expires_at: None,
            health_endpoint: None,
        };

        // First mount succeeds with expected_version=0
        let mounted = registry
            .mount(
                &ns,
                "/public/compute/node1",
                entry.clone(),
                0,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();
        assert_eq!(mounted.entry.version, 1);

        // Update with wrong version fails
        let err = registry
            .mount(
                &ns,
                "/public/compute/node1",
                entry.clone(),
                0,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap_err();
        assert!(matches!(err, RegistryError::VersionMismatch { .. }));

        // Update with correct version succeeds
        let updated = registry
            .mount(
                &ns,
                "/public/compute/node1",
                entry,
                1,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();
        assert_eq!(updated.entry.version, 2);
    }

    #[tokio::test]
    async fn unmount_removes_service() {
        let ns = Namespace::new(test_participants(), [0xcc; 32]);
        let registry = Registry::new();

        let entry = ServiceEntry {
            name: "temp-service".to_string(),
            kind: ServiceKind::Storage,
            sturdy_ref: "pyana://tmp/cell/1".to_string(),
            owner: [0x03; 32],
            version: 0,
            tags: vec!["storage".to_string()],
            description: "Temporary storage".to_string(),
            registered_at: 0,
            expires_at: Some(99999),
            health_endpoint: None,
        };

        registry
            .mount(&ns, "/public/tmp/store", entry, 0, &AuthLevel::Anonymous)
            .await
            .unwrap();

        // Unmount
        let removed = registry
            .unmount(&ns, "/public/tmp/store", &AuthLevel::Anonymous)
            .await
            .unwrap();
        assert_eq!(removed.entry.name, "temp-service");

        // Resolve now fails
        let err = registry
            .resolve(&ns, "/public/tmp/store", &AuthLevel::Anonymous)
            .await
            .unwrap_err();
        assert!(matches!(err, RegistryError::NotFound(_)));
    }

    #[tokio::test]
    async fn discovery_scoped_by_auth() {
        let ns = Namespace::new(test_participants(), [0xdd; 32]);
        let registry = Registry::new();

        let owner = [0x04; 32];

        // Mount a public service
        let public_entry = ServiceEntry {
            name: "public-oracle".to_string(),
            kind: ServiceKind::Oracle,
            sturdy_ref: "pyana://pub/oracle/1".to_string(),
            owner,
            version: 0,
            tags: vec!["oracle".to_string()],
            description: "Public oracle".to_string(),
            registered_at: 0,
            expires_at: None,
            health_endpoint: None,
        };
        registry
            .mount(
                &ns,
                "/public/oracles/pub",
                public_entry,
                0,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();

        // Mount a members-only service
        let member_entry = ServiceEntry {
            name: "member-oracle".to_string(),
            kind: ServiceKind::Oracle,
            sturdy_ref: "pyana://members/oracle/1".to_string(),
            owner,
            version: 0,
            tags: vec!["oracle".to_string()],
            description: "Members-only oracle".to_string(),
            registered_at: 0,
            expires_at: None,
            health_endpoint: None,
        };
        registry
            .mount(
                &ns,
                "/members/oracles/priv",
                member_entry,
                0,
                &AuthLevel::Member,
            )
            .await
            .unwrap();

        // Anonymous discovers: should only see public
        let anon_results = registry
            .discover(&ns, &["oracle".to_string()], &AuthLevel::Anonymous)
            .await;
        assert_eq!(anon_results.len(), 1);
        assert_eq!(anon_results[0].entry.name, "public-oracle");

        // Member discovers: should see both
        let member_results = registry
            .discover(&ns, &["oracle".to_string()], &AuthLevel::Member)
            .await;
        assert_eq!(member_results.len(), 2);
    }

    #[tokio::test]
    async fn health_check() {
        let ns = Namespace::new(test_participants(), [0xee; 32]);
        let registry = Registry::new();

        let entry = ServiceEntry {
            name: "healthy-service".to_string(),
            kind: ServiceKind::Compute,
            sturdy_ref: "pyana://health/cell/1".to_string(),
            owner: [0x05; 32],
            version: 0,
            tags: vec!["compute".to_string()],
            description: "A service with health checks".to_string(),
            registered_at: 0,
            expires_at: None,
            health_endpoint: Some("/health".to_string()),
        };

        registry
            .mount(&ns, "/public/healthy", entry, 0, &AuthLevel::Anonymous)
            .await
            .unwrap();

        let status = registry
            .health(&ns, "/public/healthy", &AuthLevel::Anonymous)
            .await
            .unwrap();

        // In the demo, declared health endpoint = healthy
        assert_eq!(status, HealthStatus::Healthy);
    }

    #[tokio::test]
    async fn unauthorized_mount_denied() {
        let ns = Namespace::new(test_participants(), [0xff; 32]);
        let registry = Registry::new();

        let entry = ServiceEntry {
            name: "sneaky-service".to_string(),
            kind: ServiceKind::Custom("backdoor".to_string()),
            sturdy_ref: "pyana://evil/cell/666".to_string(),
            owner: [0x06; 32],
            version: 0,
            tags: vec![],
            description: "Shouldn't be allowed".to_string(),
            registered_at: 0,
            expires_at: None,
            health_endpoint: None,
        };

        // Anonymous trying to mount in members-only path
        let err = registry
            .mount(&ns, "/members/sneaky", entry, 0, &AuthLevel::Anonymous)
            .await
            .unwrap_err();

        assert!(matches!(err, RegistryError::Unauthorized(_)));
    }
}
