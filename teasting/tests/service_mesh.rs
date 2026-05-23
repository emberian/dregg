//! Service registry integration tests: mount, discover, resolve, CAS, TTL, health.
//!
//! Tests the service mesh overlay that allows agents to register capabilities
//! at governed paths, discover services by tags, and resolve sturdy refs.
//!
//! Since the full governed-namespace Registry lives in a binary-only app crate,
//! these tests exercise the same patterns using inline data structures that
//! model the registry semantics (CAS mount, tag discovery, TTL expiry, health flags).

use std::collections::BTreeMap;

use pyana_captp::sturdy::SwissTable;
use pyana_captp::uri::PyanaUri;
use pyana_cell::AuthRequired;
use pyana_teasting::agent::SimAgent;
use pyana_teasting::federation::quick_federation;
use pyana_types::CellId;

// =============================================================================
// Inline service registry (models governed-namespace/src/registry.rs semantics)
// =============================================================================

/// Service kind classification.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum ServiceKind {
    Oracle,
    Compute,
    Storage,
}

/// Health status of a service.
#[derive(Clone, Debug, PartialEq, Eq)]
enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// A service entry in the registry.
#[derive(Clone, Debug)]
#[allow(dead_code)]
struct ServiceEntry {
    name: String,
    kind: ServiceKind,
    sturdy_ref: String,
    owner: [u8; 32],
    version: u64,
    tags: Vec<String>,
    registered_at: u64,
    expires_at: Option<u64>,
    health: HealthStatus,
}

/// Registry error types.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RegistryError {
    VersionMismatch {
        path: String,
        current: u64,
        expected: u64,
    },
    NotFound(String),
    InvalidPath(String),
}

/// A minimal service registry with CAS semantics.
struct ServiceRegistry {
    services: BTreeMap<String, ServiceEntry>,
}

impl ServiceRegistry {
    fn new() -> Self {
        Self {
            services: BTreeMap::new(),
        }
    }

    /// Mount a service at a path with CAS semantics.
    /// - If path doesn't exist: expected_version must be 0, service gets version=1.
    /// - If path exists: expected_version must match current version; version increments.
    fn mount(
        &mut self,
        path: &str,
        mut entry: ServiceEntry,
        expected_version: u64,
    ) -> Result<&ServiceEntry, RegistryError> {
        if path.is_empty() || !path.starts_with('/') {
            return Err(RegistryError::InvalidPath(
                "path must start with '/'".into(),
            ));
        }

        if let Some(existing) = self.services.get(path) {
            if existing.version != expected_version {
                return Err(RegistryError::VersionMismatch {
                    path: path.to_string(),
                    current: existing.version,
                    expected: expected_version,
                });
            }
            entry.version = existing.version + 1;
        } else {
            if expected_version != 0 {
                return Err(RegistryError::VersionMismatch {
                    path: path.to_string(),
                    current: 0,
                    expected: expected_version,
                });
            }
            entry.version = 1;
        }

        self.services.insert(path.to_string(), entry);
        Ok(self.services.get(path).unwrap())
    }

    /// Discover services matching all provided tags.
    fn discover(&self, tags: &[&str]) -> Vec<&ServiceEntry> {
        self.services
            .values()
            .filter(|entry| tags.iter().all(|tag| entry.tags.contains(&tag.to_string())))
            .collect()
    }

    /// Resolve a path to its service entry.
    fn resolve(&self, path: &str) -> Result<&ServiceEntry, RegistryError> {
        self.services
            .get(path)
            .ok_or_else(|| RegistryError::NotFound(path.to_string()))
    }

    /// Expire services past their TTL (block height).
    fn expire(&mut self, current_height: u64) -> usize {
        let expired_paths: Vec<String> = self
            .services
            .iter()
            .filter(|(_, entry)| {
                if let Some(exp) = entry.expires_at {
                    current_height >= exp
                } else {
                    false
                }
            })
            .map(|(path, _)| path.clone())
            .collect();

        let count = expired_paths.len();
        for path in expired_paths {
            self.services.remove(&path);
        }
        count
    }

    /// Mark a service as unhealthy.
    fn mark_unhealthy(&mut self, path: &str) -> Result<(), RegistryError> {
        let entry = self
            .services
            .get_mut(path)
            .ok_or_else(|| RegistryError::NotFound(path.to_string()))?;
        entry.health = HealthStatus::Unhealthy;
        Ok(())
    }

    /// Get service count.
    fn count(&self) -> usize {
        self.services.len()
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn make_oracle_entry(owner: [u8; 32], sturdy_ref: &str, registered_at: u64) -> ServiceEntry {
    ServiceEntry {
        name: "price-oracle".to_string(),
        kind: ServiceKind::Oracle,
        sturdy_ref: sturdy_ref.to_string(),
        owner,
        version: 0,
        tags: vec![
            "oracle".to_string(),
            "prices".to_string(),
            "defi".to_string(),
        ],
        registered_at,
        expires_at: None,
        health: HealthStatus::Unknown,
    }
}

fn make_compute_entry(owner: [u8; 32], sturdy_ref: &str, registered_at: u64) -> ServiceEntry {
    ServiceEntry {
        name: "gpu-compute".to_string(),
        kind: ServiceKind::Compute,
        sturdy_ref: sturdy_ref.to_string(),
        owner,
        version: 0,
        tags: vec!["compute".to_string(), "gpu".to_string()],
        registered_at,
        expires_at: None,
        health: HealthStatus::Unknown,
    }
}

// =============================================================================
// Test 1: Agent joins federation -> mounts a service at /services/agent/oracle
// =============================================================================

/// An agent mounts a service at a path, providing a sturdy ref. The mount
/// succeeds with version=1 on first registration.
#[test]
fn test_agent_mounts_service() {
    let mut harness = quick_federation();
    let alice = SimAgent::new("Alice");

    let mut registry = ServiceRegistry::new();

    // Alice has an oracle service with a sturdy ref.
    let mut swiss_table = SwissTable::new();
    let cell_id = CellId([0x11; 32]);
    let swiss = swiss_table.export(cell_id, AuthRequired::Signature, 0, None);
    let uri = swiss_table.make_uri([0xAA; 32], &swiss).unwrap();
    let uri_string = uri.to_uri_string();

    // Mount it.
    let entry = make_oracle_entry(
        alice.public_key().0,
        &uri_string,
        harness.clock.block_height,
    );
    let mounted = registry.mount("/services/alice/oracle", entry, 0).unwrap();

    assert_eq!(mounted.version, 1);
    assert_eq!(mounted.name, "price-oracle");
    assert_eq!(mounted.sturdy_ref, uri_string);

    harness.advance_blocks(1);
}

// =============================================================================
// Test 2: Other agent discovers via tags -> resolves -> gets sturdy ref
// =============================================================================

/// Bob discovers Alice's service by tags and resolves the path to get the
/// sturdy ref, which can then be parsed and enlivened.
#[test]
fn test_discover_and_resolve_service() {
    let mut harness = quick_federation();
    let alice = SimAgent::new("Alice");
    let _bob = SimAgent::new("Bob");

    let mut registry = ServiceRegistry::new();
    let mut swiss_table = SwissTable::new();

    // Alice mounts her oracle.
    let cell_id = CellId([0x22; 32]);
    let swiss = swiss_table.export(cell_id, AuthRequired::Signature, 0, None);
    let uri = swiss_table.make_uri([0xBB; 32], &swiss).unwrap();
    let uri_string = uri.to_uri_string();

    let entry = make_oracle_entry(
        alice.public_key().0,
        &uri_string,
        harness.clock.block_height,
    );
    registry.mount("/services/alice/oracle", entry, 0).unwrap();

    // Bob discovers by tags.
    let found = registry.discover(&["oracle", "prices"]);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, "price-oracle");

    // Bob resolves the path.
    let resolved = registry.resolve("/services/alice/oracle").unwrap();
    assert_eq!(resolved.sturdy_ref, uri_string);

    // Bob parses and enlivens the URI.
    let parsed = PyanaUri::parse(&resolved.sturdy_ref).unwrap();
    let enliven_result = swiss_table.enliven(&parsed.swiss, 10);
    assert!(enliven_result.is_ok());
    let entry = enliven_result.unwrap();
    assert_eq!(entry.cell_id, cell_id);

    harness.advance_blocks(1);
}

// =============================================================================
// Test 3: CAS semantics - concurrent mount at same path -> one fails
// =============================================================================

/// Two agents try to mount at the same path. The first succeeds (version 0->1).
/// The second fails with a version mismatch since it also expects version 0.
#[test]
fn test_cas_concurrent_mount_conflict() {
    let _harness = quick_federation();
    let alice = SimAgent::new("Alice");
    let bob = SimAgent::new("Bob");

    let mut registry = ServiceRegistry::new();

    // Alice mounts first.
    let alice_entry = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/swiss", 100);
    let result = registry.mount("/services/shared/oracle", alice_entry, 0);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().version, 1);

    // Bob tries to mount at the same path with expected_version=0 (stale).
    let bob_entry = make_compute_entry(bob.public_key().0, "pyana://bob/cell/swiss", 100);
    let err = registry
        .mount("/services/shared/oracle", bob_entry, 0)
        .unwrap_err();

    assert_eq!(
        err,
        RegistryError::VersionMismatch {
            path: "/services/shared/oracle".to_string(),
            current: 1,
            expected: 0,
        }
    );

    // Alice's service is still the one mounted.
    let resolved = registry.resolve("/services/shared/oracle").unwrap();
    assert_eq!(resolved.name, "price-oracle");
}

// =============================================================================
// Test 4: TTL expiry - mounted service expires after N blocks -> removed
// =============================================================================

/// A service with a TTL is automatically removed when the federation advances
/// past the expiration block height.
#[test]
fn test_ttl_expiry_removes_service() {
    let mut harness = quick_federation();
    let alice = SimAgent::new("Alice");

    let mut registry = ServiceRegistry::new();

    // Alice mounts a service that expires at block 50.
    let mut entry = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/swiss", 0);
    entry.expires_at = Some(50); // Expires at block 50.
    registry
        .mount("/services/alice/temp-oracle", entry, 0)
        .unwrap();

    assert_eq!(registry.count(), 1);

    // At block 49: not yet expired.
    let expired = registry.expire(49);
    assert_eq!(expired, 0);
    assert_eq!(registry.count(), 1);

    // At block 50: expired.
    harness.advance_blocks(50);
    let expired = registry.expire(50);
    assert_eq!(expired, 1);
    assert_eq!(registry.count(), 0);

    // Resolve now fails.
    let err = registry.resolve("/services/alice/temp-oracle").unwrap_err();
    assert!(matches!(err, RegistryError::NotFound(_)));
}

// =============================================================================
// Test 5: Health - mark service unhealthy -> still discoverable but flagged
// =============================================================================

/// An unhealthy service remains in the directory (discoverable) but its health
/// status is flagged so consumers can decide whether to use it.
#[test]
fn test_unhealthy_service_still_discoverable() {
    let _harness = quick_federation();
    let alice = SimAgent::new("Alice");

    let mut registry = ServiceRegistry::new();

    let entry = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/swiss", 100);
    registry.mount("/services/alice/oracle", entry, 0).unwrap();

    // Initially health is unknown.
    let resolved = registry.resolve("/services/alice/oracle").unwrap();
    assert_eq!(resolved.health, HealthStatus::Unknown);

    // Mark unhealthy (e.g., health check probe failed).
    registry.mark_unhealthy("/services/alice/oracle").unwrap();

    // Still discoverable.
    let found = registry.discover(&["oracle", "prices"]);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].health, HealthStatus::Unhealthy);

    // Still resolvable.
    let resolved = registry.resolve("/services/alice/oracle").unwrap();
    assert_eq!(resolved.health, HealthStatus::Unhealthy);
    assert_eq!(resolved.sturdy_ref, "pyana://alice/cell/swiss");
}

// =============================================================================
// Test 6: Update via CAS (version check)
// =============================================================================

/// A legitimate update succeeds when the correct version is provided.
/// The version increments on each successful update.
#[test]
fn test_cas_update_increments_version() {
    let _harness = quick_federation();
    let alice = SimAgent::new("Alice");

    let mut registry = ServiceRegistry::new();

    // Initial mount.
    let entry_v1 = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/v1", 100);
    registry
        .mount("/services/alice/oracle", entry_v1, 0)
        .unwrap();

    // Update with correct version (1).
    let entry_v2 = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/v2", 200);
    let updated = registry
        .mount("/services/alice/oracle", entry_v2, 1)
        .unwrap();
    assert_eq!(updated.version, 2);
    assert_eq!(updated.sturdy_ref, "pyana://alice/cell/v2");

    // Update again with correct version (2).
    let entry_v3 = make_oracle_entry(alice.public_key().0, "pyana://alice/cell/v3", 300);
    let updated = registry
        .mount("/services/alice/oracle", entry_v3, 2)
        .unwrap();
    assert_eq!(updated.version, 3);
    assert_eq!(updated.sturdy_ref, "pyana://alice/cell/v3");
}

// =============================================================================
// Test 7: Multiple services, multi-tag discovery
// =============================================================================

/// Multiple services are mounted. Discovery by multiple tags returns only
/// services matching ALL specified tags.
#[test]
fn test_multi_tag_discovery() {
    let _harness = quick_federation();
    let alice = SimAgent::new("Alice");
    let bob = SimAgent::new("Bob");

    let mut registry = ServiceRegistry::new();

    // Alice's oracle (tags: oracle, prices, defi).
    let alice_oracle = make_oracle_entry(alice.public_key().0, "pyana://alice/oracle/1", 100);
    registry
        .mount("/services/alice/oracle", alice_oracle, 0)
        .unwrap();

    // Bob's compute (tags: compute, gpu).
    let bob_compute = make_compute_entry(bob.public_key().0, "pyana://bob/compute/1", 100);
    registry
        .mount("/services/bob/compute", bob_compute, 0)
        .unwrap();

    // Alice's compute+oracle hybrid (tags: oracle, compute, prices).
    let alice_hybrid = ServiceEntry {
        name: "oracle-compute".to_string(),
        kind: ServiceKind::Oracle,
        sturdy_ref: "pyana://alice/hybrid/1".to_string(),
        owner: alice.public_key().0,
        version: 0,
        tags: vec![
            "oracle".to_string(),
            "compute".to_string(),
            "prices".to_string(),
        ],
        registered_at: 100,
        expires_at: None,
        health: HealthStatus::Healthy,
    };
    registry
        .mount("/services/alice/hybrid", alice_hybrid, 0)
        .unwrap();

    // Discover oracle services: Alice's oracle + Alice's hybrid.
    let oracle_results = registry.discover(&["oracle"]);
    assert_eq!(oracle_results.len(), 2);

    // Discover oracle+prices: Alice's oracle + Alice's hybrid.
    let oracle_prices = registry.discover(&["oracle", "prices"]);
    assert_eq!(oracle_prices.len(), 2);

    // Discover oracle+compute: only Alice's hybrid.
    let oracle_compute = registry.discover(&["oracle", "compute"]);
    assert_eq!(oracle_compute.len(), 1);
    assert_eq!(oracle_compute[0].name, "oracle-compute");

    // Discover gpu: only Bob's compute.
    let gpu_results = registry.discover(&["gpu"]);
    assert_eq!(gpu_results.len(), 1);
    assert_eq!(gpu_results[0].name, "gpu-compute");

    // Discover nonexistent tag: empty.
    let empty = registry.discover(&["nonexistent"]);
    assert!(empty.is_empty());
}
