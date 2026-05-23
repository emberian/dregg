//! Simulated service mesh for testing mount/discover/resolve flows.
//!
//! Provides an in-process service registry that exercises the real DFA router
//! for path-based resolution, combined with tag-based service discovery.
//! This simulates the service mesh layer that sits above CapTP sessions.

use std::collections::HashMap;

use pyana_captp::GroupId;
use pyana_types::CellId;
use pyana_wire::dfa_router::RouteTarget;

use crate::router_sim::SimRouter;

/// Errors that can occur in the simulated service mesh.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MeshError {
    /// A service is already mounted at the given path.
    PathConflict { path: String },
    /// The path is invalid (empty, missing leading slash, etc.).
    InvalidPath { reason: String },
    /// The router failed to compile after adding the route.
    RouterCompileError { reason: String },
}

impl std::fmt::Display for MeshError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MeshError::PathConflict { path } => {
                write!(f, "service already mounted at path: {path}")
            }
            MeshError::InvalidPath { reason } => write!(f, "invalid path: {reason}"),
            MeshError::RouterCompileError { reason } => {
                write!(f, "router compile failed: {reason}")
            }
        }
    }
}

impl std::error::Error for MeshError {}

/// A service entry in the mesh registry.
#[derive(Clone, Debug)]
pub struct ServiceEntry {
    /// The mount path for this service (e.g., "/cells/stablecoin").
    pub path: String,
    /// The cell ID that handles requests for this service.
    pub cell_id: CellId,
    /// The federation hosting this service.
    pub federation_id: GroupId,
    /// The sturdy reference URI string for accessing this service.
    pub sturdy_ref: String,
    /// Human-readable service name.
    pub name: String,
    /// Discovery tags (e.g., ["defi", "stablecoin", "transfer"]).
    pub tags: Vec<String>,
    /// Protocol version this service supports.
    pub version: u32,
}

/// A simulated service registry for testing mount/discover/resolve flows.
///
/// Combines:
/// - A `HashMap` registry of service entries (for lookup by path and tag-based discovery)
/// - A `SimRouter` for DFA-based path classification
///
/// This lets tests exercise the full service mesh lifecycle: mount a service,
/// discover it by tags, and resolve a path to a sturdy reference.
pub struct SimServiceMesh {
    /// Service entries keyed by their mount path.
    pub registry: HashMap<String, ServiceEntry>,
    /// The underlying DFA router for path-based classification.
    pub router: SimRouter,
}

impl SimServiceMesh {
    /// Create a new empty service mesh.
    pub fn new() -> Self {
        // Start with an empty router (no routes)
        let router = SimRouter::with_routes(&[]);
        Self {
            registry: HashMap::new(),
            router,
        }
    }

    /// Mount a service at a path, making it discoverable and routable.
    ///
    /// The path must start with `/` and not already have a service mounted.
    /// After mounting, the DFA router is rebuilt to include a wildcard route
    /// for the new path prefix.
    pub fn mount(&mut self, entry: ServiceEntry) -> Result<(), MeshError> {
        let path = entry.path.clone();

        // Validate path
        if !path.starts_with('/') {
            return Err(MeshError::InvalidPath {
                reason: "path must start with '/'".to_string(),
            });
        }
        if path.is_empty() || path == "/" {
            return Err(MeshError::InvalidPath {
                reason: "path must have at least one segment".to_string(),
            });
        }

        // Check for conflicts
        if self.registry.contains_key(&path) {
            return Err(MeshError::PathConflict { path });
        }

        // Insert into registry
        self.registry.insert(path.clone(), entry);

        // Rebuild the router with all current routes
        self.rebuild_router();

        Ok(())
    }

    /// Unmount a service from the given path.
    ///
    /// Returns the removed `ServiceEntry` if it existed, or `None` if no service
    /// was mounted at that path.
    pub fn unmount(&mut self, path: &str) -> Option<ServiceEntry> {
        let entry = self.registry.remove(path)?;
        self.rebuild_router();
        Some(entry)
    }

    /// Discover services matching ALL of the given tags.
    ///
    /// Returns references to all service entries whose tag set is a superset
    /// of the query tags. An empty tag query returns all services.
    pub fn discover(&self, tags: &[&str]) -> Vec<&ServiceEntry> {
        self.registry
            .values()
            .filter(|entry| tags.iter().all(|tag| entry.tags.iter().any(|t| t == tag)))
            .collect()
    }

    /// Discover services by name prefix.
    pub fn discover_by_name(&self, prefix: &str) -> Vec<&ServiceEntry> {
        self.registry
            .values()
            .filter(|entry| entry.name.starts_with(prefix))
            .collect()
    }

    /// Resolve a path to a sturdy reference URI string.
    ///
    /// Uses the DFA router to classify the path, then looks up the matching
    /// service entry to return its sturdy ref.
    pub fn resolve(&self, path: &str) -> Option<&str> {
        // Use the router to classify
        let target = self.router.classify(path)?;

        // Find the matching service by cell ID
        match target {
            RouteTarget::Cell(cell_id) => {
                // Find the service entry that has this cell_id
                self.registry
                    .values()
                    .find(|entry| entry.cell_id == *cell_id)
                    .map(|entry| entry.sturdy_ref.as_str())
            }
            RouteTarget::Handler(name) => {
                // Look up by handler name matching service name
                self.registry
                    .values()
                    .find(|entry| entry.name == *name)
                    .map(|entry| entry.sturdy_ref.as_str())
            }
            _ => None,
        }
    }

    /// Resolve a path to the full service entry.
    pub fn resolve_entry(&self, path: &str) -> Option<&ServiceEntry> {
        let target = self.router.classify(path)?;

        match target {
            RouteTarget::Cell(cell_id) => self
                .registry
                .values()
                .find(|entry| entry.cell_id == *cell_id),
            RouteTarget::Handler(name) => self.registry.values().find(|entry| entry.name == *name),
            _ => None,
        }
    }

    /// Get the total number of mounted services.
    pub fn service_count(&self) -> usize {
        self.registry.len()
    }

    /// Check if a path has a service mounted.
    pub fn is_mounted(&self, path: &str) -> bool {
        self.registry.contains_key(path)
    }

    /// Rebuild the DFA router from the current registry.
    fn rebuild_router(&mut self) {
        let routes: Vec<(String, RouteTarget)> = self
            .registry
            .values()
            .map(|entry| {
                let pattern = format!("{}/*", entry.path);
                let target = RouteTarget::Cell(entry.cell_id);
                (pattern, target)
            })
            .collect();

        let route_refs: Vec<(&str, RouteTarget)> = routes
            .iter()
            .map(|(p, t)| (p.as_str(), t.clone()))
            .collect();

        self.router = SimRouter::with_routes(&route_refs);
    }
}

impl Default for SimServiceMesh {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell(n: u8) -> CellId {
        CellId([n; 32])
    }

    fn test_federation() -> GroupId {
        GroupId([0xAA; 32])
    }

    fn make_service(path: &str, name: &str, cell_byte: u8, tags: &[&str]) -> ServiceEntry {
        ServiceEntry {
            path: path.to_string(),
            cell_id: test_cell(cell_byte),
            federation_id: test_federation(),
            sturdy_ref: format!("pyana://test/{name}"),
            name: name.to_string(),
            tags: tags.iter().map(|s| s.to_string()).collect(),
            version: 1,
        }
    }

    #[test]
    fn mount_and_resolve() {
        let mut mesh = SimServiceMesh::new();

        let entry = make_service("/cells/stablecoin", "stablecoin", 0x01, &["defi", "token"]);
        mesh.mount(entry).unwrap();

        let resolved = mesh.resolve("/cells/stablecoin/transfer");
        assert_eq!(resolved, Some("pyana://test/stablecoin"));
    }

    #[test]
    fn mount_conflict_fails() {
        let mut mesh = SimServiceMesh::new();

        let entry1 = make_service("/cells/alpha", "alpha", 0x01, &[]);
        let entry2 = make_service("/cells/alpha", "alpha-dup", 0x02, &[]);

        mesh.mount(entry1).unwrap();
        let err = mesh.mount(entry2).unwrap_err();
        assert!(matches!(err, MeshError::PathConflict { .. }));
    }

    #[test]
    fn mount_invalid_path_fails() {
        let mut mesh = SimServiceMesh::new();

        let mut entry = make_service("/cells/alpha", "alpha", 0x01, &[]);
        entry.path = "no-leading-slash".to_string();
        let err = mesh.mount(entry).unwrap_err();
        assert!(matches!(err, MeshError::InvalidPath { .. }));
    }

    #[test]
    fn discover_by_tags() {
        let mut mesh = SimServiceMesh::new();

        mesh.mount(make_service(
            "/cells/stablecoin",
            "stablecoin",
            0x01,
            &["defi", "token"],
        ))
        .unwrap();
        mesh.mount(make_service("/cells/nft", "nft", 0x02, &["defi", "nft"]))
            .unwrap();
        mesh.mount(make_service(
            "/cells/oracle",
            "oracle",
            0x03,
            &["data", "oracle"],
        ))
        .unwrap();

        // Query for "defi" — should match stablecoin and nft
        let defi = mesh.discover(&["defi"]);
        assert_eq!(defi.len(), 2);

        // Query for "defi" + "token" — only stablecoin
        let defi_token = mesh.discover(&["defi", "token"]);
        assert_eq!(defi_token.len(), 1);
        assert_eq!(defi_token[0].name, "stablecoin");

        // Query for "data" — only oracle
        let data = mesh.discover(&["data"]);
        assert_eq!(data.len(), 1);
        assert_eq!(data[0].name, "oracle");

        // Empty query — all services
        let all = mesh.discover(&[]);
        assert_eq!(all.len(), 3);
    }

    #[test]
    fn unmount_removes_route() {
        let mut mesh = SimServiceMesh::new();

        mesh.mount(make_service("/cells/alpha", "alpha", 0x01, &[]))
            .unwrap();
        assert!(mesh.resolve("/cells/alpha/action").is_some());

        let removed = mesh.unmount("/cells/alpha");
        assert!(removed.is_some());
        assert_eq!(removed.unwrap().name, "alpha");

        // Route no longer resolves
        assert!(mesh.resolve("/cells/alpha/action").is_none());
    }

    #[test]
    fn multiple_services_resolve_independently() {
        let mut mesh = SimServiceMesh::new();

        mesh.mount(make_service("/cells/alpha", "alpha", 0x01, &[]))
            .unwrap();
        mesh.mount(make_service("/cells/beta", "beta", 0x02, &[]))
            .unwrap();

        assert_eq!(
            mesh.resolve("/cells/alpha/transfer"),
            Some("pyana://test/alpha")
        );
        assert_eq!(
            mesh.resolve("/cells/beta/balance"),
            Some("pyana://test/beta")
        );
        assert_eq!(mesh.resolve("/cells/gamma/x"), None);
    }

    #[test]
    fn resolve_entry_returns_full_metadata() {
        let mut mesh = SimServiceMesh::new();

        mesh.mount(make_service(
            "/cells/stablecoin",
            "stablecoin",
            0x01,
            &["defi"],
        ))
        .unwrap();

        let entry = mesh.resolve_entry("/cells/stablecoin/transfer").unwrap();
        assert_eq!(entry.name, "stablecoin");
        assert_eq!(entry.cell_id, test_cell(0x01));
        assert_eq!(entry.tags, vec!["defi"]);
    }
}
