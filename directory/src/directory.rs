//! The core `Directory` trait + in-memory reference implementation.
//!
//! Modelled on `rbg::directory::DirectoryCell` (the Robigalia-inspired
//! prototype). The four canonical operations:
//!
//! - **register** — bind a name to a resource handle. Idempotent on
//!   exact-match; conflicts on different-value-same-name.
//! - **lookup**   — resolve a name to its current entry.
//! - **revoke**   — mark an entry as revoked. Subsequent lookups fail.
//! - **discover** — search the directory by tag / kind / prefix.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;

use crate::ResourceHandle;

/// Monotonically increasing version counter used for CAS semantics.
pub type Version = u64;

/// What kind of capability an entry points at. Mirrors the
/// `rbg::directory::EntryKind` enum so the two crates can be
/// cross-compatible later.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EntryKind {
    /// An invocable service (cell with public methods).
    Service,
    /// A sub-directory (recursive scoping).
    SubDirectory,
    /// A data store / oracle (read-only).
    DataSource,
    /// A factory (creates new cells).
    Factory,
    /// An opaque capability the directory does not introspect.
    Capability,
}

/// A single directory entry. Versioned for CAS semantics.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectoryEntry {
    /// What this name resolves to.
    pub handle: ResourceHandle,
    /// Current version (monotonically increases on every mutation).
    pub version: Version,
    /// Kind of resource this entry represents.
    pub kind: EntryKind,
    /// Optional human-readable description.
    pub description: Option<String>,
    /// Filtering tags (e.g., ["storage", "oracle"]).
    pub tags: Vec<String>,
    /// Block height at registration.
    pub registered_at: u64,
    /// Block height at which the entry expires. `None` = no expiry.
    pub expires_at: Option<u64>,
    /// Whether the entry has been revoked. Revoked entries remain
    /// queryable (so lookups can return `Revoked`) but `lookup()`
    /// returns an explicit revocation error.
    pub revoked: bool,
}

/// Errors any directory implementation can raise.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum DirectoryError {
    #[error("entry not found: `{0}`")]
    NotFound(String),
    #[error("entry already registered with different value: `{0}`")]
    AlreadyRegistered(String),
    #[error("CAS conflict on `{name}`: expected version {expected}, actual {actual}")]
    VersionConflict {
        name: String,
        expected: Version,
        actual: Version,
    },
    #[error("entry `{0}` has been revoked")]
    Revoked(String),
    #[error("entry `{0}` has expired")]
    Expired(String),
    #[error("invalid name `{name}`: {reason}")]
    InvalidName { name: String, reason: String },
    #[error("directory is at capacity ({0} entries)")]
    Full(usize),
}

/// The canonical `Directory` trait.
///
/// Implementors may be thread-safe (in which case they own internal
/// locking) or single-threaded (callers must mediate). The trait does
/// not impose `Send + Sync`; consumers that need concurrent access wrap
/// the implementation in `Arc<RwLock<_>>`.
pub trait Directory {
    /// Register a name → resource handle binding.
    ///
    /// Returns the resulting version. If the name already exists with
    /// the same handle, this returns the existing version (idempotent).
    /// If the name exists with a different handle, returns
    /// [`DirectoryError::AlreadyRegistered`].
    fn register(&mut self, name: &str, entry: DirectoryEntry) -> Result<Version, DirectoryError>;

    /// Look up a name. Returns [`DirectoryError::NotFound`] if absent,
    /// [`DirectoryError::Revoked`] if revoked, [`DirectoryError::Expired`]
    /// if past its expiry.
    fn lookup(&self, name: &str, current_height: u64) -> Result<&DirectoryEntry, DirectoryError>;

    /// Revoke a name. Subsequent lookups will return
    /// [`DirectoryError::Revoked`].
    fn revoke(&mut self, name: &str) -> Result<Version, DirectoryError>;

    /// Discover entries matching the given filter.
    fn discover(&self, filter: &DiscoveryFilter) -> Listing;

    /// Get the current global version of the directory.
    fn version(&self) -> Version;

    /// Get the count of all entries (including revoked).
    fn len(&self) -> usize;

    /// Whether the directory has no entries.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Filter expression for [`Directory::discover`].
#[derive(Clone, Debug, Default)]
pub struct DiscoveryFilter {
    /// Match entries whose name starts with this prefix.
    pub name_prefix: Option<String>,
    /// Match entries that have ALL of these tags.
    pub required_tags: Vec<String>,
    /// Match entries with this kind.
    pub kind: Option<EntryKind>,
    /// Include revoked entries.
    pub include_revoked: bool,
}

/// A directory listing snapshot.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Listing {
    pub directory_version: Version,
    pub entries: Vec<(String, DirectoryEntry)>,
}

// ============================================================================
// In-memory reference implementation
// ============================================================================

/// Maximum entry-name length (chosen to match `rbg::directory`).
pub const MAX_NAME_LEN: usize = 256;

/// Default capacity for the in-memory directory.
pub const DEFAULT_MAX_ENTRIES: usize = 10_000;

/// In-process reference `Directory` implementation.
///
/// Backs the cell-state of a [`DirectoryCell`-shaped pattern](crate). The
/// canonical capacity is `DEFAULT_MAX_ENTRIES`. The `version` field
/// monotonically increments on every successful mutation; per-entry
/// `version` mirrors the directory version at the time of the entry's
/// last mutation.
#[derive(Clone, Debug)]
pub struct InMemoryDirectory {
    version: Version,
    entries: BTreeMap<String, DirectoryEntry>,
    max_entries: usize,
}

impl Default for InMemoryDirectory {
    fn default() -> Self {
        Self::new()
    }
}

impl InMemoryDirectory {
    pub fn new() -> Self {
        Self {
            version: 0,
            entries: BTreeMap::new(),
            max_entries: DEFAULT_MAX_ENTRIES,
        }
    }

    pub fn with_capacity(max_entries: usize) -> Self {
        Self {
            version: 0,
            entries: BTreeMap::new(),
            max_entries,
        }
    }

    /// Garbage-collect expired entries. Returns the number of entries removed.
    pub fn gc_expired(&mut self, current_height: u64) -> usize {
        let before = self.entries.len();
        self.entries.retain(|_, e| match e.expires_at {
            Some(h) => current_height <= h,
            None => true,
        });
        let removed = before - self.entries.len();
        if removed > 0 {
            self.version += 1;
        }
        removed
    }

    fn validate_name(name: &str) -> Result<(), DirectoryError> {
        if name.is_empty() {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: "empty name".into(),
            });
        }
        if name.len() > MAX_NAME_LEN {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: format!("exceeds {MAX_NAME_LEN}-byte limit"),
            });
        }
        if name.contains('\0') {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: "contains null byte".into(),
            });
        }
        Ok(())
    }
}

impl Directory for InMemoryDirectory {
    fn register(&mut self, name: &str, entry: DirectoryEntry) -> Result<Version, DirectoryError> {
        Self::validate_name(name)?;

        if let Some(existing) = self.entries.get(name) {
            // Idempotent on exact match. Compare on the (kind, handle)
            // tuple — version and registered_at differ and shouldn't
            // block re-registration of the same logical binding.
            if existing.kind == entry.kind && existing.handle == entry.handle && !existing.revoked {
                return Ok(existing.version);
            }
            return Err(DirectoryError::AlreadyRegistered(name.to_string()));
        }

        if self.entries.len() >= self.max_entries {
            return Err(DirectoryError::Full(self.max_entries));
        }

        self.version += 1;
        let mut entry = entry;
        entry.version = self.version;
        self.entries.insert(name.to_string(), entry);
        Ok(self.version)
    }

    fn lookup(&self, name: &str, current_height: u64) -> Result<&DirectoryEntry, DirectoryError> {
        let entry = self
            .entries
            .get(name)
            .ok_or_else(|| DirectoryError::NotFound(name.to_string()))?;
        if entry.revoked {
            return Err(DirectoryError::Revoked(name.to_string()));
        }
        if let Some(exp) = entry.expires_at {
            if current_height > exp {
                return Err(DirectoryError::Expired(name.to_string()));
            }
        }
        Ok(entry)
    }

    fn revoke(&mut self, name: &str) -> Result<Version, DirectoryError> {
        let entry = self
            .entries
            .get_mut(name)
            .ok_or_else(|| DirectoryError::NotFound(name.to_string()))?;
        if entry.revoked {
            return Ok(entry.version);
        }
        self.version += 1;
        entry.revoked = true;
        entry.version = self.version;
        Ok(self.version)
    }

    fn discover(&self, filter: &DiscoveryFilter) -> Listing {
        let entries = self
            .entries
            .iter()
            .filter(|(name, entry)| {
                if !filter.include_revoked && entry.revoked {
                    return false;
                }
                if let Some(prefix) = &filter.name_prefix {
                    if !name.starts_with(prefix) {
                        return false;
                    }
                }
                if let Some(kind) = &filter.kind {
                    if &entry.kind != kind {
                        return false;
                    }
                }
                if !filter
                    .required_tags
                    .iter()
                    .all(|t| entry.tags.iter().any(|et| et == t))
                {
                    return false;
                }
                true
            })
            .map(|(n, e)| (n.clone(), e.clone()))
            .collect();
        Listing {
            directory_version: self.version,
            entries,
        }
    }

    fn version(&self) -> Version {
        self.version
    }

    fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_handle(seed: u8) -> ResourceHandle {
        ResourceHandle {
            federation_id: [seed; 32],
            cell_id: [seed.wrapping_add(1); 32],
            swiss: [seed.wrapping_add(2); 32],
        }
    }

    fn fixture_entry(handle: ResourceHandle, height: u64) -> DirectoryEntry {
        DirectoryEntry {
            handle,
            version: 0,
            kind: EntryKind::Service,
            description: Some("test entry".into()),
            tags: vec!["test".into(), "service".into()],
            registered_at: height,
            expires_at: None,
            revoked: false,
        }
    }

    #[test]
    fn register_lookup_roundtrip() {
        let mut dir = InMemoryDirectory::new();
        let handle = fixture_handle(1);
        let entry = fixture_entry(handle.clone(), 100);
        let v = dir.register("alice", entry).unwrap();
        assert_eq!(v, 1);

        let got = dir.lookup("alice", 100).unwrap();
        assert_eq!(got.handle, handle);
        assert_eq!(got.version, 1);
    }

    #[test]
    fn register_idempotent_on_exact_match() {
        let mut dir = InMemoryDirectory::new();
        let handle = fixture_handle(1);
        let v1 = dir
            .register("alice", fixture_entry(handle.clone(), 100))
            .unwrap();
        let v2 = dir
            .register("alice", fixture_entry(handle.clone(), 200))
            .unwrap();
        // Idempotent: same version, no new mutation.
        assert_eq!(v1, v2);
        assert_eq!(dir.version(), 1);
    }

    #[test]
    fn register_conflicts_on_different_value() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        let err = dir
            .register("alice", fixture_entry(fixture_handle(2), 100))
            .unwrap_err();
        assert!(matches!(err, DirectoryError::AlreadyRegistered(_)));
    }

    #[test]
    fn lookup_missing_returns_not_found() {
        let dir = InMemoryDirectory::new();
        let err = dir.lookup("missing", 100).unwrap_err();
        assert!(matches!(err, DirectoryError::NotFound(_)));
    }

    #[test]
    fn revoke_then_lookup_fails() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        dir.revoke("alice").unwrap();
        let err = dir.lookup("alice", 100).unwrap_err();
        assert!(matches!(err, DirectoryError::Revoked(_)));
    }

    #[test]
    fn revoke_increments_version() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        assert_eq!(dir.version(), 1);
        dir.revoke("alice").unwrap();
        assert_eq!(dir.version(), 2);
    }

    #[test]
    fn revoke_missing_returns_not_found() {
        let mut dir = InMemoryDirectory::new();
        let err = dir.revoke("alice").unwrap_err();
        assert!(matches!(err, DirectoryError::NotFound(_)));
    }

    #[test]
    fn revoke_is_idempotent() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        let v1 = dir.revoke("alice").unwrap();
        let v2 = dir.revoke("alice").unwrap();
        assert_eq!(v1, v2);
    }

    #[test]
    fn lookup_expired_fails() {
        let mut dir = InMemoryDirectory::new();
        let mut e = fixture_entry(fixture_handle(1), 100);
        e.expires_at = Some(150);
        dir.register("alice", e).unwrap();

        assert!(dir.lookup("alice", 150).is_ok());
        let err = dir.lookup("alice", 200).unwrap_err();
        assert!(matches!(err, DirectoryError::Expired(_)));
    }

    #[test]
    fn discover_by_tag() {
        let mut dir = InMemoryDirectory::new();
        let mut e1 = fixture_entry(fixture_handle(1), 100);
        e1.tags = vec!["storage".into()];
        dir.register("foo", e1).unwrap();
        let mut e2 = fixture_entry(fixture_handle(2), 100);
        e2.tags = vec!["oracle".into()];
        dir.register("bar", e2).unwrap();

        let listing = dir.discover(&DiscoveryFilter {
            required_tags: vec!["storage".into()],
            ..Default::default()
        });
        assert_eq!(listing.entries.len(), 1);
        assert_eq!(listing.entries[0].0, "foo");
    }

    #[test]
    fn discover_by_prefix() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        dir.register("alex", fixture_entry(fixture_handle(2), 100))
            .unwrap();
        dir.register("bob", fixture_entry(fixture_handle(3), 100))
            .unwrap();

        let listing = dir.discover(&DiscoveryFilter {
            name_prefix: Some("al".into()),
            ..Default::default()
        });
        assert_eq!(listing.entries.len(), 2);
    }

    #[test]
    fn discover_excludes_revoked_by_default() {
        let mut dir = InMemoryDirectory::new();
        dir.register("alice", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        dir.revoke("alice").unwrap();
        let listing = dir.discover(&DiscoveryFilter::default());
        assert_eq!(listing.entries.len(), 0);

        let listing = dir.discover(&DiscoveryFilter {
            include_revoked: true,
            ..Default::default()
        });
        assert_eq!(listing.entries.len(), 1);
    }

    #[test]
    fn capacity_limit_enforced() {
        let mut dir = InMemoryDirectory::with_capacity(2);
        dir.register("a", fixture_entry(fixture_handle(1), 100))
            .unwrap();
        dir.register("b", fixture_entry(fixture_handle(2), 100))
            .unwrap();
        let err = dir
            .register("c", fixture_entry(fixture_handle(3), 100))
            .unwrap_err();
        assert!(matches!(err, DirectoryError::Full(2)));
    }

    #[test]
    fn invalid_names_rejected() {
        let mut dir = InMemoryDirectory::new();
        let err = dir
            .register("", fixture_entry(fixture_handle(1), 100))
            .unwrap_err();
        assert!(matches!(err, DirectoryError::InvalidName { .. }));

        let err = dir
            .register("with\0null", fixture_entry(fixture_handle(1), 100))
            .unwrap_err();
        assert!(matches!(err, DirectoryError::InvalidName { .. }));
    }

    #[test]
    fn gc_expired_removes_old_entries() {
        let mut dir = InMemoryDirectory::new();
        let mut e1 = fixture_entry(fixture_handle(1), 100);
        e1.expires_at = Some(150);
        dir.register("alice", e1).unwrap();
        let e2 = fixture_entry(fixture_handle(2), 100);
        dir.register("bob", e2).unwrap();

        let removed = dir.gc_expired(200);
        assert_eq!(removed, 1);
        assert_eq!(dir.len(), 1);
    }
}
