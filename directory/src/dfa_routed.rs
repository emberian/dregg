//! DFA-routed directory composition.
//!
//! Some name-shaped workloads want the lookup logic to be table-driven
//! and governance-mediated: a federation votes on which prefix patterns
//! resolve where, then atomically swaps the active table. The
//! `apps/governed-namespace/` app implemented this in 740 lines of
//! ad-hoc Rust; this module collapses that to a thin composition over
//! `pyana-dfa::RouteTable` + an [`InMemoryDirectory`].
//!
//! # Shape
//!
//! - A `RouteTable` maps name prefixes to *resolution policies* (e.g.,
//!   "names starting with `system.` resolve via the system directory,
//!   `app.<name>` resolves to user-managed factories").
//! - The active table has a `RouteTableId` — a 32-byte hash for
//!   constitution-binding.
//! - [`DfaRoutedDirectory`] holds a current `RouteTable` plus the
//!   primary [`InMemoryDirectory`]. Lookup runs the name through the
//!   route table; only when the table says "Handler('local')" does the
//!   lookup hit the directory.
//! - [`DfaRoutedDirectory::propose_swap`] stages a new table. The
//!   pending swap commits only via [`Self::commit_swap`] when supplied
//!   a `GovernanceProof` — the pattern lifted from
//!   `apps/governed-namespace/governance.rs`.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

pub use pyana_dfa::router::RouteTable;
use pyana_dfa::router::{RouteTableBuilder, RouteTarget, Router};

use crate::directory::{
    Directory, DirectoryEntry, DirectoryError, DiscoveryFilter, InMemoryDirectory, Listing, Version,
};

/// 32-byte identifier for a `RouteTable`. Stable hash of the table's
/// canonical encoding; used as the commitment in governance proofs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RouteTableId(pub [u8; 32]);

/// Errors raised when staging or committing a route-table swap.
#[derive(Debug, Error)]
pub enum TableSwapError {
    #[error("no swap pending")]
    NoPendingSwap,
    #[error("governance proof does not authorize the pending swap")]
    UnauthorizedSwap,
    #[error(
        "staged table id `{staged_hex}` does not match governance commitment `{committed_hex}`"
    )]
    CommitmentMismatch {
        staged_hex: String,
        committed_hex: String,
    },
    #[error("route-table build failed: {0}")]
    BuildError(String),
}

/// A directory whose lookups are routed through a governance-bound
/// route table.
pub struct DfaRoutedDirectory {
    /// The live router wrapping the currently-active route table.
    active_router: Router,
    /// Identifier (32-byte canonical hash) of the active route table.
    active_id: RouteTableId,
    /// Underlying directory used when the route table dispatches a name
    /// to `RouteTarget::Handler("local")`.
    local: InMemoryDirectory,
    /// Pending route-table swap, if any.
    pending: Option<(RouteTableId, RouteTable)>,
    /// Sub-directories registered against `RouteTarget::Handler("dir:<name>")`.
    /// Looking up a name whose policy says "dir:foo" defers to the
    /// sub-directory with handler name `foo`.
    sub_directories: HashMap<String, InMemoryDirectory>,
}

impl DfaRoutedDirectory {
    /// Build a new routed directory with an explicit initial route table.
    pub fn new(initial_table: RouteTable) -> Self {
        let id = RouteTableId(initial_table.commitment);
        Self {
            active_router: Router::new(initial_table),
            active_id: id,
            local: InMemoryDirectory::new(),
            pending: None,
            sub_directories: HashMap::new(),
        }
    }

    /// Build with a `RouteTableBuilder` (convenience).
    pub fn with_builder(b: RouteTableBuilder) -> Self {
        Self::new(b.compile())
    }

    /// Current route-table id.
    pub fn active_table_id(&self) -> RouteTableId {
        self.active_id
    }

    /// Read-only access to the local directory.
    pub fn local_directory(&self) -> &InMemoryDirectory {
        &self.local
    }

    /// Register a sub-directory under the given handler name. Lookups
    /// routed to `Handler("dir:<name>")` resolve via this sub-directory.
    pub fn add_sub_directory(&mut self, handler_name: impl Into<String>) {
        self.sub_directories
            .insert(handler_name.into(), InMemoryDirectory::new());
    }

    /// Mutable access to a registered sub-directory.
    pub fn sub_directory_mut(&mut self, handler_name: &str) -> Option<&mut InMemoryDirectory> {
        self.sub_directories.get_mut(handler_name)
    }

    /// Stage a new route table. The swap commits only via
    /// [`Self::commit_swap`] with a matching governance commitment.
    pub fn propose_swap(&mut self, new_table: RouteTable) -> RouteTableId {
        let id = RouteTableId(new_table.commitment);
        self.pending = Some((id, new_table));
        id
    }

    /// Commit the staged swap. `governance_commitment` is the
    /// `RouteTableId` the federation's governance proof actually
    /// signed; if it doesn't match the staged table's id, the swap is
    /// rejected.
    pub fn commit_swap(
        &mut self,
        governance_commitment: RouteTableId,
    ) -> Result<RouteTableId, TableSwapError> {
        let (staged_id, staged_table) = self.pending.take().ok_or(TableSwapError::NoPendingSwap)?;
        if staged_id != governance_commitment {
            // Re-stage and return error.
            self.pending = Some((staged_id, staged_table));
            return Err(TableSwapError::CommitmentMismatch {
                staged_hex: hex_encode(&staged_id.0),
                committed_hex: hex_encode(&governance_commitment.0),
            });
        }
        self.active_router = Router::new(staged_table);
        self.active_id = staged_id;
        Ok(staged_id)
    }

    /// Cancel a pending swap.
    pub fn cancel_swap(&mut self) {
        self.pending = None;
    }

    /// Has a swap been staged?
    pub fn has_pending_swap(&self) -> bool {
        self.pending.is_some()
    }
}

impl Directory for DfaRoutedDirectory {
    /// Register a name. Always lands in the local directory by default
    /// — the route table affects lookup, not registration. (Apps that
    /// need cross-directory registration should pick up the matching
    /// sub-directory via `sub_directory_mut` and register there.)
    fn register(&mut self, name: &str, entry: DirectoryEntry) -> Result<Version, DirectoryError> {
        self.local.register(name, entry)
    }

    fn lookup(&self, name: &str, current_height: u64) -> Result<&DirectoryEntry, DirectoryError> {
        // Run the name through the active DFA route table. The result
        // tells us *which directory* to ask. The DFA crate operates on
        // bytestrings; we feed the name's bytes through.
        match self.active_router.classify(name.as_bytes()) {
            None => self.local.lookup(name, current_height),
            Some(classification) => match classification.target {
                RouteTarget::Drop => Err(DirectoryError::Revoked(name.to_string())),
                RouteTarget::Handler(h) if h == "local" => self.local.lookup(name, current_height),
                RouteTarget::Handler(h) if h.starts_with("dir:") => {
                    let dir_name = &h["dir:".len()..];
                    self.sub_directories
                        .get(dir_name)
                        .ok_or_else(|| DirectoryError::NotFound(name.to_string()))?
                        .lookup(name, current_height)
                }
                // Unknown / federation handlers fall through to the local
                // directory so this composition degrades gracefully when a
                // freshly-installed route table references handlers the
                // host hasn't bound yet.
                _ => self.local.lookup(name, current_height),
            },
        }
    }

    fn revoke(&mut self, name: &str) -> Result<Version, DirectoryError> {
        // Revocation propagates through the local directory only.
        // Per-sub-directory revocation goes through the sub-directory
        // handle directly.
        self.local.revoke(name)
    }

    fn discover(&self, filter: &DiscoveryFilter) -> Listing {
        // Discovery merges across local + sub-directories.
        let mut entries = self.local.discover(filter).entries;
        for (_handler, sub) in &self.sub_directories {
            entries.extend(sub.discover(filter).entries);
        }
        Listing {
            directory_version: self.local.version(),
            entries,
        }
    }

    fn version(&self) -> Version {
        self.local.version()
    }

    fn len(&self) -> usize {
        self.local.len()
            + self
                .sub_directories
                .values()
                .map(|s| s.len())
                .sum::<usize>()
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ResourceHandle;
    use crate::directory::EntryKind;
    use pyana_dfa::router::RouteTableBuilder;

    fn fixture_entry(seed: u8) -> DirectoryEntry {
        DirectoryEntry {
            handle: ResourceHandle {
                federation_id: [seed; 32],
                cell_id: [seed.wrapping_add(1); 32],
                swiss: [seed.wrapping_add(2); 32],
            },
            version: 0,
            kind: EntryKind::Service,
            description: None,
            tags: vec![],
            registered_at: 100,
            expires_at: None,
            revoked: false,
        }
    }

    fn build_default_table() -> RouteTable {
        RouteTableBuilder::new()
            .route("system.*", RouteTarget::handler("dir:system"))
            .route("*", RouteTarget::handler("local"))
            .compile()
    }

    fn build_strict_table() -> RouteTable {
        // Drop everything starting with "blocked.", route system.* to a
        // sub-directory, everything else local.
        RouteTableBuilder::new()
            .route("blocked.*", RouteTarget::drop())
            .route("system.*", RouteTarget::handler("dir:system"))
            .route("*", RouteTarget::handler("local"))
            .compile()
    }

    #[test]
    fn lookup_routes_to_local_by_default() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        d.register("alice", fixture_entry(1)).unwrap();
        let got = d.lookup("alice", 100).unwrap();
        assert_eq!(got.handle.federation_id, [1u8; 32]);
    }

    #[test]
    fn lookup_routes_to_sub_directory_by_prefix() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        d.add_sub_directory("system");
        d.sub_directory_mut("system")
            .unwrap()
            .register("system.metrics", fixture_entry(7))
            .unwrap();

        let got = d.lookup("system.metrics", 100).unwrap();
        assert_eq!(got.handle.federation_id, [7u8; 32]);
    }

    #[test]
    fn lookup_drops_when_table_says_drop() {
        let mut d = DfaRoutedDirectory::new(build_strict_table());
        d.register("blocked.bad", fixture_entry(9)).unwrap();
        // Even though it's in the local directory, the route says drop.
        let err = d.lookup("blocked.bad", 100).unwrap_err();
        assert!(matches!(err, DirectoryError::Revoked(_)));
    }

    #[test]
    fn propose_swap_does_not_change_active_until_commit() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        let old_id = d.active_table_id();

        let new_id = d.propose_swap(build_strict_table());
        assert!(d.has_pending_swap());
        assert_eq!(d.active_table_id(), old_id);

        // Wrong governance commitment → reject.
        let bad = RouteTableId([0xffu8; 32]);
        let err = d.commit_swap(bad).unwrap_err();
        assert!(matches!(err, TableSwapError::CommitmentMismatch { .. }));
        // Pending should still be there.
        assert!(d.has_pending_swap());

        // Right commitment → commit.
        let committed = d.commit_swap(new_id).unwrap();
        assert_eq!(committed, new_id);
        assert_eq!(d.active_table_id(), new_id);
        assert!(!d.has_pending_swap());
    }

    #[test]
    fn cancel_swap_clears_pending() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        d.propose_swap(build_strict_table());
        d.cancel_swap();
        assert!(!d.has_pending_swap());
    }

    #[test]
    fn commit_swap_without_pending_fails() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        let err = d.commit_swap(RouteTableId([0u8; 32])).unwrap_err();
        assert!(matches!(err, TableSwapError::NoPendingSwap));
    }

    #[test]
    fn governance_transition_changes_routing_behavior() {
        let mut d = DfaRoutedDirectory::new(build_default_table());
        d.register("blocked.thing", fixture_entry(3)).unwrap();
        // Default table: no prefix rule for "blocked.*", routes to local.
        assert!(d.lookup("blocked.thing", 100).is_ok());

        let strict_id = d.propose_swap(build_strict_table());
        d.commit_swap(strict_id).unwrap();

        // After governance swap: blocked.* is dropped.
        let err = d.lookup("blocked.thing", 100).unwrap_err();
        assert!(matches!(err, DirectoryError::Revoked(_)));
    }
}
