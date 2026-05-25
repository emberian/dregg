//! Meta-directory: directory-of-directories for federation peer discovery.
//!
//! Lifted from `rbg::directory::MetaDirectory`. A `MetaDirectory`
//! enumerates other directories (typically one per federation peer);
//! cross-federation resolution starts here and recurses into the
//! discovered directory cell.

use crate::ResourceHandle;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// A peer handle: identifies a single federation by its 32-byte id and
/// names the directory cell that catalogs that federation's services.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PeerHandle {
    /// 32-byte federation id.
    pub federation_id: [u8; 32],
    /// The directory cell that serves this federation's name table.
    pub directory: ResourceHandle,
    /// Optional human-readable label.
    pub label: Option<String>,
}

/// A directory-of-directories.
///
/// Keys are federation ids. Values are peer handles pointing at each
/// federation's directory cell. The structure is deliberately simple:
/// constitution-level changes (which federations are recognized) take
/// place via a route-table swap on the host (see
/// `pyana_directory::DfaRoutedDirectory`).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MetaDirectory {
    peers: BTreeMap<[u8; 32], PeerHandle>,
}

impl MetaDirectory {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a peer federation. Returns `Some(old)` if a peer with
    /// the same id existed.
    pub fn add_peer(&mut self, peer: PeerHandle) -> Option<PeerHandle> {
        self.peers.insert(peer.federation_id, peer)
    }

    /// Remove a peer federation.
    pub fn remove_peer(&mut self, federation_id: &[u8; 32]) -> Option<PeerHandle> {
        self.peers.remove(federation_id)
    }

    /// Look up a peer by federation id.
    pub fn get(&self, federation_id: &[u8; 32]) -> Option<&PeerHandle> {
        self.peers.get(federation_id)
    }

    /// All peers, sorted by federation id.
    pub fn peers(&self) -> impl Iterator<Item = &PeerHandle> {
        self.peers.values()
    }

    pub fn len(&self) -> usize {
        self.peers.len()
    }

    pub fn is_empty(&self) -> bool {
        self.peers.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_peer(id: u8) -> PeerHandle {
        PeerHandle {
            federation_id: [id; 32],
            directory: ResourceHandle {
                federation_id: [id; 32],
                cell_id: [id.wrapping_add(1); 32],
                swiss: [id.wrapping_add(2); 32],
            },
            label: Some(format!("peer-{id}")),
        }
    }

    #[test]
    fn add_and_lookup_peer() {
        let mut md = MetaDirectory::new();
        md.add_peer(fixture_peer(1));
        let got = md.get(&[1u8; 32]).unwrap();
        assert_eq!(got.label.as_deref(), Some("peer-1"));
    }

    #[test]
    fn add_peer_returns_previous() {
        let mut md = MetaDirectory::new();
        assert!(md.add_peer(fixture_peer(1)).is_none());
        let prev = md.add_peer(PeerHandle {
            federation_id: [1u8; 32],
            directory: fixture_peer(1).directory,
            label: Some("renamed".into()),
        });
        assert!(prev.is_some());
    }

    #[test]
    fn remove_peer_succeeds() {
        let mut md = MetaDirectory::new();
        md.add_peer(fixture_peer(1));
        md.add_peer(fixture_peer(2));
        let removed = md.remove_peer(&[1u8; 32]);
        assert!(removed.is_some());
        assert_eq!(md.len(), 1);
    }
}
