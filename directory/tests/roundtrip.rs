//! End-to-end integration tests: register → lookup → revoke → discover.
//!
//! Exercises the four canonical `Directory` operations via `InMemoryDirectory`
//! plus the DFA-routed and meta-directory variants.

use pyana_directory::{
    Directory, DirectoryEntry, EntryKind, InMemoryDirectory, Listing, MetaDirectory, PeerHandle,
    ResourceHandle,
};

fn fixture_handle(seed: u8) -> ResourceHandle {
    ResourceHandle::new([seed; 32], [seed.wrapping_add(1); 32], [seed.wrapping_add(2); 32])
}

fn fixture_entry(seed: u8) -> DirectoryEntry {
    DirectoryEntry {
        handle: fixture_handle(seed),
        version: 0,
        kind: EntryKind::Service,
        description: Some(format!("entry-{seed}")),
        tags: vec!["test".into()],
        registered_at: 100,
        expires_at: None,
        revoked: false,
    }
}

// ============================================================================
// InMemoryDirectory round-trip
// ============================================================================

#[test]
fn register_lookup_roundtrip() {
    let mut dir = InMemoryDirectory::new();
    let entry = fixture_entry(1);
    let v = dir.register("alice", entry.clone()).unwrap();
    assert_eq!(v, 1);

    let got = dir.lookup("alice", 100).unwrap();
    assert_eq!(got.handle, fixture_handle(1));
    assert_eq!(got.description.as_deref(), Some("entry-1"));
}

#[test]
fn double_register_idempotent_on_exact_match() {
    let mut dir = InMemoryDirectory::new();
    let v1 = dir.register("alice", fixture_entry(1)).unwrap();
    let v2 = dir.register("alice", fixture_entry(1)).unwrap();
    assert_eq!(v1, v2, "re-registration of same entry must be idempotent");
}

#[test]
fn double_register_conflicts_on_different_handle() {
    use pyana_directory::DirectoryError;
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    let err = dir.register("alice", fixture_entry(2)).unwrap_err();
    assert!(matches!(err, DirectoryError::AlreadyRegistered(_)));
}

#[test]
fn revoke_then_lookup_fails() {
    use pyana_directory::DirectoryError;
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    dir.revoke("alice").unwrap();
    let err = dir.lookup("alice", 100).unwrap_err();
    assert!(matches!(err, DirectoryError::Revoked(_)));
}

#[test]
fn revoke_increments_version() {
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    let pre = dir.version();
    dir.revoke("alice").unwrap();
    assert_eq!(dir.version(), pre + 1);
}

#[test]
fn revoke_is_idempotent() {
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    let v1 = dir.revoke("alice").unwrap();
    let v2 = dir.revoke("alice").unwrap();
    assert_eq!(v1, v2);
}

#[test]
fn discover_by_tag() {
    let mut dir = InMemoryDirectory::new();
    let mut e1 = fixture_entry(1);
    e1.tags = vec!["storage".into()];
    dir.register("store.a", e1).unwrap();
    let mut e2 = fixture_entry(2);
    e2.tags = vec!["oracle".into()];
    dir.register("oracle.b", e2).unwrap();

    let Listing { entries, .. } = dir.discover(&pyana_directory::DiscoveryFilter {
        required_tags: vec!["storage".into()],
        ..Default::default()
    });
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].0, "store.a");
}

#[test]
fn discover_excludes_revoked_by_default() {
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    dir.revoke("alice").unwrap();

    let Listing { entries, .. } = dir.discover(&Default::default());
    assert_eq!(entries.len(), 0);
}

#[test]
fn discover_includes_revoked_when_flag_set() {
    use pyana_directory::DiscoveryFilter;
    let mut dir = InMemoryDirectory::new();
    dir.register("alice", fixture_entry(1)).unwrap();
    dir.revoke("alice").unwrap();

    let Listing { entries, .. } = dir.discover(&DiscoveryFilter {
        include_revoked: true,
        ..Default::default()
    });
    assert_eq!(entries.len(), 1);
}

#[test]
fn expiry_enforced_on_lookup() {
    use pyana_directory::DirectoryError;
    let mut dir = InMemoryDirectory::new();
    let mut e = fixture_entry(1);
    e.expires_at = Some(150);
    dir.register("ephemeral", e).unwrap();

    assert!(dir.lookup("ephemeral", 150).is_ok());
    let err = dir.lookup("ephemeral", 151).unwrap_err();
    assert!(matches!(err, DirectoryError::Expired(_)));
}

// ============================================================================
// MetaDirectory round-trip
// ============================================================================

#[test]
fn meta_directory_add_lookup_remove() {
    let mut md = MetaDirectory::new();
    let peer = PeerHandle {
        federation_id: [1u8; 32],
        directory: fixture_handle(1),
        label: Some("peer-alpha".into()),
    };
    assert!(md.add_peer(peer.clone()).is_none());
    assert_eq!(md.len(), 1);

    let got = md.get(&[1u8; 32]).unwrap();
    assert_eq!(got.label.as_deref(), Some("peer-alpha"));

    let removed = md.remove_peer(&[1u8; 32]).unwrap();
    assert_eq!(removed.federation_id, [1u8; 32]);
    assert!(md.is_empty());
}

#[test]
fn meta_directory_overwrite_returns_old() {
    let mut md = MetaDirectory::new();
    md.add_peer(PeerHandle {
        federation_id: [1u8; 32],
        directory: fixture_handle(1),
        label: Some("old".into()),
    });
    let old = md.add_peer(PeerHandle {
        federation_id: [1u8; 32],
        directory: fixture_handle(2),
        label: Some("new".into()),
    });
    assert_eq!(old.unwrap().label.as_deref(), Some("old"));
    assert_eq!(md.get(&[1u8; 32]).unwrap().label.as_deref(), Some("new"));
}

// ============================================================================
// ResourceHandle URI round-trip
// ============================================================================

#[test]
fn resource_handle_uri_contains_hex_fields() {
    let h = ResourceHandle::new([0xabu8; 32], [0xcdu8; 32], [0xefu8; 32]);
    let uri = h.to_uri();
    assert!(uri.starts_with("pyana://"), "URI must start with pyana://");
    // federation_id hex
    assert!(uri.contains("abababababababababababababababababababababababababababababababababab"));
}
