//! The grain's private data = a dregg cell's **umem heap**.
//!
//! In Sandstorm a grain's `/var` is a read-write bind-mount, private to that grain,
//! that the app stores its database/state in. On dregg that `/var` *is* the cell's
//! umem heap: a keyed byte store that commits to a content-addressed **`data_root`**.
//! The difference Sandstorm cannot offer: the root is a commitment, so a checkpoint
//! is re-witnessable (a backup that proves what it contains), and the transitions —
//! not just a snapshot — are what get committed.
//!
//! This is the prototype's stand-in for `turn/src/umem.rs` + `durable/`: a real
//! content-addressed heap (sha256 over the sorted entries) with the same shape the
//! grain lifecycle leans on (commit → `data_root`; restore from a `data_root`).

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use crate::spk::base32;

/// A content commitment to a umem heap state (`data_root`). Deterministic in the
/// heap contents, order-free.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DataRoot(pub String);

/// The grain's read-write `/var`, realized as a dregg cell's umem heap.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Umem {
    entries: BTreeMap<String, Vec<u8>>,
}

impl Umem {
    pub fn new() -> Self {
        Umem::default()
    }

    pub fn get(&self, key: &str) -> Option<&[u8]> {
        self.entries.get(key).map(|v| v.as_slice())
    }

    pub fn put(&mut self, key: impl Into<String>, value: impl Into<Vec<u8>>) {
        self.entries.insert(key.into(), value.into());
    }

    pub fn remove(&mut self, key: &str) -> bool {
        self.entries.remove(key).is_some()
    }

    /// Drop every entry — used when a workload returns a fresh `/var` image.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Iterate the heap entries (`key -> bytes`) in sorted key order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.entries.iter().map(|(k, v)| (k.as_str(), v.as_slice()))
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Total stored bytes — the storage meter's input (per-MB billing).
    pub fn stored_bytes(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Commit to the current heap state — the `data_root` a checkpoint records.
    /// Content-addressed (sha256 over the sorted `key\0len\0value` entries), so two
    /// heaps with the same contents commit to the same root regardless of insert
    /// order — the property that makes a checkpoint re-witnessable.
    pub fn commit(&self) -> DataRoot {
        let mut h = Sha256::new();
        h.update((self.entries.len() as u64).to_le_bytes());
        for (k, v) in &self.entries {
            h.update((k.len() as u64).to_le_bytes());
            h.update(k.as_bytes());
            h.update((v.len() as u64).to_le_bytes());
            h.update(v);
        }
        let digest = h.finalize();
        DataRoot(format!("umem1{}", base32(&digest)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_is_order_free_and_content_addressed() {
        let mut a = Umem::new();
        a.put("notes/1", b"hello".to_vec());
        a.put("notes/2", b"world".to_vec());

        let mut b = Umem::new();
        // Insert in the opposite order.
        b.put("notes/2", b"world".to_vec());
        b.put("notes/1", b"hello".to_vec());

        assert_eq!(a.commit(), b.commit());

        // A different value → a different root.
        b.put("notes/2", b"WORLD".to_vec());
        assert_ne!(a.commit(), b.commit());
    }

    #[test]
    fn empty_commit_is_stable() {
        assert_eq!(Umem::new().commit(), Umem::new().commit());
        assert!(Umem::new().commit().0.starts_with("umem1"));
    }
}
