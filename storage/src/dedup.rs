//! Deduplication filter using content hashes.
//!
//! Tracks recently-seen message hashes to prevent duplicates from retries.
//! Uses a bounded ring buffer to limit memory usage.

use std::collections::{HashSet, VecDeque};

/// Deduplication filter using content hashes.
/// Tracks recently-seen content hashes to prevent duplicates from retries.
#[derive(Debug, Clone)]
pub struct DeduplicationFilter {
    /// Recently seen content hashes.
    seen: HashSet<[u8; 32]>,
    /// Order of insertion (for eviction of oldest entries).
    order: VecDeque<[u8; 32]>,
    /// Maximum entries to track.
    capacity: usize,
}

impl DeduplicationFilter {
    /// Create a new deduplication filter with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            seen: HashSet::with_capacity(capacity),
            order: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// Check if a message has been seen before. If not, record it.
    /// Returns `true` if this is a DUPLICATE (already seen).
    pub fn is_duplicate(&mut self, content_hash: &[u8; 32]) -> bool {
        if self.seen.contains(content_hash) {
            return true;
        }

        // Not seen — record it.
        self.insert(*content_hash);
        false
    }

    /// Explicitly mark a hash as seen (for replay from WAL).
    pub fn mark_seen(&mut self, content_hash: &[u8; 32]) {
        if self.seen.contains(content_hash) {
            return; // Already tracked.
        }
        self.insert(*content_hash);
    }

    /// How many entries are currently tracked.
    pub fn len(&self) -> usize {
        self.seen.len()
    }

    /// Whether the filter is empty.
    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }

    /// The maximum capacity of this filter.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Insert a hash, evicting the oldest if at capacity.
    fn insert(&mut self, hash: [u8; 32]) {
        if self.order.len() >= self.capacity {
            // Evict the oldest.
            if let Some(oldest) = self.order.pop_front() {
                self.seen.remove(&oldest);
            }
        }
        self.seen.insert(hash);
        self.order.push_back(hash);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_message_accepted_duplicate_rejected() {
        let mut filter = DeduplicationFilter::new(100);
        let hash = *blake3::hash(b"hello").as_bytes();

        // First time: not a duplicate.
        assert!(!filter.is_duplicate(&hash));
        // Second time: duplicate.
        assert!(filter.is_duplicate(&hash));
        // Length is 1 (only tracked once).
        assert_eq!(filter.len(), 1);
    }

    #[test]
    fn capacity_eviction_oldest_forgotten() {
        let mut filter = DeduplicationFilter::new(3);

        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];
        let h4 = [4u8; 32];

        assert!(!filter.is_duplicate(&h1));
        assert!(!filter.is_duplicate(&h2));
        assert!(!filter.is_duplicate(&h3));
        assert_eq!(filter.len(), 3);

        // Adding h4 should evict h1.
        assert!(!filter.is_duplicate(&h4));
        assert_eq!(filter.len(), 3);

        // h1 is no longer tracked — appears as "new".
        assert!(!filter.is_duplicate(&h1));
        // h2, h3, h4 should still be seen (but h2 was evicted when h1 was re-added).
        // After re-adding h1: order is [h3, h4, h1], h2 was evicted.
        assert!(!filter.is_duplicate(&h2)); // h2 was evicted
    }

    #[test]
    fn mark_seen_for_replay() {
        let mut filter = DeduplicationFilter::new(100);
        let hash = [0xAA; 32];

        filter.mark_seen(&hash);
        assert_eq!(filter.len(), 1);

        // Now is_duplicate should return true.
        assert!(filter.is_duplicate(&hash));
        // Length unchanged (not double-inserted).
        assert_eq!(filter.len(), 1);
    }

    #[test]
    fn mark_seen_idempotent() {
        let mut filter = DeduplicationFilter::new(100);
        let hash = [0xBB; 32];

        filter.mark_seen(&hash);
        filter.mark_seen(&hash);
        filter.mark_seen(&hash);

        assert_eq!(filter.len(), 1);
    }

    #[test]
    fn different_hashes_all_accepted() {
        let mut filter = DeduplicationFilter::new(100);

        for i in 0u8..50 {
            let hash = *blake3::hash(&[i]).as_bytes();
            assert!(!filter.is_duplicate(&hash));
        }

        assert_eq!(filter.len(), 50);

        // All are duplicates now.
        for i in 0u8..50 {
            let hash = *blake3::hash(&[i]).as_bytes();
            assert!(filter.is_duplicate(&hash));
        }
    }

    #[test]
    fn empty_filter() {
        let filter = DeduplicationFilter::new(10);
        assert!(filter.is_empty());
        assert_eq!(filter.len(), 0);
        assert_eq!(filter.capacity(), 10);
    }
}
