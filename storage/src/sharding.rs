//! Queue sharding for hot queues.
//!
//! A `ShardedQueue` splits a single logical queue across N physical shards.
//! Messages are routed to shards by content hash (deterministic).
//! Readers can query any shard independently.

use crate::queue::{DequeueProof, MerkleQueue, QueueEntry, QueueError};

// ============================================================================
// Core types
// ============================================================================

/// A sharded queue: splits a single logical queue across N physical shards.
/// Messages are routed to shards by content hash (deterministic).
/// Readers can query any shard independently.
pub struct ShardedQueue {
    /// Physical shard queues.
    shards: Vec<MerkleQueue>,
    /// Number of shards.
    shard_count: usize,
    /// Combined root (hash of all shard roots).
    combined_root: [u8; 32],
    /// Round-robin counter for dequeue_any.
    round_robin: usize,
}

// ============================================================================
// Implementation
// ============================================================================

impl ShardedQueue {
    /// Create a new sharded queue with the given number of shards and capacity per shard.
    pub fn new(shard_count: usize, capacity_per_shard: usize) -> Self {
        let shard_count = shard_count.max(1);
        let shards: Vec<MerkleQueue> = (0..shard_count)
            .map(|_| MerkleQueue::new(capacity_per_shard))
            .collect();

        let combined_root = compute_combined_root(&shards);

        Self {
            shards,
            shard_count,
            combined_root,
            round_robin: 0,
        }
    }

    /// Route a message to its shard (deterministic by content hash).
    fn shard_for(&self, content_hash: &[u8; 32]) -> usize {
        // Use first 8 bytes as a u64, mod shard_count.
        let n = u64::from_le_bytes(content_hash[..8].try_into().unwrap());
        (n as usize) % self.shard_count
    }

    /// Enqueue to the appropriate shard (determined by content hash).
    pub fn enqueue(&mut self, entry: QueueEntry) -> Result<[u8; 32], QueueError> {
        let shard_idx = self.shard_for(&entry.content_hash);
        self.shards[shard_idx].enqueue(entry)?;
        self.update_combined_root();
        Ok(self.combined_root)
    }

    /// Dequeue from a specific shard.
    pub fn dequeue_shard(&mut self, shard: usize) -> Result<(QueueEntry, DequeueProof), QueueError> {
        if shard >= self.shard_count {
            return Err(QueueError::Empty);
        }
        let result = self.shards[shard].dequeue()?;
        self.update_combined_root();
        Ok(result)
    }

    /// Dequeue from any shard that has messages (round-robin).
    /// Returns the entry, proof, and which shard it came from.
    pub fn dequeue_any(&mut self) -> Result<(QueueEntry, DequeueProof, usize), QueueError> {
        // Try each shard starting from round_robin position.
        for i in 0..self.shard_count {
            let shard_idx = (self.round_robin + i) % self.shard_count;
            if !self.shards[shard_idx].is_empty() {
                let result = self.shards[shard_idx].dequeue()?;
                self.round_robin = (shard_idx + 1) % self.shard_count;
                self.update_combined_root();
                return Ok((result.0, result.1, shard_idx));
            }
        }
        Err(QueueError::Empty)
    }

    /// Combined root (proves state of ALL shards).
    pub fn combined_root(&self) -> [u8; 32] {
        self.combined_root
    }

    /// Total messages across all shards.
    pub fn total_len(&self) -> usize {
        self.shards.iter().map(|s| s.len()).sum()
    }

    /// Number of shards.
    pub fn shard_count(&self) -> usize {
        self.shard_count
    }

    /// Length of a specific shard.
    pub fn shard_len(&self, shard: usize) -> usize {
        if shard >= self.shard_count {
            return 0;
        }
        self.shards[shard].len()
    }

    /// Whether all shards are empty.
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.is_empty())
    }

    /// Rebalance: move messages from overloaded shards to underloaded ones.
    /// Returns the number of messages moved.
    pub fn rebalance(&mut self) -> usize {
        let total = self.total_len();
        if total == 0 || self.shard_count <= 1 {
            return 0;
        }

        let target_per_shard = total / self.shard_count;
        let mut moved = 0;

        // Collect messages from overloaded shards.
        let mut overflow: Vec<QueueEntry> = Vec::new();
        for shard in &mut self.shards {
            while shard.len() > target_per_shard + 1 {
                match shard.dequeue() {
                    Ok((entry, _)) => overflow.push(entry),
                    Err(_) => break,
                }
            }
        }

        // Distribute to underloaded shards.
        for entry in overflow {
            // Find the shard with the fewest entries.
            let min_shard_idx = self
                .shards
                .iter()
                .enumerate()
                .min_by_key(|(_, s)| s.len())
                .map(|(idx, _)| idx)
                .unwrap_or(0);

            if self.shards[min_shard_idx].enqueue(entry).is_ok() {
                moved += 1;
            }
        }

        if moved > 0 {
            self.update_combined_root();
        }
        moved
    }

    /// Recompute the combined root from all shard roots.
    fn update_combined_root(&mut self) {
        self.combined_root = compute_combined_root(&self.shards);
    }
}

/// Compute the combined root from all shard roots.
///
/// Routes through Commitment<ShardSetMarker> from the typed framework.
/// Returns the BLAKE3 form; dual-form via `compute_combined_root_dual`.
fn compute_combined_root(shards: &[MerkleQueue]) -> [u8; 32] {
    compute_combined_root_dual(shards).blake3
}

/// Dual-form (BLAKE3 + Poseidon2) combined-shard-root commitment.
pub fn compute_combined_root_dual(
    shards: &[MerkleQueue],
) -> crate::commitment::ShardSetCommitment {
    let mut canonical = Vec::with_capacity(shards.len() * 32);
    for shard in shards {
        canonical.extend_from_slice(&shard.root());
    }
    crate::commitment::Commitment::seal(&canonical[..])
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(content: &[u8], sender: [u8; 32], deposit: u64) -> QueueEntry {
        QueueEntry {
            content_hash: *blake3::hash(content).as_bytes(),
            sender,
            deposit,
            enqueued_at: 100,
            size: content.len(),
        }
    }

    #[test]
    fn messages_route_to_correct_shard_deterministic() {
        let sq = ShardedQueue::new(4, 10);

        let entry1 = make_entry(b"hello", [0xAA; 32], 100);
        let entry2 = make_entry(b"hello", [0xAA; 32], 100); // same content = same shard

        let shard1 = sq.shard_for(&entry1.content_hash);
        let shard2 = sq.shard_for(&entry2.content_hash);
        assert_eq!(shard1, shard2);

        // Different content -> possibly different shard (at least deterministic).
        let entry3 = make_entry(b"world", [0xBB; 32], 200);
        let shard3 = sq.shard_for(&entry3.content_hash);
        // shard3 might or might not equal shard1, but the mapping is deterministic.
        let shard3_again = sq.shard_for(&entry3.content_hash);
        assert_eq!(shard3, shard3_again);
    }

    #[test]
    fn enqueue_to_sharded_queue_dequeue_from_correct_shard() {
        let mut sq = ShardedQueue::new(4, 10);

        let entry = make_entry(b"target", [0xAA; 32], 100);
        let expected_shard = sq.shard_for(&entry.content_hash);

        sq.enqueue(entry.clone()).unwrap();

        // The message should be in the expected shard.
        assert_eq!(sq.shard_len(expected_shard), 1);
        assert_eq!(sq.total_len(), 1);

        // Dequeue from that shard.
        let (dequeued, _proof) = sq.dequeue_shard(expected_shard).unwrap();
        assert_eq!(dequeued.content_hash, entry.content_hash);
        assert_eq!(sq.total_len(), 0);
    }

    #[test]
    fn dequeue_any_round_robins_across_shards() {
        let mut sq = ShardedQueue::new(4, 10);

        // Enqueue messages that land in different shards.
        // We'll keep trying until we have messages in at least 2 shards.
        let mut entries = Vec::new();
        for i in 0u64..20 {
            let entry = make_entry(&i.to_le_bytes(), [0xAA; 32], 100);
            entries.push(entry);
        }

        for entry in &entries {
            sq.enqueue(entry.clone()).unwrap();
        }

        // Track which shards we dequeue from.
        let mut dequeued_shards = Vec::new();
        let total = sq.total_len();
        for _ in 0..total {
            let (_, _, shard) = sq.dequeue_any().unwrap();
            dequeued_shards.push(shard);
        }

        // We should have dequeued from multiple shards (given enough messages).
        let unique_shards: std::collections::HashSet<_> = dequeued_shards.iter().collect();
        assert!(unique_shards.len() > 1, "Expected messages in multiple shards");

        // Queue should be empty now.
        assert!(sq.is_empty());
    }

    #[test]
    fn combined_root_changes_on_any_shard_mutation() {
        let mut sq = ShardedQueue::new(4, 10);
        let root_empty = sq.combined_root();

        let entry = make_entry(b"first", [0xAA; 32], 100);
        sq.enqueue(entry).unwrap();
        let root_one = sq.combined_root();
        assert_ne!(root_empty, root_one);

        let entry2 = make_entry(b"second", [0xBB; 32], 200);
        sq.enqueue(entry2).unwrap();
        let root_two = sq.combined_root();
        assert_ne!(root_one, root_two);

        // Dequeue changes root too.
        sq.dequeue_any().unwrap();
        let root_after_dequeue = sq.combined_root();
        assert_ne!(root_two, root_after_dequeue);
    }

    #[test]
    fn rebalance_moves_messages_from_overloaded_shards() {
        let mut sq = ShardedQueue::new(4, 100);

        // Enqueue many messages. Due to hash distribution, some shards will have more.
        for i in 0u64..40 {
            let entry = make_entry(&i.to_le_bytes(), [0xAA; 32], 100);
            sq.enqueue(entry).unwrap();
        }

        // Check distribution before rebalance.
        let mut shard_lens_before: Vec<usize> = (0..4).map(|i| sq.shard_len(i)).collect();
        shard_lens_before.sort();

        let moved = sq.rebalance();

        // If the distribution was uneven, some messages should have been moved.
        // The total should remain the same.
        assert_eq!(sq.total_len(), 40);

        // After rebalance, distribution should be more even (max - min <= 2).
        let mut shard_lens_after: Vec<usize> = (0..4).map(|i| sq.shard_len(i)).collect();
        shard_lens_after.sort();
        let spread = shard_lens_after.last().unwrap() - shard_lens_after.first().unwrap();
        // After rebalance, spread should be at most 2 (target +/- 1).
        assert!(spread <= 2, "Spread after rebalance: {spread}, lens: {shard_lens_after:?}");

        // If original distribution was uneven, moved > 0.
        let original_spread =
            shard_lens_before.last().unwrap() - shard_lens_before.first().unwrap();
        if original_spread > 2 {
            assert!(moved > 0);
        }
    }

    #[test]
    fn empty_sharded_queue_dequeue_returns_error() {
        let mut sq = ShardedQueue::new(4, 10);
        let result = sq.dequeue_any();
        assert_eq!(result, Err(QueueError::Empty));

        let result = sq.dequeue_shard(0);
        assert_eq!(result, Err(QueueError::Empty));
    }
}
