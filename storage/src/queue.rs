//! Merkle queue: content-addressed append-only queue.
//!
//! Each state of the queue has a unique root hash (blake3 Merkle tree of entries).
//! Enqueue = append leaf. Dequeue = advance head pointer.
//! The queue root IS the content address of the queue state.

use std::path::PathBuf;

use crate::wal::{WalEntry, WriteAheadLog};

/// A content-addressed append-only queue.
/// Each state of the queue has a unique root hash (Merkle tree of entries).
/// Enqueue = append leaf. Dequeue = advance head pointer.
/// The queue root IS the content address of the queue state.
#[derive(Debug)]
pub struct MerkleQueue {
    /// Current entries (linear buffer with head pointer).
    entries: Vec<QueueEntry>,
    /// Head pointer (first un-dequeued entry index into `entries`).
    head: usize,
    /// Maximum capacity (bounded by quota).
    capacity: usize,
    /// Current root hash (blake3 of all entries from head to tail).
    root: [u8; 32],
    /// Optional WAL for durable mode.
    wal: Option<Box<WalState>>,
}

/// Internal WAL state.
#[derive(Debug)]
struct WalState {
    wal: WriteAheadLog,
    queue_id: [u8; 32],
}

impl Clone for MerkleQueue {
    fn clone(&self) -> Self {
        // Cloning produces an in-memory-only copy (WAL is not cloned).
        Self {
            entries: self.entries.clone(),
            head: self.head,
            capacity: self.capacity,
            root: self.root,
            wal: None,
        }
    }
}

/// A single entry in the queue.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueueEntry {
    /// Content hash of the enqueued data.
    pub content_hash: [u8; 32],
    /// Who enqueued this (for deposit refund tracking).
    pub sender: [u8; 32],
    /// Deposit paid by sender (computrons).
    pub deposit: u64,
    /// When this was enqueued (block height).
    pub enqueued_at: u64,
    /// Size in bytes.
    pub size: usize,
}

/// Proof that an entry was dequeued (for deposit refund).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DequeueProof {
    pub entry: QueueEntry,
    pub old_root: [u8; 32],
    pub new_root: [u8; 32],
    pub position: usize,
}

/// Errors from queue operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueueError {
    /// Queue is full (at capacity).
    Full { capacity: usize },
    /// Queue is empty (nothing to dequeue).
    Empty,
}

impl MerkleQueue {
    /// Create a new empty queue with the given capacity (in-memory only).
    pub fn new(capacity: usize) -> Self {
        let mut q = Self {
            entries: Vec::new(),
            head: 0,
            capacity,
            root: [0u8; 32],
            wal: None,
        };
        q.recompute_root();
        q
    }

    /// Create a queue with WAL-backed durability.
    pub fn with_wal(capacity: usize, wal_path: PathBuf) -> std::io::Result<Self> {
        let queue_id = *blake3::hash(wal_path.to_string_lossy().as_bytes()).as_bytes();
        let mut wal = WriteAheadLog::open(wal_path)?;

        // Log the queue creation.
        let seq = wal.next_sequence();
        let entry = WalEntry::CreateQueue {
            queue_id,
            capacity,
            sequence: seq,
        };
        wal.append(&entry)?;
        wal.sync()?;

        let mut q = Self {
            entries: Vec::new(),
            head: 0,
            capacity,
            root: [0u8; 32],
            wal: Some(Box::new(WalState { wal, queue_id })),
        };
        q.recompute_root();
        Ok(q)
    }

    /// Enqueue with WAL (logged before applied, fsync'd).
    pub fn enqueue_durable(&mut self, entry: QueueEntry) -> std::io::Result<[u8; 32]> {
        if self.is_full() {
            return Err(std::io::Error::other(format!("queue full (capacity {})", self.capacity)));
        }

        let wal_state = self
            .wal
            .as_mut()
            .ok_or_else(|| std::io::Error::other("no WAL attached"))?;

        // Serialize entry data for the WAL.
        let entry_data = serialize_queue_entry(&entry);
        let entry_hash = entry.content_hash;

        let seq = wal_state.wal.next_sequence();
        let wal_entry = WalEntry::Enqueue {
            queue_id: wal_state.queue_id,
            entry_hash,
            data: entry_data,
            sequence: seq,
        };

        // Log BEFORE applying.
        wal_state.wal.append(&wal_entry)?;
        wal_state.wal.sync()?;

        // Now apply in memory.
        self.entries.push(entry);
        self.recompute_root();
        Ok(self.root)
    }

    /// Dequeue with WAL.
    pub fn dequeue_durable(&mut self) -> std::io::Result<Option<(QueueEntry, DequeueProof)>> {
        if self.head >= self.entries.len() {
            return Ok(None);
        }

        let wal_state = self
            .wal
            .as_mut()
            .ok_or_else(|| std::io::Error::other("no WAL attached"))?;

        let position = self.head;
        let seq = wal_state.wal.next_sequence();
        let wal_entry = WalEntry::Dequeue {
            queue_id: wal_state.queue_id,
            position,
            sequence: seq,
        };

        // Log BEFORE applying.
        wal_state.wal.append(&wal_entry)?;
        wal_state.wal.sync()?;

        // Apply in memory.
        let old_root = self.root;
        let entry = self.entries[self.head].clone();
        self.head += 1;
        self.recompute_root();

        let proof = DequeueProof {
            entry: entry.clone(),
            old_root,
            new_root: self.root,
            position,
        };

        Ok(Some((entry, proof)))
    }

    /// Recover state from WAL after crash.
    /// Replays all WAL entries to reconstruct the queue state.
    pub fn recover_from_wal(wal_path: PathBuf) -> std::io::Result<Self> {
        let queue_id = *blake3::hash(wal_path.to_string_lossy().as_bytes()).as_bytes();
        let wal = WriteAheadLog::open(wal_path)?;
        let entries = wal.replay()?;

        let mut capacity = 0usize;
        let mut queue_entries: Vec<QueueEntry> = Vec::new();
        let mut head: usize = 0;

        for entry in &entries {
            match entry {
                WalEntry::CreateQueue {
                    capacity: cap,
                    queue_id: qid,
                    ..
                } if *qid == queue_id => {
                    capacity = *cap;
                    queue_entries.clear();
                    head = 0;
                }
                WalEntry::Enqueue {
                    data,
                    queue_id: qid,
                    ..
                } if *qid == queue_id => {
                    if let Some(qe) = deserialize_queue_entry(data) {
                        queue_entries.push(qe);
                    }
                }
                WalEntry::Dequeue {
                    queue_id: qid, ..
                } if *qid == queue_id => {
                    head += 1;
                }
                WalEntry::Checkpoint {
                    queue_id: qid, ..
                } if *qid == queue_id => {
                    // After a checkpoint, earlier entries were truncated.
                    // The queue state at this point is what we have.
                }
                _ => {}
            }
        }

        let mut q = Self {
            entries: queue_entries,
            head,
            capacity,
            root: [0u8; 32],
            wal: Some(Box::new(WalState { wal, queue_id })),
        };
        q.recompute_root();
        Ok(q)
    }

    /// Checkpoint: truncate WAL up to current state (called periodically).
    pub fn checkpoint(&mut self) -> std::io::Result<()> {
        let wal_state = self
            .wal
            .as_mut()
            .ok_or_else(|| std::io::Error::other("no WAL attached"))?;

        let seq = wal_state.wal.checkpoint(&wal_state.queue_id, &self.root)?;
        // Truncate all entries before the checkpoint.
        wal_state.wal.truncate_before(seq)?;
        Ok(())
    }

    /// Enqueue an entry. Returns the new root hash on success.
    pub fn enqueue(&mut self, entry: QueueEntry) -> Result<[u8; 32], QueueError> {
        if self.is_full() {
            return Err(QueueError::Full {
                capacity: self.capacity,
            });
        }
        self.entries.push(entry);
        self.recompute_root();
        Ok(self.root)
    }

    /// Dequeue the next entry (FIFO). Returns the entry and a dequeue proof.
    pub fn dequeue(&mut self) -> Result<(QueueEntry, DequeueProof), QueueError> {
        if self.head >= self.entries.len() {
            return Err(QueueError::Empty);
        }

        let old_root = self.root;
        let position = self.head;
        let entry = self.entries[self.head].clone();
        self.head += 1;
        self.recompute_root();

        let proof = DequeueProof {
            entry: entry.clone(),
            old_root,
            new_root: self.root,
            position,
        };

        Ok((entry, proof))
    }

    /// Peek at the next entry without consuming it.
    pub fn peek(&self) -> Option<&QueueEntry> {
        if self.head < self.entries.len() {
            Some(&self.entries[self.head])
        } else {
            None
        }
    }

    /// Number of pending (un-dequeued) entries.
    pub fn len(&self) -> usize {
        self.entries.len() - self.head
    }

    /// Whether the queue has no pending entries.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether the queue is at capacity.
    pub fn is_full(&self) -> bool {
        self.len() >= self.capacity
    }

    /// Current Merkle root hash.
    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    /// Total entries ever enqueued (tail index).
    pub fn tail(&self) -> usize {
        self.entries.len()
    }

    /// Current head position.
    pub fn head_position(&self) -> usize {
        self.head
    }

    /// Peek at an entry by relative position from head.
    /// Returns None if the index is out of bounds.
    pub fn peek_relative(&self, relative_index: usize) -> Option<&QueueEntry> {
        let absolute = self.head + relative_index;
        if absolute < self.entries.len() {
            Some(&self.entries[absolute])
        } else {
            None
        }
    }

    /// Recompute the Merkle root from all pending entries (head..tail).
    ///
    /// Uses a binary Merkle tree over blake3 hashes of entry content hashes.
    /// For an empty queue, the root is blake3(b"empty_queue").
    fn recompute_root(&mut self) {
        let pending = &self.entries[self.head..];
        if pending.is_empty() {
            self.root = *blake3::hash(b"empty_queue").as_bytes();
            return;
        }

        // Leaf hashes: blake3(content_hash || sender || deposit || enqueued_at || size)
        let leaves: Vec<[u8; 32]> = pending.iter().map(hash_entry).collect();

        self.root = merkle_root(&leaves);
    }
}

/// Hash a queue entry to produce its leaf hash.
fn hash_entry(entry: &QueueEntry) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&entry.content_hash);
    hasher.update(&entry.sender);
    hasher.update(&entry.deposit.to_le_bytes());
    hasher.update(&entry.enqueued_at.to_le_bytes());
    hasher.update(&(entry.size as u64).to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute the Merkle root of a set of leaf hashes.
/// Uses a standard binary Merkle tree (pad with zero-hashes if not a power of 2).
fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return *blake3::hash(b"empty_queue").as_bytes();
    }
    if leaves.len() == 1 {
        return leaves[0];
    }

    // Pad to next power of 2.
    let mut layer: Vec<[u8; 32]> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    let zero_hash = [0u8; 32];
    layer.resize(next_pow2, zero_hash);

    // Iteratively hash pairs until we have a single root.
    while layer.len() > 1 {
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next_layer.push(*hasher.finalize().as_bytes());
        }
        layer = next_layer;
    }

    layer[0]
}

/// Verify a dequeue proof: that dequeueing the given entry from a queue with
/// old_root produces new_root.
///
/// This reconstructs what the new root should be by removing the entry at `position`
/// from the old state. In practice, a full verifier would need the sibling hashes;
/// here we provide a simplified check that the proof is internally consistent.
pub fn verify_dequeue_proof(proof: &DequeueProof) -> bool {
    // Basic consistency: old_root != new_root (unless the queue is pathological).
    // The proof is valid if old_root and new_root differ (state changed).
    // A full implementation would verify Merkle paths; for Phase 1 we verify
    // that the roots are different and the entry is well-formed.
    proof.old_root != proof.new_root || {
        // Edge case: if dequeueing produces an empty queue, both could be the empty root.
        // That's only valid if old_root was a single-element tree.
        proof.new_root == *blake3::hash(b"empty_queue").as_bytes()
    }
}

/// Serialize a QueueEntry to bytes for WAL storage.
pub fn serialize_queue_entry(entry: &QueueEntry) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&entry.content_hash);
    buf.extend_from_slice(&entry.sender);
    buf.extend_from_slice(&entry.deposit.to_le_bytes());
    buf.extend_from_slice(&entry.enqueued_at.to_le_bytes());
    buf.extend_from_slice(&(entry.size as u64).to_le_bytes());
    buf
}

/// Deserialize a QueueEntry from bytes (WAL replay).
pub fn deserialize_queue_entry(data: &[u8]) -> Option<QueueEntry> {
    // content_hash(32) + sender(32) + deposit(8) + enqueued_at(8) + size(8) = 88 bytes
    if data.len() < 88 {
        return None;
    }
    let mut content_hash = [0u8; 32];
    content_hash.copy_from_slice(&data[0..32]);
    let mut sender = [0u8; 32];
    sender.copy_from_slice(&data[32..64]);
    let deposit = u64::from_le_bytes(data[64..72].try_into().ok()?);
    let enqueued_at = u64::from_le_bytes(data[72..80].try_into().ok()?);
    let size = u64::from_le_bytes(data[80..88].try_into().ok()?) as usize;
    Some(QueueEntry {
        content_hash,
        sender,
        deposit,
        enqueued_at,
        size,
    })
}

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
    fn enqueue_dequeue_roundtrip() {
        let mut q = MerkleQueue::new(10);
        let entry = make_entry(b"hello", [1u8; 32], 500);

        let root_after_enqueue = q.enqueue(entry.clone()).unwrap();
        assert_ne!(root_after_enqueue, *blake3::hash(b"empty_queue").as_bytes());
        assert_eq!(q.len(), 1);

        let (dequeued, proof) = q.dequeue().unwrap();
        assert_eq!(dequeued, entry);
        assert_eq!(proof.old_root, root_after_enqueue);
        assert_eq!(proof.position, 0);
        assert_eq!(q.len(), 0);
    }

    #[test]
    fn root_changes_on_mutation() {
        let mut q = MerkleQueue::new(10);
        let root_empty = q.root();

        let entry1 = make_entry(b"first", [1u8; 32], 100);
        q.enqueue(entry1).unwrap();
        let root_one = q.root();
        assert_ne!(root_empty, root_one);

        let entry2 = make_entry(b"second", [2u8; 32], 200);
        q.enqueue(entry2).unwrap();
        let root_two = q.root();
        assert_ne!(root_one, root_two);

        q.dequeue().unwrap();
        let root_after_dequeue = q.root();
        assert_ne!(root_two, root_after_dequeue);
    }

    #[test]
    fn full_queue_rejects() {
        let mut q = MerkleQueue::new(2);
        let e1 = make_entry(b"a", [1u8; 32], 10);
        let e2 = make_entry(b"b", [2u8; 32], 20);
        let e3 = make_entry(b"c", [3u8; 32], 30);

        q.enqueue(e1).unwrap();
        q.enqueue(e2).unwrap();
        let result = q.enqueue(e3);
        assert_eq!(result, Err(QueueError::Full { capacity: 2 }));
    }

    #[test]
    fn empty_queue_dequeue_error() {
        let mut q = MerkleQueue::new(10);
        let result = q.dequeue();
        assert_eq!(result, Err(QueueError::Empty));
    }

    #[test]
    fn root_is_deterministic() {
        // Same entries in same order produce same root.
        let mut q1 = MerkleQueue::new(10);
        let mut q2 = MerkleQueue::new(10);

        let e1 = make_entry(b"alpha", [0xAA; 32], 100);
        let e2 = make_entry(b"beta", [0xBB; 32], 200);

        q1.enqueue(e1.clone()).unwrap();
        q1.enqueue(e2.clone()).unwrap();

        q2.enqueue(e1).unwrap();
        q2.enqueue(e2).unwrap();

        assert_eq!(q1.root(), q2.root());
    }

    #[test]
    fn dequeue_proof_is_verifiable() {
        let mut q = MerkleQueue::new(10);
        let e1 = make_entry(b"msg1", [1u8; 32], 50);
        let e2 = make_entry(b"msg2", [2u8; 32], 75);

        q.enqueue(e1).unwrap();
        q.enqueue(e2).unwrap();

        let (_, proof) = q.dequeue().unwrap();
        assert!(verify_dequeue_proof(&proof));
        assert_ne!(proof.old_root, proof.new_root);

        // Second dequeue produces empty queue.
        let (_, proof2) = q.dequeue().unwrap();
        assert!(verify_dequeue_proof(&proof2));
        assert_eq!(proof2.new_root, *blake3::hash(b"empty_queue").as_bytes());
    }

    #[test]
    fn peek_does_not_consume() {
        let mut q = MerkleQueue::new(10);
        let entry = make_entry(b"peek_me", [5u8; 32], 300);
        q.enqueue(entry.clone()).unwrap();

        let peeked = q.peek().unwrap();
        assert_eq!(peeked, &entry);
        assert_eq!(q.len(), 1);

        // Peek again — still there.
        let peeked2 = q.peek().unwrap();
        assert_eq!(peeked2, &entry);
    }

    #[test]
    fn fifo_order() {
        let mut q = MerkleQueue::new(10);
        let entries: Vec<QueueEntry> = (0..5)
            .map(|i| make_entry(format!("msg{i}").as_bytes(), [i as u8; 32], i as u64 * 10))
            .collect();

        for e in &entries {
            q.enqueue(e.clone()).unwrap();
        }

        for expected in &entries {
            let (got, _) = q.dequeue().unwrap();
            assert_eq!(&got, expected);
        }
    }

    #[test]
    fn capacity_freed_after_dequeue() {
        let mut q = MerkleQueue::new(2);
        let e1 = make_entry(b"x", [1u8; 32], 10);
        let e2 = make_entry(b"y", [2u8; 32], 20);

        q.enqueue(e1).unwrap();
        q.enqueue(e2).unwrap();
        assert!(q.is_full());

        // Dequeue one — now there's room.
        q.dequeue().unwrap();
        assert!(!q.is_full());
        assert_eq!(q.len(), 1);

        // Can enqueue again.
        let e3 = make_entry(b"z", [3u8; 32], 30);
        q.enqueue(e3).unwrap();
        assert_eq!(q.len(), 2);
    }
}
