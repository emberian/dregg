//! Append-only Merkle-committed audit log.
//!
//! The `AuditLog` maintains a sequence of `UsageEvent`s committed into a
//! 4-ary Merkle tree. Events are appended in order and cannot be removed.
//! The log supports generating various proofs about its contents without
//! revealing the full event history.

use std::collections::HashMap;

use pyana_commit::hash::{HASH_ARITY, empty_hash_at_depth, hash_leaf, hash_node};
use serde::{Deserialize, Serialize};

use crate::event::{AuditReceipt, InclusionProof, UsageEvent};
use crate::proofs::{ConsistencyProof, CountProof, LastUseProof, RangeProof};

/// The depth of the audit Merkle tree.
/// 4^12 = ~16 million events capacity, sufficient for demo purposes.
const TREE_DEPTH: usize = 12;

/// Default maximum number of historical roots to retain.
/// Older roots beyond this limit are pruned on each append.
/// This prevents unbounded memory growth in long-running systems.
pub const DEFAULT_HISTORICAL_ROOTS_LIMIT: usize = 10_000;

/// An append-only audit log backed by a 4-ary Merkle tree.
///
/// Each event is hashed and inserted as a leaf. The tree is addressed by
/// a position-based key (the event's global index mapped to tree coordinates),
/// ensuring that the append-only property is structurally enforced.
///
/// Interior Merkle nodes are cached in `tree_levels` so that append only
/// recomputes the O(log₄ N) path from the new leaf to the root, rather than
/// rebuilding the entire tree.
#[derive(Clone, Debug)]
pub struct AuditLog {
    /// The ordered sequence of events.
    events: Vec<UsageEvent>,
    /// Map from event hash to global index for quick lookup.
    event_index: HashMap<[u8; 32], Vec<u64>>,
    /// Map from token_id to list of global indices of that token's events.
    token_events: HashMap<[u8; 32], Vec<u64>>,
    /// Cached Merkle tree nodes by level.
    /// `tree_levels[0]` = leaf hashes (depth == TREE_DEPTH in the tree).
    /// `tree_levels[k]` = nodes at level k (depth == TREE_DEPTH - k).
    /// `tree_levels[TREE_DEPTH]` = single root node.
    ///
    /// Each level is indexed by position: the node at `tree_levels[level][i]`
    /// is the parent of children `tree_levels[level-1][i*4 .. i*4+3]`.
    tree_levels: Vec<Vec<[u8; 32]>>,
    /// Historical roots: root after each append, for consistency proofs.
    /// Pruned to at most `historical_roots_limit` entries (oldest are dropped).
    historical_roots: Vec<[u8; 32]>,
    /// The global index offset of the first entry in `historical_roots`.
    /// When roots are pruned, this advances so that `historical_root(size)`
    /// can still map correctly.
    historical_roots_offset: usize,
    /// Maximum number of historical roots to retain. Configurable.
    historical_roots_limit: usize,
}

/// Snapshot of the log state at a point in time, for consistency proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LogSnapshot {
    /// The root hash at this point.
    pub root: [u8; 32],
    /// The number of events at this point.
    pub size: u64,
}

impl AuditLog {
    /// Create a new empty audit log with the default historical roots retention limit.
    pub fn new() -> Self {
        Self::with_roots_limit(DEFAULT_HISTORICAL_ROOTS_LIMIT)
    }

    /// Create a new empty audit log with a custom historical roots retention limit.
    ///
    /// The limit controls how many historical roots are kept in memory. Once the
    /// limit is exceeded, the oldest roots are pruned. A limit of 0 means no
    /// historical roots are retained (consistency proofs will be unavailable for
    /// old snapshots).
    pub fn with_roots_limit(limit: usize) -> Self {
        // Initialize tree_levels with TREE_DEPTH + 1 empty levels.
        // Level 0 = leaves, level TREE_DEPTH = root.
        let mut tree_levels = Vec::with_capacity(TREE_DEPTH + 1);
        for _ in 0..=TREE_DEPTH {
            tree_levels.push(Vec::new());
        }
        Self {
            events: Vec::new(),
            event_index: HashMap::new(),
            token_events: HashMap::new(),
            tree_levels,
            historical_roots: Vec::new(),
            historical_roots_offset: 0,
            historical_roots_limit: limit,
        }
    }

    /// Number of events in the log.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Get the current root hash of the log. O(1) — returns the cached root.
    pub fn root(&mut self) -> [u8; 32] {
        self.cached_root()
    }

    /// Get the root hash without mutating. O(1).
    pub fn root_cached(&self) -> Option<[u8; 32]> {
        Some(self.cached_root())
    }

    /// Return the cached root. For an empty tree, this is the canonical empty root.
    fn cached_root(&self) -> [u8; 32] {
        if self.events.is_empty() {
            return empty_hash_at_depth(TREE_DEPTH);
        }
        // The root is always at tree_levels[TREE_DEPTH][0], maintained incrementally.
        self.tree_levels[TREE_DEPTH][0]
    }

    /// Get a snapshot of the current log state.
    pub fn snapshot(&mut self) -> LogSnapshot {
        let root = self.root();
        LogSnapshot {
            root,
            size: self.events.len() as u64,
        }
    }

    /// Append an event to the log, returning a receipt.
    ///
    /// The receipt contains the event hash, the new log root, and an
    /// inclusion proof that the event is in the log.
    ///
    /// Complexity: O(log₄ N) — only the path from the new leaf to root is
    /// recomputed, using the cached interior nodes.
    pub fn append(&mut self, event: UsageEvent) -> AuditReceipt {
        let event_hash = event.hash();
        let global_index = self.events.len() as u64;

        // Update indices.
        self.event_index
            .entry(event_hash)
            .or_default()
            .push(global_index);
        self.token_events
            .entry(event.token_id)
            .or_default()
            .push(global_index);

        // Insert leaf hash into level 0.
        let leaf_hash = hash_leaf(&event.to_bytes());
        let leaf_idx = self.events.len(); // index of the new leaf
        self.tree_levels[0].push(leaf_hash);
        self.events.push(event);

        // Update the path from this leaf to root (O(TREE_DEPTH) = O(log₄ N)).
        let mut idx = leaf_idx;
        for level in 0..TREE_DEPTH {
            let parent_idx = idx / HASH_ARITY;
            let sibling_base = parent_idx * HASH_ARITY;

            // Compute parent hash from its 4 children at the current level.
            let mut children = [[0u8; 32]; 4];
            for i in 0..HASH_ARITY {
                let child_idx = sibling_base + i;
                if child_idx < self.tree_levels[level].len() {
                    children[i] = self.tree_levels[level][child_idx];
                } else {
                    // Empty subtree at the appropriate depth.
                    // Level 0 children are leaves (depth 0 empty), level k children
                    // have empty hash at depth k.
                    children[i] = empty_hash_at_depth(level);
                }
            }
            let parent_hash = hash_node(&children);

            // Update or extend the parent level.
            let next_level = level + 1;
            if parent_idx < self.tree_levels[next_level].len() {
                self.tree_levels[next_level][parent_idx] = parent_hash;
            } else {
                // Should only extend by exactly one in normal append order.
                debug_assert_eq!(parent_idx, self.tree_levels[next_level].len());
                self.tree_levels[next_level].push(parent_hash);
            }

            idx = parent_idx;
        }

        // Root is now at tree_levels[TREE_DEPTH][0].
        let new_root = self.tree_levels[TREE_DEPTH][0];
        self.historical_roots.push(new_root);

        // Prune historical roots if they exceed the retention limit.
        if self.historical_roots_limit > 0
            && self.historical_roots.len() > self.historical_roots_limit
        {
            let excess = self.historical_roots.len() - self.historical_roots_limit;
            self.historical_roots.drain(..excess);
            self.historical_roots_offset += excess;
        }

        // Generate inclusion proof.
        let inclusion_proof = self.prove_inclusion_at(global_index);

        AuditReceipt {
            event_hash,
            log_root_after: new_root,
            inclusion_proof,
            global_index,
        }
    }

    /// Generate an inclusion proof for an event at a given global index.
    pub fn prove_inclusion(&mut self, global_index: u64) -> Option<InclusionProof> {
        if global_index >= self.events.len() as u64 {
            return None;
        }
        Some(self.prove_inclusion_at(global_index))
    }

    /// Prove how many times a token was used (count proof).
    ///
    /// Returns a `CountProof` that proves the token was used exactly K times
    /// without revealing which events those were or what actions were taken.
    pub fn prove_count(&mut self, token_id: &[u8; 32]) -> CountProof {
        let indices = self.token_events.get(token_id).cloned().unwrap_or_default();
        let count = indices.len() as u64;
        let root = self.root();

        // Collect inclusion proofs for each event belonging to this token.
        let event_proofs: Vec<(u64, [u8; 32], InclusionProof)> = indices
            .iter()
            .map(|&idx| {
                let leaf_hash = self.tree_levels[0][idx as usize];
                let proof = self.prove_inclusion_at(idx);
                (idx, leaf_hash, proof)
            })
            .collect();

        // Compute a commitment to the set of indices (hides them from the auditor
        // unless they need to verify).
        let index_commitment = self.commit_indices(&indices);

        CountProof {
            token_id: *token_id,
            count,
            log_root: root,
            log_size: self.events.len() as u64,
            index_commitment,
            event_proofs,
        }
    }

    /// Prove that all uses of a token are within a given time range.
    ///
    /// Returns a `RangeProof` that proves every event for this token has
    /// a timestamp within [start, end].
    pub fn prove_range(&mut self, token_id: &[u8; 32], start: i64, end: i64) -> RangeProof {
        let indices = self.token_events.get(token_id).cloned().unwrap_or_default();
        let root = self.root();

        // Collect the timestamps and proofs.
        let timestamp_proofs: Vec<TimestampWitness> = indices
            .iter()
            .map(|&idx| {
                let event = &self.events[idx as usize];
                let proof = self.prove_inclusion_at(idx);
                TimestampWitness {
                    global_index: idx,
                    timestamp: event.timestamp,
                    event_hash: event.hash(),
                    leaf_hash: self.tree_levels[0][idx as usize],
                    inclusion_proof: proof,
                }
            })
            .collect();

        RangeProof {
            token_id: *token_id,
            range_start: start,
            range_end: end,
            log_root: root,
            log_size: self.events.len() as u64,
            timestamp_witnesses: timestamp_proofs,
        }
    }

    /// Prove that the last use of a token occurred at a specific time/sequence.
    pub fn prove_last_use(&mut self, token_id: &[u8; 32]) -> Option<LastUseProof> {
        let indices = self.token_events.get(token_id)?;
        let last_idx = *indices.last()?;
        let last_sequence = self.events[last_idx as usize].sequence;
        let last_timestamp = self.events[last_idx as usize].timestamp;
        let event_hash = self.events[last_idx as usize].hash();
        let leaf_hash = self.tree_levels[0][last_idx as usize];
        let root = self.root();
        let proof = self.prove_inclusion_at(last_idx);

        Some(LastUseProof {
            token_id: *token_id,
            last_sequence,
            last_timestamp,
            event_hash,
            leaf_hash,
            log_root: root,
            log_size: self.events.len() as u64,
            inclusion_proof: proof,
        })
    }

    /// Prove that the log is append-only: a previous snapshot is consistent
    /// with the current state (the old tree is a prefix of the new tree).
    pub fn prove_consistency(&mut self, old_snapshot: &LogSnapshot) -> Option<ConsistencyProof> {
        let old_size = old_snapshot.size as usize;
        if old_size > self.events.len() {
            return None;
        }

        let current_root = self.root();

        // Reconstruct the old root from the first `old_size` leaves.
        let old_root_recomputed = self.compute_root_for_prefix(old_size);
        if old_root_recomputed != old_snapshot.root {
            return None; // The snapshot doesn't match our history.
        }

        // Generate proof: show that the old leaves are a prefix of the current leaves.
        // We provide the "bridge" hashes: subtree hashes in the current tree that,
        // together with the old tree's leaves, reconstruct the old root.
        let bridge_hashes = self.compute_bridge_hashes(old_size);

        Some(ConsistencyProof {
            old_root: old_snapshot.root,
            old_size: old_snapshot.size,
            new_root: current_root,
            new_size: self.events.len() as u64,
            bridge_hashes,
        })
    }

    /// Get an event by its global index.
    pub fn get_event(&self, global_index: u64) -> Option<&UsageEvent> {
        self.events.get(global_index as usize)
    }

    /// Get all event indices for a token.
    pub fn token_event_indices(&self, token_id: &[u8; 32]) -> &[u64] {
        self.token_events
            .get(token_id)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Get the count of events for a specific token.
    pub fn token_use_count(&self, token_id: &[u8; 32]) -> u64 {
        self.token_events
            .get(token_id)
            .map(|v| v.len() as u64)
            .unwrap_or(0)
    }

    /// Get the historical root at a given size.
    ///
    /// Returns `None` if the requested root has been pruned (older than the
    /// retention limit) or is beyond the current log size.
    pub fn historical_root(&self, size: usize) -> Option<[u8; 32]> {
        if size == 0 {
            return Some(empty_hash_at_depth(TREE_DEPTH));
        }
        // Convert 1-based size to 0-based index, then adjust for the offset.
        let absolute_idx = size - 1;
        if absolute_idx < self.historical_roots_offset {
            // This root has been pruned.
            return None;
        }
        let local_idx = absolute_idx - self.historical_roots_offset;
        self.historical_roots.get(local_idx).copied()
    }

    /// Get the current historical roots retention limit.
    pub fn historical_roots_limit(&self) -> usize {
        self.historical_roots_limit
    }

    /// Set a new historical roots retention limit.
    ///
    /// If the new limit is smaller than the current number of retained roots,
    /// excess old roots are immediately pruned.
    pub fn set_historical_roots_limit(&mut self, limit: usize) {
        self.historical_roots_limit = limit;
        if limit > 0 && self.historical_roots.len() > limit {
            let excess = self.historical_roots.len() - limit;
            self.historical_roots.drain(..excess);
            self.historical_roots_offset += excess;
        }
    }

    // ─── Internal helpers ───────────────────────────────────────────────

    /// Access leaves (level 0 of the cached tree).
    fn leaves(&self) -> &[[u8; 32]] {
        &self.tree_levels[0]
    }

    /// Generate an inclusion proof for a leaf at position `index`.
    /// O(TREE_DEPTH) — reads siblings directly from the cached tree levels.
    fn prove_inclusion_at(&self, index: u64) -> InclusionProof {
        let leaf_hash = self.tree_levels[0][index as usize];
        let key = index as u32;
        let path_indices = Self::key_to_path_leaf_to_root(key);
        let siblings = self.compute_siblings_cached(key);

        InclusionProof {
            leaf_hash,
            path_indices,
            siblings,
        }
    }

    /// Compute the root of the tree from all current leaves (full recomputation).
    /// Used for validation in `rebuild_tree_and_verify`.
    #[cfg(test)]
    fn compute_root_from_scratch(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return empty_hash_at_depth(TREE_DEPTH);
        }
        Self::compute_subtree_hash_static(leaves, 0, 0, leaves.len())
    }

    /// Compute the root of the tree using only the first `prefix_len` leaves.
    fn compute_root_for_prefix(&self, prefix_len: usize) -> [u8; 32] {
        if prefix_len == 0 {
            return empty_hash_at_depth(TREE_DEPTH);
        }
        let leaves = self.leaves();
        Self::compute_subtree_hash_static(leaves, 0, 0, prefix_len)
    }

    /// Recursively compute the hash of a subtree (static, no cache mutation).
    /// `depth`: current depth (0 = root level).
    /// `prefix`: the position prefix (which subtree we're in).
    /// `leaf_count`: how many leaves to consider.
    fn compute_subtree_hash_static(
        leaves: &[[u8; 32]],
        depth: usize,
        prefix: u32,
        leaf_count: usize,
    ) -> [u8; 32] {
        if depth == TREE_DEPTH {
            // Leaf level.
            let idx = prefix as usize;
            if idx < leaf_count {
                return leaves[idx];
            }
            return empty_hash_at_depth(0);
        }

        let mut children = [[0u8; 32]; 4];
        let shift = (TREE_DEPTH - 1 - depth) * 2;

        for i in 0..HASH_ARITY {
            let child_prefix = prefix | ((i as u32) << shift);
            let subtree_start = child_prefix as usize;
            let subtree_size = 1usize << shift;
            let subtree_end = subtree_start + subtree_size;

            if subtree_start >= leaf_count {
                children[i] = empty_hash_at_depth(TREE_DEPTH - depth - 1);
            } else if subtree_end <= leaf_count {
                children[i] =
                    Self::compute_subtree_hash_static(leaves, depth + 1, child_prefix, leaf_count);
            } else {
                children[i] =
                    Self::compute_subtree_hash_static(leaves, depth + 1, child_prefix, leaf_count);
            }
        }

        hash_node(&children)
    }

    /// Compute siblings for a leaf at position `key` using cached tree levels.
    /// O(TREE_DEPTH) — reads directly from `tree_levels`.
    fn compute_siblings_cached(&self, key: u32) -> Vec<[[u8; 32]; 3]> {
        let mut siblings = Vec::with_capacity(TREE_DEPTH);

        // Walk from leaf (level 0) to just below root (level TREE_DEPTH - 1).
        // At each level, we need the 3 siblings of the node on the path.
        let mut node_idx = key as usize;
        for level in 0..TREE_DEPTH {
            let idx_in_parent = node_idx % HASH_ARITY; // which child (0..3) are we?
            let sibling_base = node_idx - idx_in_parent; // first child of the same parent

            let mut sibs = [[0u8; 32]; 3];
            let mut sib_pos = 0;
            for i in 0..HASH_ARITY {
                if i == idx_in_parent {
                    continue;
                }
                let sibling_idx = sibling_base + i;
                if sibling_idx < self.tree_levels[level].len() {
                    sibs[sib_pos] = self.tree_levels[level][sibling_idx];
                } else {
                    // This sibling doesn't exist yet — use the empty hash at this level's depth.
                    sibs[sib_pos] = empty_hash_at_depth(level);
                }
                sib_pos += 1;
            }
            siblings.push(sibs);

            // Move up to parent.
            node_idx /= HASH_ARITY;
        }

        siblings
    }

    /// Convert a position key to path indices in leaf-to-root order.
    fn key_to_path_leaf_to_root(key: u32) -> Vec<u8> {
        let mut path = Vec::with_capacity(TREE_DEPTH);
        for level in 0..TREE_DEPTH {
            let shift = level * 2;
            let idx = ((key >> shift) & 0x3) as u8;
            path.push(idx);
        }
        path
    }

    /// Compute a commitment to a set of indices (for CountProof).
    fn commit_indices(&self, indices: &[u64]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-audit index-commit v1");
        for &idx in indices {
            hasher.update(&idx.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// Compute bridge hashes for a consistency proof.
    ///
    /// These are the subtree hashes that, combined with the old prefix,
    /// allow reconstruction of the new root. They represent the "new" parts
    /// of the tree that were added after the old snapshot.
    fn compute_bridge_hashes(&self, old_size: usize) -> Vec<BridgeHash> {
        let current_size = self.leaves().len();
        if old_size == current_size {
            return Vec::new();
        }

        // Walk the tree and find subtrees that contain only new leaves.
        let leaves = self.leaves();
        Self::find_bridge_subtrees(leaves, 0, 0, old_size, current_size)
    }

    /// Recursively find subtrees that bridge old and new states.
    fn find_bridge_subtrees(
        leaves: &[[u8; 32]],
        depth: usize,
        prefix: u32,
        old_size: usize,
        new_size: usize,
    ) -> Vec<BridgeHash> {
        if depth == TREE_DEPTH {
            return Vec::new();
        }

        let mut bridges = Vec::new();
        let shift = (TREE_DEPTH - 1 - depth) * 2;

        for i in 0..HASH_ARITY {
            let child_prefix = prefix | ((i as u32) << shift);
            let subtree_start = child_prefix as usize;
            let subtree_size = 1usize << shift;
            let subtree_end = subtree_start + subtree_size;

            if subtree_end <= old_size {
                // Entirely in old tree — part of the prefix, not a bridge.
                continue;
            } else if subtree_start >= old_size && subtree_start < new_size {
                // Entirely new — this is a bridge hash.
                let hash =
                    Self::compute_subtree_hash_static(leaves, depth + 1, child_prefix, new_size);
                bridges.push(BridgeHash {
                    depth: depth + 1,
                    position: child_prefix,
                    hash,
                });
            } else if subtree_start < old_size && subtree_end > old_size {
                // Straddles old/new boundary — recurse.
                let sub =
                    Self::find_bridge_subtrees(leaves, depth + 1, child_prefix, old_size, new_size);
                bridges.extend(sub);
            }
        }

        bridges
    }

    /// Rebuild the entire tree from scratch and verify it matches the cached state.
    /// Useful for validation and testing.
    #[cfg(test)]
    fn rebuild_tree_and_verify(&self) {
        let leaves = self.leaves();
        let root_from_scratch = Self::compute_root_from_scratch(leaves);
        let cached_root = if self.events.is_empty() {
            empty_hash_at_depth(TREE_DEPTH)
        } else {
            self.tree_levels[TREE_DEPTH][0]
        };
        assert_eq!(
            root_from_scratch, cached_root,
            "Cached root does not match full recomputation"
        );
    }
}

impl Default for AuditLog {
    fn default() -> Self {
        Self::new()
    }
}

/// A witness to a timestamp for range proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimestampWitness {
    /// Global index of the event.
    pub global_index: u64,
    /// The timestamp of the event.
    pub timestamp: i64,
    /// Hash of the full event.
    pub event_hash: [u8; 32],
    /// The Merkle leaf hash.
    pub leaf_hash: [u8; 32],
    /// Proof that this leaf is in the log.
    pub inclusion_proof: InclusionProof,
}

/// A bridge hash for consistency proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BridgeHash {
    /// Depth of this subtree in the tree.
    pub depth: usize,
    /// Position prefix of this subtree.
    pub position: u32,
    /// Hash of the subtree.
    pub hash: [u8; 32],
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_event(token_id: [u8; 32], seq: u64, ts: i64) -> UsageEvent {
        UsageEvent::new(token_id, ts, [0xAA; 32], [0xBB; 32], seq)
    }

    #[test]
    fn empty_log() {
        let mut log = AuditLog::new();
        assert_eq!(log.len(), 0);
        assert!(log.is_empty());
        assert_eq!(log.root(), empty_hash_at_depth(TREE_DEPTH));
    }

    #[test]
    fn append_changes_root() {
        let mut log = AuditLog::new();
        let empty_root = log.root();
        let event = make_event([1u8; 32], 0, 1000);
        log.append(event);
        assert_ne!(log.root(), empty_root);
    }

    #[test]
    fn append_returns_valid_receipt() {
        let mut log = AuditLog::new();
        let event = make_event([1u8; 32], 0, 1000);
        let receipt = log.append(event.clone());

        assert_eq!(receipt.event_hash, event.hash());
        assert_eq!(receipt.log_root_after, log.root());
        assert_eq!(receipt.global_index, 0);
        assert!(receipt.inclusion_proof.verify(&receipt.log_root_after));
    }

    #[test]
    fn multiple_appends() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..10 {
            let event = make_event(token, i, 1000 + i as i64);
            let receipt = log.append(event);
            assert_eq!(receipt.global_index, i);
            assert!(receipt.inclusion_proof.verify(&receipt.log_root_after));
        }

        assert_eq!(log.len(), 10);
        assert_eq!(log.token_use_count(&token), 10);
    }

    #[test]
    fn inclusion_proof_valid_after_more_appends() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        // Append first event.
        let event0 = make_event(token, 0, 1000);
        let receipt0 = log.append(event0);

        // Append more events.
        for i in 1..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        // The original receipt's proof should still be valid against its recorded root
        // (not the current root — roots change as more events are added).
        assert!(receipt0.inclusion_proof.verify(&receipt0.log_root_after));

        // But it should NOT verify against the current (different) root.
        let current_root = log.root();
        assert_ne!(receipt0.log_root_after, current_root);
    }

    #[test]
    fn prove_inclusion_works() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        for i in 0..5 {
            log.append(make_event(token, i, 1000 + i as i64));
        }

        let root = log.root();
        for i in 0..5 {
            let proof = log.prove_inclusion(i).unwrap();
            assert!(proof.verify(&root));
        }

        // Out-of-bounds index.
        assert!(log.prove_inclusion(5).is_none());
    }

    #[test]
    fn historical_roots() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        let mut roots = Vec::new();
        for i in 0..5 {
            let receipt = log.append(make_event(token, i, 1000 + i as i64));
            roots.push(receipt.log_root_after);
        }

        for (i, expected_root) in roots.iter().enumerate() {
            assert_eq!(log.historical_root(i + 1), Some(*expected_root));
        }
    }

    #[test]
    fn cached_tree_matches_full_recomputation() {
        let mut log = AuditLog::new();
        let token = [1u8; 32];

        // Test at various sizes including boundary cases for 4-ary tree:
        // 1, 2, 3, 4 (fills first group), 5 (new group), 16, 17, 64, 100
        for i in 0..100u64 {
            log.append(make_event(token, i, 1000 + i as i64));
            // Verify at key sizes.
            if matches!(i, 0 | 1 | 2 | 3 | 4 | 15 | 16 | 63 | 64 | 99) {
                log.rebuild_tree_and_verify();
            }
        }
    }
}
