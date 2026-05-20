//! Causal DAG for tracking happened-before ordering between turns.
//!
//! The causal DAG ensures that turns are processed in a consistent order
//! across all peers, respecting causal dependencies (happened-before relations).
//! Each turn declares which previous turns it causally depends on (its "deps"),
//! forming a directed acyclic graph.
//!
//! This module layers domain-specific entry storage (`DagEntry`) on top of the
//! shared `pyana_types::CausalDag` graph structure.

use std::collections::{HashMap, HashSet};

// Re-export the shared CausalDag and CausalError from pyana-types.
pub use pyana_types::causal::hex_short;
pub use pyana_types::{CausalDag as DagGraph, CausalError};

/// A single entry in the causal DAG, representing one turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DagEntry {
    /// The blake3 hash identifying this turn.
    pub turn_hash: [u8; 32],
    /// The serialized turn data.
    pub turn_data: Vec<u8>,
    /// Hashes of turns this turn causally depends on (happened-before).
    pub deps: Vec<[u8; 32]>,
    /// Unix timestamp (milliseconds) when the turn was created.
    pub timestamp: i64,
    /// The public key (or hash thereof) of the node that produced this turn.
    pub node_id: [u8; 32],
}

/// The causal DAG tracks turns and their happened-before relationships.
///
/// Wraps the shared `pyana_types::CausalDag` graph with per-entry metadata
/// storage needed by the gossip network layer.
///
/// Invariants:
/// - Every entry's deps must be present in the DAG before (or at) insertion time.
/// - No duplicate hashes.
/// - The graph is always a DAG (no cycles).
#[derive(Debug, Clone)]
pub struct CausalDag {
    /// The underlying graph structure (shared with pyana-coord).
    graph: DagGraph,
    /// All turns indexed by their hash (entry metadata).
    turns: HashMap<[u8; 32], DagEntry>,
}

impl CausalDag {
    /// Create a new empty causal DAG.
    pub fn new() -> Self {
        Self {
            graph: DagGraph::new(),
            turns: HashMap::new(),
        }
    }

    /// Insert a new entry into the DAG.
    ///
    /// Fails if:
    /// - Any dependency is missing (use `missing_deps` to check first).
    /// - The turn hash is already present.
    pub fn insert(&mut self, entry: DagEntry) -> Result<(), CausalError> {
        self.graph.insert(entry.turn_hash, &entry.deps)?;
        self.turns.insert(entry.turn_hash, entry);
        Ok(())
    }

    /// Insert an entry, buffering it if deps are missing (returns list of missing deps).
    /// If all deps are present, inserts and returns Ok(None).
    /// If deps are missing, returns Ok(Some(missing_deps)) without inserting.
    pub fn try_insert(&mut self, entry: DagEntry) -> Result<Option<Vec<[u8; 32]>>, CausalError> {
        match self.graph.try_insert(entry.turn_hash, &entry.deps)? {
            None => {
                self.turns.insert(entry.turn_hash, entry);
                Ok(None)
            }
            Some(missing) => Ok(Some(missing)),
        }
    }

    /// Check whether an entry's causal dependencies are all present.
    pub fn is_causally_valid(&self, entry: &DagEntry) -> bool {
        self.graph.has_all_deps(&entry.deps)
    }

    /// Return the list of missing dependencies for an entry.
    pub fn missing_deps(&self, entry: &DagEntry) -> Vec<[u8; 32]> {
        self.graph.missing_deps(&entry.deps)
    }

    /// Return a topological ordering of all entries (respecting happened-before).
    pub fn causal_order(&self) -> Vec<&DagEntry> {
        self.graph
            .topological_order()
            .iter()
            .filter_map(|h| self.turns.get(h))
            .collect()
    }

    /// Get the frontier: entries with no dependents (the "latest" set).
    pub fn latest(&self) -> Vec<&DagEntry> {
        self.graph
            .frontier()
            .iter()
            .filter_map(|h| self.turns.get(h))
            .collect()
    }

    /// Compute a deterministic hash of the current frontier.
    /// This can be used to compare DAG states between peers.
    pub fn merge_frontier(&self) -> [u8; 32] {
        self.graph.merge_frontier()
    }

    /// Get a turn by its hash.
    pub fn get(&self, hash: &[u8; 32]) -> Option<&DagEntry> {
        self.turns.get(hash)
    }

    /// Check if the DAG contains a turn with the given hash.
    pub fn contains(&self, hash: &[u8; 32]) -> bool {
        self.graph.contains(hash)
    }

    /// Get the number of turns in the DAG.
    pub fn len(&self) -> usize {
        self.graph.len()
    }

    /// Check if the DAG is empty.
    pub fn is_empty(&self) -> bool {
        self.graph.is_empty()
    }

    /// Get all turns that transitively depend on the given turn (descendants).
    pub fn descendants(&self, hash: &[u8; 32]) -> HashSet<[u8; 32]> {
        self.graph.descendants(hash)
    }

    /// Get all turns that this turn transitively depends on (ancestors).
    pub fn ancestors(&self, hash: &[u8; 32]) -> HashSet<[u8; 32]> {
        self.graph.ancestors(hash)
    }

    /// Check if `ancestor` happened before `descendant`.
    pub fn happened_before(&self, ancestor: &[u8; 32], descendant: &[u8; 32]) -> bool {
        self.graph.happened_before(ancestor, descendant)
    }

    /// Check if two turns are concurrent (neither happened before the other).
    pub fn are_concurrent(&self, a: &[u8; 32], b: &[u8; 32]) -> bool {
        self.graph.are_concurrent(a, b)
    }

    /// Get the causal depth of a turn.
    pub fn depth(&self, hash: &[u8; 32]) -> Option<usize> {
        self.graph.depth(hash)
    }

    /// Access the underlying graph structure.
    pub fn graph(&self) -> &DagGraph {
        &self.graph
    }

    /// Verify that a turn's hash matches blake3(turn_data).
    pub fn verify_hash(entry: &DagEntry) -> Result<(), HashMismatch> {
        let computed = *blake3::hash(&entry.turn_data).as_bytes();
        if computed != entry.turn_hash {
            return Err(HashMismatch {
                claimed: entry.turn_hash,
                computed,
            });
        }
        Ok(())
    }
}

impl Default for CausalDag {
    fn default() -> Self {
        Self::new()
    }
}

/// Hash verification error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashMismatch {
    pub claimed: [u8; 32],
    pub computed: [u8; 32],
}

impl std::fmt::Display for HashMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "hash mismatch: claimed {} != computed {}",
            hex_short(&self.claimed),
            hex_short(&self.computed)
        )
    }
}

impl std::error::Error for HashMismatch {}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_turn(data: &[u8], deps: Vec<[u8; 32]>, node: u8) -> DagEntry {
        let turn_hash = *blake3::hash(data).as_bytes();
        DagEntry {
            turn_hash,
            turn_data: data.to_vec(),
            deps,
            timestamp: 1000,
            node_id: [node; 32],
        }
    }

    #[test]
    fn empty_dag() {
        let dag = CausalDag::new();
        assert!(dag.is_empty());
        assert_eq!(dag.len(), 0);
        assert!(dag.latest().is_empty());
        assert!(dag.causal_order().is_empty());
    }

    #[test]
    fn insert_genesis() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"turn-1", vec![], 1);
        dag.insert(t1.clone()).unwrap();

        assert_eq!(dag.len(), 1);
        assert!(dag.contains(&t1.turn_hash));
        assert_eq!(dag.latest().len(), 1);
        assert_eq!(dag.latest()[0].turn_hash, t1.turn_hash);
    }

    #[test]
    fn causal_chain() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"turn-1", vec![], 1);
        let t2 = make_turn(b"turn-2", vec![t1.turn_hash], 2);
        let t3 = make_turn(b"turn-3", vec![t2.turn_hash], 1);

        dag.insert(t1.clone()).unwrap();
        dag.insert(t2.clone()).unwrap();
        dag.insert(t3.clone()).unwrap();

        assert_eq!(dag.len(), 3);

        // Frontier should be just t3
        let frontier = dag.latest();
        assert_eq!(frontier.len(), 1);
        assert_eq!(frontier[0].turn_hash, t3.turn_hash);

        // Causal order should be t1 -> t2 -> t3
        let order = dag.causal_order();
        assert_eq!(order.len(), 3);
        assert_eq!(order[0].turn_hash, t1.turn_hash);
        assert_eq!(order[1].turn_hash, t2.turn_hash);
        assert_eq!(order[2].turn_hash, t3.turn_hash);
    }

    #[test]
    fn concurrent_turns_diamond() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"genesis", vec![], 1);
        // Two concurrent turns depending on genesis
        let t2a = make_turn(b"branch-a", vec![t1.turn_hash], 1);
        let t2b = make_turn(b"branch-b", vec![t1.turn_hash], 2);
        // Merge turn depending on both
        let t3 = make_turn(b"merge", vec![t2a.turn_hash, t2b.turn_hash], 1);

        dag.insert(t1.clone()).unwrap();
        dag.insert(t2a.clone()).unwrap();
        dag.insert(t2b.clone()).unwrap();
        dag.insert(t3.clone()).unwrap();

        assert_eq!(dag.len(), 4);

        // Frontier should be just the merge
        let frontier = dag.latest();
        assert_eq!(frontier.len(), 1);
        assert_eq!(frontier[0].turn_hash, t3.turn_hash);

        // Causal order: t1 first, then t2a and t2b (in some deterministic order), then t3
        let order = dag.causal_order();
        assert_eq!(order.len(), 4);
        assert_eq!(order[0].turn_hash, t1.turn_hash);
        assert_eq!(order[3].turn_hash, t3.turn_hash);
    }

    #[test]
    fn missing_deps_rejected() {
        let mut dag = CausalDag::new();
        let fake_dep = [0xaa; 32];
        let t = make_turn(b"orphan", vec![fake_dep], 1);

        let result = dag.insert(t);
        assert!(matches!(result, Err(CausalError::MissingDeps { .. })));
    }

    #[test]
    fn duplicate_rejected() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"turn-1", vec![], 1);
        dag.insert(t1.clone()).unwrap();

        let result = dag.insert(t1);
        assert!(matches!(result, Err(CausalError::Duplicate(_))));
    }

    #[test]
    fn hash_verification() {
        let t = make_turn(b"hello", vec![], 1);
        assert!(CausalDag::verify_hash(&t).is_ok());

        let mut bad = t.clone();
        bad.turn_hash = [0xff; 32];
        assert!(CausalDag::verify_hash(&bad).is_err());
    }

    #[test]
    fn merge_frontier_deterministic() {
        let mut dag1 = CausalDag::new();
        let mut dag2 = CausalDag::new();

        let t1 = make_turn(b"turn-1", vec![], 1);
        let t2 = make_turn(b"turn-2", vec![], 2);

        // Insert in different orders
        dag1.insert(t1.clone()).unwrap();
        dag1.insert(t2.clone()).unwrap();

        dag2.insert(t2.clone()).unwrap();
        dag2.insert(t1.clone()).unwrap();

        // Merge frontier should be the same regardless of insertion order
        assert_eq!(dag1.merge_frontier(), dag2.merge_frontier());
    }

    #[test]
    fn ancestors_and_descendants() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"t1", vec![], 1);
        let t2 = make_turn(b"t2", vec![t1.turn_hash], 2);
        let t3 = make_turn(b"t3", vec![t2.turn_hash], 1);

        dag.insert(t1.clone()).unwrap();
        dag.insert(t2.clone()).unwrap();
        dag.insert(t3.clone()).unwrap();

        let desc = dag.descendants(&t1.turn_hash);
        assert!(desc.contains(&t2.turn_hash));
        assert!(desc.contains(&t3.turn_hash));
        assert_eq!(desc.len(), 2);

        let anc = dag.ancestors(&t3.turn_hash);
        assert!(anc.contains(&t1.turn_hash));
        assert!(anc.contains(&t2.turn_hash));
        assert_eq!(anc.len(), 2);
    }

    #[test]
    fn try_insert_buffering() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"t1", vec![], 1);
        let t2 = make_turn(b"t2", vec![t1.turn_hash], 2);

        // Try inserting t2 before t1 - should return missing deps
        let result = dag.try_insert(t2.clone()).unwrap();
        assert_eq!(result, Some(vec![t1.turn_hash]));
        assert_eq!(dag.len(), 0); // Not inserted

        // Now insert t1
        dag.insert(t1).unwrap();

        // Now t2 should insert fine
        let result = dag.try_insert(t2).unwrap();
        assert_eq!(result, None);
        assert_eq!(dag.len(), 2);
    }

    #[test]
    fn happened_before_and_concurrent() {
        let mut dag = CausalDag::new();
        let t1 = make_turn(b"t1", vec![], 1);
        let t2 = make_turn(b"t2", vec![t1.turn_hash], 1);
        let t3 = make_turn(b"t3", vec![t1.turn_hash], 2);

        dag.insert(t1.clone()).unwrap();
        dag.insert(t2.clone()).unwrap();
        dag.insert(t3.clone()).unwrap();

        assert!(dag.happened_before(&t1.turn_hash, &t2.turn_hash));
        assert!(dag.happened_before(&t1.turn_hash, &t3.turn_hash));
        assert!(!dag.happened_before(&t2.turn_hash, &t3.turn_hash));
        assert!(dag.are_concurrent(&t2.turn_hash, &t3.turn_hash));
    }
}
