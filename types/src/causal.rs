//! Shared Causal DAG: a hash-linked directed acyclic graph for tracking
//! happened-before ordering between turns.
//!
//! This module provides the foundational graph structure used by both the
//! gossip network layer (`pyana-net`) and the coordination layer (`pyana-coord`).
//! It stores only the graph topology (hashes and edges), leaving domain-specific
//! entry storage to consumers.
//!
//! # Supported operations
//!
//! - Insert with dependency checking
//! - Topological sort (deterministic)
//! - Frontier tracking (turns with no successors)
//! - Happened-before queries (ancestor/descendant)
//! - Concurrency detection
//! - `try_insert` for out-of-order arrivals
//! - Depth calculation (longest path from genesis)
//! - Merge frontier hash (deterministic state fingerprint)

use std::collections::{HashMap, HashSet, VecDeque};

// ─── CausalError ──────────────────────────────────────────────────────────────

/// Errors from causal DAG operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CausalError {
    /// One or more dependencies are not yet in the DAG.
    MissingDeps {
        /// The turn that has missing deps.
        turn_hash: [u8; 32],
        /// The missing dependency hashes.
        missing: Vec<[u8; 32]>,
    },
    /// A turn with this hash already exists.
    Duplicate([u8; 32]),
}

impl std::fmt::Display for CausalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CausalError::MissingDeps { turn_hash, missing } => {
                write!(
                    f,
                    "turn {} missing {} causal dependencies",
                    hex_short(turn_hash),
                    missing.len()
                )
            }
            CausalError::Duplicate(h) => {
                write!(f, "duplicate turn: {}", hex_short(h))
            }
        }
    }
}

impl std::error::Error for CausalError {}

// ─── CausalDag ────────────────────────────────────────────────────────────────

/// A directed acyclic graph tracking happened-before relationships between turns.
///
/// Stores only the graph topology (turn hashes and edges). Domain-specific
/// metadata (turn data, timestamps, etc.) should be stored externally by consumers.
///
/// # Invariants
///
/// - Every entry's deps must be present in the DAG at insertion time.
/// - No duplicate hashes.
/// - The graph is always a DAG (guaranteed by hash-linking).
#[derive(Clone, Debug, Default)]
pub struct CausalDag {
    /// Forward edges: turn_hash -> set of turns that depend on it (successors).
    successors: HashMap<[u8; 32], HashSet<[u8; 32]>>,
    /// Backward edges: turn_hash -> set of turns it depends on (dependencies).
    dependencies: HashMap<[u8; 32], HashSet<[u8; 32]>>,
    /// All turn hashes in the DAG.
    all_turns: HashSet<[u8; 32]>,
    /// The current frontier: turns that have no successors yet.
    frontier: HashSet<[u8; 32]>,
}

impl CausalDag {
    /// Create a new empty causal DAG.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a turn into the DAG with its causal dependencies.
    ///
    /// Returns an error if:
    /// - The turn already exists (duplicate).
    /// - Any dependency is missing from the DAG.
    pub fn insert(&mut self, turn_hash: [u8; 32], deps: &[[u8; 32]]) -> Result<(), CausalError> {
        if self.all_turns.contains(&turn_hash) {
            return Err(CausalError::Duplicate(turn_hash));
        }

        // Verify all dependencies are present.
        let missing: Vec<[u8; 32]> = deps
            .iter()
            .filter(|d| !self.all_turns.contains(*d))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(CausalError::MissingDeps { turn_hash, missing });
        }

        // Insert the turn.
        self.all_turns.insert(turn_hash);
        self.dependencies
            .insert(turn_hash, deps.iter().copied().collect());
        self.successors.entry(turn_hash).or_default();

        // Register as successor of each dependency.
        for dep in deps {
            self.successors.entry(*dep).or_default().insert(turn_hash);
            // Remove dep from frontier since it now has a successor.
            self.frontier.remove(dep);
        }

        // New turn is on the frontier (no successors yet).
        self.frontier.insert(turn_hash);

        Ok(())
    }

    /// Insert a genesis turn (no dependencies required).
    pub fn insert_genesis(&mut self, turn_hash: [u8; 32]) -> Result<(), CausalError> {
        self.insert(turn_hash, &[])
    }

    /// Try to insert a turn. If all deps are present, inserts and returns `Ok(None)`.
    /// If deps are missing, returns `Ok(Some(missing_deps))` without inserting.
    /// Returns `Err` only for duplicate turns.
    pub fn try_insert(
        &mut self,
        turn_hash: [u8; 32],
        deps: &[[u8; 32]],
    ) -> Result<Option<Vec<[u8; 32]>>, CausalError> {
        if self.all_turns.contains(&turn_hash) {
            return Err(CausalError::Duplicate(turn_hash));
        }
        let missing = self.missing_deps(deps);
        if missing.is_empty() {
            self.insert(turn_hash, deps)?;
            Ok(None)
        } else {
            Ok(Some(missing))
        }
    }

    /// Check if all dependencies for a turn are present in the DAG.
    pub fn has_all_deps(&self, deps: &[[u8; 32]]) -> bool {
        deps.iter().all(|d| self.all_turns.contains(d))
    }

    /// Get the missing dependencies from a set of required deps.
    pub fn missing_deps(&self, deps: &[[u8; 32]]) -> Vec<[u8; 32]> {
        deps.iter()
            .filter(|d| !self.all_turns.contains(*d))
            .copied()
            .collect()
    }

    /// Check if `ancestor` happened before `descendant` (ancestor is reachable from
    /// descendant by following dependency edges backward).
    pub fn happened_before(&self, ancestor: &[u8; 32], descendant: &[u8; 32]) -> bool {
        if ancestor == descendant {
            return false; // A turn does not happen before itself.
        }
        if !self.all_turns.contains(ancestor) || !self.all_turns.contains(descendant) {
            return false;
        }

        // BFS backward from descendant through dependencies.
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*descendant);
        visited.insert(*descendant);

        while let Some(current) = queue.pop_front() {
            if let Some(deps) = self.dependencies.get(&current) {
                for dep in deps {
                    if dep == ancestor {
                        return true;
                    }
                    if visited.insert(*dep) {
                        queue.push_back(*dep);
                    }
                }
            }
        }

        false
    }

    /// Check if two turns are concurrent (neither happened before the other).
    pub fn are_concurrent(&self, a: &[u8; 32], b: &[u8; 32]) -> bool {
        if a == b {
            return false;
        }
        !self.happened_before(a, b) && !self.happened_before(b, a)
    }

    /// Get the current causal frontier: turns with no successors.
    pub fn frontier(&self) -> Vec<[u8; 32]> {
        self.frontier.iter().copied().collect()
    }

    /// Get a reference to the frontier set.
    pub fn frontier_set(&self) -> &HashSet<[u8; 32]> {
        &self.frontier
    }

    /// Compute a deterministic hash of the current frontier.
    /// This can be used to compare DAG states between peers.
    pub fn merge_frontier(&self) -> [u8; 32] {
        let mut frontier_hashes: Vec<[u8; 32]> = self.frontier.iter().copied().collect();
        frontier_hashes.sort();

        let mut hasher = blake3::Hasher::new();
        for h in &frontier_hashes {
            hasher.update(h);
        }
        *hasher.finalize().as_bytes()
    }

    /// Get all direct dependencies of a turn.
    pub fn deps_of(&self, turn_hash: &[u8; 32]) -> Option<&HashSet<[u8; 32]>> {
        self.dependencies.get(turn_hash)
    }

    /// Get all direct successors of a turn.
    pub fn successors_of(&self, turn_hash: &[u8; 32]) -> Option<&HashSet<[u8; 32]>> {
        self.successors.get(turn_hash)
    }

    /// Get all turns that transitively depend on the given turn (descendants).
    pub fn descendants(&self, hash: &[u8; 32]) -> HashSet<[u8; 32]> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*hash);

        while let Some(current) = queue.pop_front() {
            if let Some(succs) = self.successors.get(&current) {
                for &succ in succs {
                    if result.insert(succ) {
                        queue.push_back(succ);
                    }
                }
            }
        }

        result
    }

    /// Get all turns that this turn transitively depends on (ancestors).
    pub fn ancestors(&self, hash: &[u8; 32]) -> HashSet<[u8; 32]> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*hash);

        while let Some(current) = queue.pop_front() {
            if let Some(deps) = self.dependencies.get(&current) {
                for &dep in deps {
                    if result.insert(dep) {
                        queue.push_back(dep);
                    }
                }
            }
        }

        result
    }

    /// Whether a turn exists in the DAG.
    pub fn contains(&self, turn_hash: &[u8; 32]) -> bool {
        self.all_turns.contains(turn_hash)
    }

    /// Number of turns in the DAG.
    pub fn len(&self) -> usize {
        self.all_turns.len()
    }

    /// Whether the DAG is empty.
    pub fn is_empty(&self) -> bool {
        self.all_turns.is_empty()
    }

    /// Get the causal depth of a turn (longest path from any genesis turn to this one).
    pub fn depth(&self, turn_hash: &[u8; 32]) -> Option<usize> {
        if !self.all_turns.contains(turn_hash) {
            return None;
        }

        let mut memo: HashMap<[u8; 32], usize> = HashMap::new();
        Some(self.depth_recursive(turn_hash, &mut memo))
    }

    /// Recursive helper for depth calculation with memoization.
    /// Since the graph is a DAG, recursion always terminates.
    fn depth_recursive(&self, node: &[u8; 32], memo: &mut HashMap<[u8; 32], usize>) -> usize {
        if let Some(&d) = memo.get(node) {
            return d;
        }
        let d = match self.dependencies.get(node) {
            Some(deps) if !deps.is_empty() => {
                1 + deps
                    .iter()
                    .map(|dep| self.depth_recursive(dep, memo))
                    .max()
                    .unwrap_or(0)
            }
            _ => 0,
        };
        memo.insert(*node, d);
        d
    }

    /// Get all turns in causal (topological) order.
    /// Returns turns such that if T1 happened before T2, T1 appears first.
    /// The ordering is deterministic (sorted tie-breaking).
    pub fn topological_order(&self) -> Vec<[u8; 32]> {
        // Compute in-degree from the dependency sets.
        let mut in_deg: HashMap<[u8; 32], usize> = HashMap::new();
        for turn in &self.all_turns {
            let dep_count = self.dependencies.get(turn).map(|d| d.len()).unwrap_or(0);
            in_deg.insert(*turn, dep_count);
        }

        // Start with nodes that have zero in-degree (genesis turns).
        let mut queue: VecDeque<[u8; 32]> = VecDeque::new();
        let mut initial: Vec<[u8; 32]> = in_deg
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&hash, _)| hash)
            .collect();
        // Sort for determinism.
        initial.sort();
        queue.extend(initial);

        let mut result = Vec::with_capacity(self.all_turns.len());
        while let Some(turn) = queue.pop_front() {
            result.push(turn);
            if let Some(succs) = self.successors.get(&turn) {
                let mut next: Vec<[u8; 32]> = Vec::new();
                for succ in succs {
                    if let Some(deg) = in_deg.get_mut(succ) {
                        *deg -= 1;
                        if *deg == 0 {
                            next.push(*succ);
                        }
                    }
                }
                // Sort for determinism.
                next.sort();
                queue.extend(next);
            }
        }

        result
    }
}

/// Format a hash in short hex for display (first 4 bytes + ellipsis).
pub fn hex_short(h: &[u8; 32]) -> String {
    format!("{:02x}{:02x}{:02x}{:02x}...", h[0], h[1], h[2], h[3])
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(data: &[u8]) -> [u8; 32] {
        *blake3::hash(data).as_bytes()
    }

    #[test]
    fn empty_dag() {
        let dag = CausalDag::new();
        assert!(dag.is_empty());
        assert_eq!(dag.len(), 0);
        assert!(dag.frontier().is_empty());
        assert!(dag.topological_order().is_empty());
    }

    #[test]
    fn insert_genesis() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        dag.insert_genesis(h1).unwrap();

        assert_eq!(dag.len(), 1);
        assert!(dag.contains(&h1));
        assert_eq!(dag.frontier(), vec![h1]);
    }

    #[test]
    fn linear_chain() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        let h2 = hash(b"turn2");
        let h3 = hash(b"turn3");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        assert_eq!(dag.len(), 3);
        assert_eq!(dag.frontier(), vec![h3]);

        assert!(dag.happened_before(&h1, &h2));
        assert!(dag.happened_before(&h1, &h3));
        assert!(dag.happened_before(&h2, &h3));
        assert!(!dag.happened_before(&h3, &h1));
        assert!(!dag.happened_before(&h2, &h1));
    }

    #[test]
    fn diamond_dag() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        let h2 = hash(b"turn2");
        let h3 = hash(b"turn3");
        let h4 = hash(b"turn4");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h1]).unwrap();
        dag.insert(h4, &[h2, h3]).unwrap();

        // h2 and h3 are concurrent.
        assert!(dag.are_concurrent(&h2, &h3));
        assert!(!dag.happened_before(&h2, &h3));
        assert!(!dag.happened_before(&h3, &h2));

        // h1 happened before everything.
        assert!(dag.happened_before(&h1, &h2));
        assert!(dag.happened_before(&h1, &h3));
        assert!(dag.happened_before(&h1, &h4));

        // h4 is after everything.
        assert!(dag.happened_before(&h2, &h4));
        assert!(dag.happened_before(&h3, &h4));

        // Frontier should be h4.
        let frontier = dag.frontier();
        assert_eq!(frontier.len(), 1);
        assert!(frontier.contains(&h4));
    }

    #[test]
    fn multiple_genesis() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"node_a_genesis");
        let h2 = hash(b"node_b_genesis");

        dag.insert_genesis(h1).unwrap();
        dag.insert_genesis(h2).unwrap();

        assert_eq!(dag.len(), 2);
        assert!(dag.are_concurrent(&h1, &h2));

        let frontier = dag.frontier();
        assert_eq!(frontier.len(), 2);
        assert!(frontier.contains(&h1));
        assert!(frontier.contains(&h2));
    }

    #[test]
    fn duplicate_rejected() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        dag.insert_genesis(h1).unwrap();

        let err = dag.insert_genesis(h1).unwrap_err();
        assert_eq!(err, CausalError::Duplicate(h1));
    }

    #[test]
    fn missing_deps_rejected() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        let h2 = hash(b"turn2");

        let err = dag.insert(h2, &[h1]).unwrap_err();
        assert!(matches!(err, CausalError::MissingDeps { .. }));
    }

    #[test]
    fn topological_order() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        let h2 = hash(b"turn2");
        let h3 = hash(b"turn3");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        let order = dag.topological_order();
        assert_eq!(order.len(), 3);
        let pos_h1 = order.iter().position(|h| h == &h1).unwrap();
        let pos_h2 = order.iter().position(|h| h == &h2).unwrap();
        let pos_h3 = order.iter().position(|h| h == &h3).unwrap();
        assert!(pos_h1 < pos_h2);
        assert!(pos_h2 < pos_h3);
    }

    #[test]
    fn depth_calculation() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"turn1");
        let h2 = hash(b"turn2");
        let h3 = hash(b"turn3");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        assert_eq!(dag.depth(&h1), Some(0));
        assert_eq!(dag.depth(&h2), Some(1));
        assert_eq!(dag.depth(&h3), Some(2));
    }

    #[test]
    fn try_insert_buffering() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"t1");
        let h2 = hash(b"t2");

        // Try inserting h2 before h1 - should return missing deps.
        let result = dag.try_insert(h2, &[h1]).unwrap();
        assert_eq!(result, Some(vec![h1]));
        assert_eq!(dag.len(), 0);

        // Now insert h1.
        dag.insert_genesis(h1).unwrap();

        // Now h2 should insert fine.
        let result = dag.try_insert(h2, &[h1]).unwrap();
        assert_eq!(result, None);
        assert_eq!(dag.len(), 2);
    }

    #[test]
    fn ancestors_and_descendants() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"t1");
        let h2 = hash(b"t2");
        let h3 = hash(b"t3");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();
        dag.insert(h3, &[h2]).unwrap();

        let desc = dag.descendants(&h1);
        assert!(desc.contains(&h2));
        assert!(desc.contains(&h3));
        assert_eq!(desc.len(), 2);

        let anc = dag.ancestors(&h3);
        assert!(anc.contains(&h1));
        assert!(anc.contains(&h2));
        assert_eq!(anc.len(), 2);
    }

    #[test]
    fn merge_frontier_deterministic() {
        let mut dag1 = CausalDag::new();
        let mut dag2 = CausalDag::new();

        let h1 = hash(b"turn-1");
        let h2 = hash(b"turn-2");

        // Insert in different orders.
        dag1.insert_genesis(h1).unwrap();
        dag1.insert_genesis(h2).unwrap();

        dag2.insert_genesis(h2).unwrap();
        dag2.insert_genesis(h1).unwrap();

        // Merge frontier should be the same regardless of insertion order.
        assert_eq!(dag1.merge_frontier(), dag2.merge_frontier());
    }

    #[test]
    fn has_all_deps_check() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"t1");
        let h2 = hash(b"t2");

        dag.insert_genesis(h1).unwrap();

        assert!(dag.has_all_deps(&[h1]));
        assert!(!dag.has_all_deps(&[h2]));
        assert!(!dag.has_all_deps(&[h1, h2]));
        assert!(dag.has_all_deps(&[]));
    }

    #[test]
    fn missing_deps_query() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"t1");
        let h2 = hash(b"t2");
        let h3 = hash(b"t3");

        dag.insert_genesis(h1).unwrap();

        let missing = dag.missing_deps(&[h1, h2, h3]);
        assert_eq!(missing.len(), 2);
        assert!(missing.contains(&h2));
        assert!(missing.contains(&h3));
    }

    #[test]
    fn deps_of_and_successors_of() {
        let mut dag = CausalDag::new();
        let h1 = hash(b"t1");
        let h2 = hash(b"t2");

        dag.insert_genesis(h1).unwrap();
        dag.insert(h2, &[h1]).unwrap();

        let deps = dag.deps_of(&h2).unwrap();
        assert!(deps.contains(&h1));
        assert_eq!(deps.len(), 1);

        let succs = dag.successors_of(&h1).unwrap();
        assert!(succs.contains(&h2));
        assert_eq!(succs.len(), 1);
    }
}
