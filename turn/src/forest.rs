//! Call forest: the tree structure of actions in a turn.
//!
//! A CallForest contains multiple root-level CallTrees, each of which is a tree of
//! actions. This directly mirrors Mina's call_forest structure: the forest IS the
//! transaction, and Merkle hashing provides cryptographic binding of the entire tree.

use serde::{Deserialize, Serialize};

use crate::action::{Action, Effect};

/// A single tree node in the call forest.
///
/// Each node contains an action and its child sub-actions. The hash commits
/// to both the action and all descendants (Merkle structure).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CallTree {
    /// The action at this node.
    pub action: Action,
    /// Sub-actions spawned by this action.
    pub children: Vec<CallTree>,
    /// Merkle hash of (action_hash || children_hash).
    /// Computed lazily; [0; 32] means not yet computed.
    pub hash: [u8; 32],
}

/// The complete call forest: a sequence of root-level call trees.
///
/// This is the top-level transaction structure, analogous to Mina's call_forest
/// within a ZkappCommand.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CallForest {
    /// Top-level actions (each may have children forming a tree).
    pub roots: Vec<CallTree>,
    /// Root hash of the entire forest.
    /// Computed lazily; [0; 32] means not yet computed.
    pub forest_hash: [u8; 32],
}

impl CallTree {
    /// Create a new call tree node from an action (no children).
    pub fn new(action: Action) -> Self {
        Self {
            action,
            children: Vec::new(),
            hash: [0u8; 32],
        }
    }

    /// Add a child action to this tree node, returning a mutable reference to it.
    pub fn add_child(&mut self, action: Action) -> &mut CallTree {
        self.children.push(CallTree::new(action));
        self.hash = [0u8; 32]; // Invalidate cached hash.
        self.children.last_mut().unwrap()
    }

    /// Compute the depth of this tree (0 = leaf, 1 = has children, etc.).
    pub fn depth(&self) -> usize {
        if self.children.is_empty() {
            0
        } else {
            1 + self.children.iter().map(|c| c.depth()).max().unwrap_or(0)
        }
    }

    /// Compute the total number of actions in this tree (including self).
    pub fn action_count(&self) -> usize {
        1 + self
            .children
            .iter()
            .map(|c| c.action_count())
            .sum::<usize>()
    }

    /// Compute the Merkle hash of this tree node.
    ///
    /// hash = BLAKE3(action_hash || children_hash)
    /// where children_hash = BLAKE3(child1_hash || child2_hash || ...)
    pub fn compute_hash(&mut self) -> [u8; 32] {
        // Compute children hashes first (bottom-up).
        for child in &mut self.children {
            child.compute_hash();
        }

        let action_hash = self.action.hash();
        let children_hash = self.compute_children_hash();

        let mut hasher = blake3::Hasher::new();
        hasher.update(&action_hash);
        hasher.update(&children_hash);
        self.hash = *hasher.finalize().as_bytes();
        self.hash
    }

    /// Compute the hash of all children (or a zero hash if no children).
    fn compute_children_hash(&self) -> [u8; 32] {
        if self.children.is_empty() {
            [0u8; 32]
        } else {
            let mut hasher = blake3::Hasher::new();
            for child in &self.children {
                hasher.update(&child.hash);
            }
            *hasher.finalize().as_bytes()
        }
    }

    /// Iterate depth-first over this tree (pre-order: self, then children left-to-right).
    pub fn iter_dfs(&self) -> CallTreeIter<'_> {
        CallTreeIter { stack: vec![self] }
    }

    /// Collect all effects in this tree (including children), depth-first.
    pub fn all_effects(&self) -> Vec<&Effect> {
        let mut effects = Vec::new();
        for effect in &self.action.effects {
            effects.push(effect);
        }
        for child in &self.children {
            effects.extend(child.all_effects());
        }
        effects
    }
}

/// Depth-first iterator over a CallTree.
pub struct CallTreeIter<'a> {
    stack: Vec<&'a CallTree>,
}

impl<'a> Iterator for CallTreeIter<'a> {
    type Item = &'a CallTree;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        // Push children in reverse order so leftmost is popped first.
        for child in node.children.iter().rev() {
            self.stack.push(child);
        }
        Some(node)
    }
}

impl CallForest {
    /// Create a new empty call forest.
    pub fn new() -> Self {
        Self {
            roots: Vec::new(),
            forest_hash: [0u8; 32],
        }
    }

    /// Add a root-level action to the forest, returning a mutable reference to it.
    pub fn add_root(&mut self, action: Action) -> &mut CallTree {
        self.roots.push(CallTree::new(action));
        self.forest_hash = [0u8; 32]; // Invalidate cached hash.
        self.roots.last_mut().unwrap()
    }

    /// Compute the Merkle hash of the entire forest (mutating, caches result).
    ///
    /// forest_hash = BLAKE3(root1_hash || root2_hash || ...)
    pub fn hash(&mut self) -> [u8; 32] {
        // Compute all root hashes.
        for root in &mut self.roots {
            root.compute_hash();
        }

        if self.roots.is_empty() {
            self.forest_hash = [0u8; 32];
        } else {
            let mut hasher = blake3::Hasher::new();
            for root in &self.roots {
                hasher.update(&root.hash);
            }
            self.forest_hash = *hasher.finalize().as_bytes();
        }
        self.forest_hash
    }

    /// Compute the Merkle hash of the entire forest without mutating self.
    ///
    /// This recomputes from scratch each time (no caching), making it suitable
    /// for use with `&self` when cloning the forest is undesirable.
    pub fn compute_hash(&self) -> [u8; 32] {
        if self.roots.is_empty() {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        for root in &self.roots {
            hasher.update(&Self::compute_tree_hash(root));
        }
        *hasher.finalize().as_bytes()
    }

    /// Recursively compute a tree hash without mutation.
    fn compute_tree_hash(tree: &CallTree) -> [u8; 32] {
        let action_hash = tree.action.hash();
        let children_hash = if tree.children.is_empty() {
            [0u8; 32]
        } else {
            let mut h = blake3::Hasher::new();
            for child in &tree.children {
                h.update(&Self::compute_tree_hash(child));
            }
            *h.finalize().as_bytes()
        };
        let mut h = blake3::Hasher::new();
        h.update(&action_hash);
        h.update(&children_hash);
        *h.finalize().as_bytes()
    }

    /// Iterate depth-first over all trees in the forest.
    pub fn iter_dfs(&self) -> ForestDfsIter<'_> {
        ForestDfsIter {
            root_idx: 0,
            current_iter: None,
            roots: &self.roots,
        }
    }

    /// Total number of actions in the forest (including all nested children).
    pub fn action_count(&self) -> usize {
        self.roots.iter().map(|r| r.action_count()).sum()
    }

    /// Collect all effects from every action in the forest, depth-first.
    pub fn total_effects(&self) -> Vec<&Effect> {
        let mut effects = Vec::new();
        for root in &self.roots {
            effects.extend(root.all_effects());
        }
        effects
    }

    /// Check if the forest is empty (no actions).
    pub fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }

    /// Get the maximum depth of any tree in the forest.
    pub fn max_depth(&self) -> usize {
        self.roots.iter().map(|r| r.depth()).max().unwrap_or(0)
    }
}

impl Default for CallForest {
    fn default() -> Self {
        Self::new()
    }
}

/// Depth-first iterator over all trees in a CallForest.
pub struct ForestDfsIter<'a> {
    root_idx: usize,
    current_iter: Option<CallTreeIter<'a>>,
    roots: &'a [CallTree],
}

impl<'a> Iterator for ForestDfsIter<'a> {
    type Item = &'a CallTree;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(iter) = &mut self.current_iter {
                if let Some(node) = iter.next() {
                    return Some(node);
                }
            }
            // Move to next root.
            if self.root_idx >= self.roots.len() {
                return None;
            }
            self.current_iter = Some(self.roots[self.root_idx].iter_dfs());
            self.root_idx += 1;
        }
    }
}
