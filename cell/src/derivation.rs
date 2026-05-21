//! Capability Derivation Tree (CDT) — tracks provenance of every capability.
//!
//! Inspired by seL4's CDT, adapted for the distributed case. In seL4 the CDT
//! enables complete revocation (revoke all descendants of a cap). In pyana
//! (distributed, no kernel), we track derivation provenance and enable
//! VERIFIABLE revocation claims:
//!
//! - Every GrantCapability, Introduce, SpawnWithDelegation, and Unseal effect
//!   creates a DERIVATION EDGE.
//! - The CDT is a tree where nodes are (CellId, slot) pairs.
//! - A revocation at any node can claim "all descendants of this cap are revoked."
//! - Verifiers can check: "was this cap derived from a revoked ancestor?"
//!
//! # Revocation Model
//!
//! **Runtime (executor) revocation** is handled by the [`RevocationChannelSet`]
//! (see `revocation_channel.rs`). When a delegated capability has a `channel_id`,
//! the executor checks the channel set before allowing exercise. This provides
//! O(1) instant revocation without CDT traversal.
//!
//! **The CDT is NOT consulted during turn execution.** It is an off-chain/verifier-side
//! data structure reconstructed from `DerivationRecord`s emitted in turn receipts.
//! External verifiers and auditors use `has_revoked_ancestor()` to verify that a
//! capability's provenance chain is untainted. The ZK circuit (future) will prove
//! non-revocation against the CDT's nullifier set without revealing the chain.
//!
//! [`RevocationChannelSet`]: crate::revocation_channel::RevocationChannelSet
//!
//! # ZK Integration (Poseidon2MerkleProof)
//!
//! The derivation path FROM a cap TO the original minting root can be proven in
//! ZK. The prover shows "my cap descends from a valid root" without revealing
//! the intermediate chain. The proof structure:
//!
//! 1. Commit each derivation node to a Poseidon2 leaf:
//!    `leaf = Poseidon2(cell_id || slot || parent_hash || derivation_type)`
//! 2. Insert all derivation nodes into a Poseidon2MerkleTree (from pyana-commit).
//! 3. To prove valid ancestry: provide a chain of membership proofs from the
//!    leaf (your cap) up through each ancestor to the minting root, each with
//!    a valid Poseidon2MerkleProof.
//! 4. To prove non-revocation: for each ancestor in the chain, provide a
//!    non-membership proof against the revocation set (NullifierSet-style).
//!
//! The circuit (not yet implemented) would verify:
//! - Each node in the chain has a valid membership proof in the CDT tree.
//! - The chain is correctly linked (child.parent_hash == hash(parent_node)).
//! - No node in the chain appears in the revocation nullifier set.
//! - The chain terminates at a recognized minting root.

use std::collections::{HashMap, HashSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::id::CellId;

/// The type of derivation that produced a capability.
///
/// Each variant corresponds to an effect in the turn executor that creates
/// a new capability entry from an existing one.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DerivationType {
    /// GrantCapability: direct grant from one cell's c-list to another.
    Grant,
    /// Three-party introduction: A introduces B to C.
    Introduce,
    /// SpawnWithDelegation: child inherits parent's c-list snapshot.
    Delegate,
    /// Recovered from a sealed box via Unseal effect.
    Unseal,
    /// Token-level attenuation (narrowed permissions on an existing cap).
    Attenuate,
}

/// A directed edge in the derivation tree: records WHERE a capability came from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationEdge {
    /// The cell that held the source capability.
    pub source_cell: CellId,
    /// The slot in the source cell's c-list.
    pub source_slot: u32,
    /// How the derivation was performed.
    pub derivation_type: DerivationType,
}

impl DerivationEdge {
    /// Compute a BLAKE3 hash of this edge for use in receipts and proofs.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-derivation-edge-v1");
        hasher.update(self.source_cell.as_bytes());
        hasher.update(&self.source_slot.to_le_bytes());
        hasher.update(&[self.derivation_type_tag()]);
        *hasher.finalize().as_bytes()
    }

    fn derivation_type_tag(&self) -> u8 {
        match self.derivation_type {
            DerivationType::Grant => 0,
            DerivationType::Introduce => 1,
            DerivationType::Delegate => 2,
            DerivationType::Unseal => 3,
            DerivationType::Attenuate => 4,
        }
    }
}

/// A node in the Capability Derivation Tree.
///
/// Each node represents a capability held in a specific cell at a specific slot,
/// with provenance information linking it to its parent derivation (if any).
/// Root nodes (parent = None) represent originally-minted capabilities.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DerivationNode {
    /// The cell holding this capability.
    pub cell: CellId,
    /// The slot in the cell's c-list.
    pub slot: u32,
    /// How this capability was derived (None for original mints).
    pub parent: Option<DerivationEdge>,
    /// Turn height or timestamp when this derivation was created.
    pub created_at: u64,
    /// Hash of the turn that created this derivation.
    pub created_by_turn: [u8; 32],
}

impl DerivationNode {
    /// Compute a BLAKE3 hash of this node for inclusion in Merkle structures.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-derivation-node-v1");
        hasher.update(self.cell.as_bytes());
        hasher.update(&self.slot.to_le_bytes());
        match &self.parent {
            Some(edge) => {
                hasher.update(&[1u8]);
                hasher.update(&edge.hash());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        hasher.update(&self.created_at.to_le_bytes());
        hasher.update(&self.created_by_turn);
        *hasher.finalize().as_bytes()
    }

    /// The key that identifies this node in the tree: (cell, slot).
    pub fn key(&self) -> (CellId, u32) {
        (self.cell, self.slot)
    }

    /// The key of the parent node, if this is a derived capability.
    pub fn parent_key(&self) -> Option<(CellId, u32)> {
        self.parent
            .as_ref()
            .map(|edge| (edge.source_cell, edge.source_slot))
    }
}

/// The Capability Derivation Tree: tracks all capability derivation relationships.
///
/// This is a forest of trees (multiple roots for independently minted caps).
/// Nodes are keyed by (CellId, slot) pairs. The structure enables:
///
/// - Ancestor queries: trace a cap back to its minting root.
/// - Descendant queries: find all capabilities derived from a given cap.
/// - Cascading revocation: check if any ancestor has been revoked.
/// - ZK provenance proofs: prove derivation chain without revealing intermediates.
#[derive(Clone, Debug, Default)]
pub struct DerivationTree {
    /// All nodes, keyed by (cell, slot).
    nodes: HashMap<(CellId, u32), DerivationNode>,
    /// Children index: for each node, the list of nodes derived from it.
    children: HashMap<(CellId, u32), Vec<(CellId, u32)>>,
}

impl DerivationTree {
    /// Create a new empty derivation tree.
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            children: HashMap::new(),
        }
    }

    /// Record a new derivation in the tree.
    ///
    /// This inserts the node and updates the parent's children index.
    /// If a node with the same (cell, slot) already exists, it is replaced
    /// (capabilities can be revoked and re-granted to the same slot).
    pub fn record_derivation(&mut self, node: DerivationNode) {
        let key = node.key();

        // If the node has a parent, register as a child.
        if let Some(parent_key) = node.parent_key() {
            self.children.entry(parent_key).or_default().push(key);
        }

        self.nodes.insert(key, node);
    }

    /// Get a node by its (cell, slot) key.
    pub fn get(&self, cell: &CellId, slot: u32) -> Option<&DerivationNode> {
        self.nodes.get(&(*cell, slot))
    }

    /// Walk the ancestor chain from a node up to the root.
    ///
    /// Returns all ancestors in order from immediate parent to root (minting origin).
    /// The starting node itself is NOT included.
    pub fn ancestors(&self, cell: &CellId, slot: u32) -> Vec<&DerivationNode> {
        let mut result = Vec::new();
        let mut current_key = Some((*cell, slot));

        while let Some(key) = current_key {
            if let Some(node) = self.nodes.get(&key) {
                // Skip the starting node itself.
                if key != (*cell, slot) {
                    result.push(node);
                }
                current_key = node.parent_key();
            } else {
                break;
            }
        }

        result
    }

    /// Find all descendants of a node (breadth-first).
    ///
    /// Returns all nodes reachable by following child edges from the given node.
    /// The starting node itself is NOT included.
    pub fn descendants(&self, cell: &CellId, slot: u32) -> Vec<&DerivationNode> {
        let mut result = Vec::new();
        let mut queue = VecDeque::new();
        queue.push_back((*cell, slot));

        while let Some(key) = queue.pop_front() {
            if let Some(child_keys) = self.children.get(&key) {
                for child_key in child_keys {
                    if let Some(child_node) = self.nodes.get(child_key) {
                        result.push(child_node);
                        queue.push_back(*child_key);
                    }
                }
            }
        }

        result
    }

    /// Check if `child` is a descendant of `ancestor` in the derivation tree.
    ///
    /// Walks the ancestor chain from `child` upward, checking if any node
    /// matches `ancestor`. Returns true if a path exists.
    pub fn is_descendant_of(&self, child: (&CellId, u32), ancestor: (&CellId, u32)) -> bool {
        let ancestor_key = (*ancestor.0, ancestor.1);
        let mut current_key = Some((*child.0, child.1));

        while let Some(key) = current_key {
            if key == ancestor_key {
                return true;
            }
            current_key = self.nodes.get(&key).and_then(|n| n.parent_key());
        }

        false
    }

    /// Check if any ancestor of the given cap has been revoked.
    ///
    /// The `revocation_set` contains (CellId, slot) pairs that have been revoked.
    /// This walks the ancestor chain and checks each node against the set.
    /// If any ancestor is in the revocation set, the cap is considered transitively revoked.
    ///
    /// Integration with NullifierSet: the revocation_set is populated by hashing
    /// (cell, slot) pairs of revoked capabilities. For ZK verification, this
    /// becomes a non-membership proof against the nullifier set.
    pub fn has_revoked_ancestor(
        &self,
        cell: &CellId,
        slot: u32,
        revocation_set: &HashSet<(CellId, u32)>,
    ) -> bool {
        // Check the node itself first.
        let start_key = (*cell, slot);
        if revocation_set.contains(&start_key) {
            return true;
        }

        // Walk ancestors.
        let mut current_key = self.nodes.get(&start_key).and_then(|n| n.parent_key());

        while let Some(key) = current_key {
            if revocation_set.contains(&key) {
                return true;
            }
            current_key = self.nodes.get(&key).and_then(|n| n.parent_key());
        }

        false
    }

    /// Compute the revocation hash for a (cell, slot) pair.
    ///
    /// This hash is what goes into the NullifierSet/revocation set.
    /// Matches the domain separation used by the nullifier set so that
    /// ZK non-membership proofs are compatible.
    pub fn revocation_hash(cell: &CellId, slot: u32) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-cdt-revocation-v1");
        hasher.update(cell.as_bytes());
        hasher.update(&slot.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Number of nodes in the tree.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Iterate over all nodes.
    pub fn iter(&self) -> impl Iterator<Item = (&(CellId, u32), &DerivationNode)> {
        self.nodes.iter()
    }

    /// Get all root nodes (nodes with no parent — original mints).
    pub fn roots(&self) -> Vec<&DerivationNode> {
        self.nodes.values().filter(|n| n.parent.is_none()).collect()
    }

    /// Collect the full derivation path from a node to its root.
    ///
    /// Returns the chain of nodes from the given node (inclusive) up to
    /// and including the root. Useful for constructing ZK provenance proofs.
    pub fn derivation_path(&self, cell: &CellId, slot: u32) -> Vec<&DerivationNode> {
        let mut path = Vec::new();
        let mut current_key = Some((*cell, slot));

        while let Some(key) = current_key {
            if let Some(node) = self.nodes.get(&key) {
                path.push(node);
                current_key = node.parent_key();
            } else {
                break;
            }
        }

        path
    }

    /// Compute the Merkle commitment of a derivation path.
    ///
    /// This produces a hash chain that can be verified in ZK:
    /// `hash(leaf || hash(parent || hash(grandparent || ... || root)))`
    ///
    /// The resulting hash binds a capability to its entire provenance chain
    /// without revealing the intermediate nodes to the verifier.
    pub fn path_commitment(&self, cell: &CellId, slot: u32) -> [u8; 32] {
        let path = self.derivation_path(cell, slot);
        if path.is_empty() {
            return [0u8; 32];
        }

        // Hash from root to leaf (accumulate).
        let mut acc = [0u8; 32];
        for node in path.iter().rev() {
            let mut hasher = blake3::Hasher::new_derive_key("pyana-cdt-path-v1");
            hasher.update(&node.hash());
            hasher.update(&acc);
            acc = *hasher.finalize().as_bytes();
        }

        acc
    }
}

/// A derivation edge record emitted in a TurnReceipt.
///
/// This is the receipt-level representation of a derivation event,
/// suitable for inclusion alongside `RoutingDirective`s. Verifiers
/// use these to reconstruct the CDT from the receipt chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationRecord {
    /// The cell that now holds the derived capability.
    pub target_cell: CellId,
    /// The slot in the target cell's c-list.
    pub target_slot: u32,
    /// The source of the derivation.
    pub edge: DerivationEdge,
    /// Timestamp/height of the derivation.
    pub created_at: u64,
}

impl DerivationRecord {
    /// Compute a BLAKE3 hash of this record for receipt inclusion.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-derivation-record-v1");
        hasher.update(self.target_cell.as_bytes());
        hasher.update(&self.target_slot.to_le_bytes());
        hasher.update(&self.edge.hash());
        hasher.update(&self.created_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Convert this record into a DerivationNode for insertion into the CDT.
    pub fn to_node(&self, turn_hash: [u8; 32]) -> DerivationNode {
        DerivationNode {
            cell: self.target_cell,
            slot: self.target_slot,
            parent: Some(self.edge.clone()),
            created_at: self.created_at,
            created_by_turn: turn_hash,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(37);
        let mut token = [0u8; 32];
        token[0] = seed;
        token[1] = 0xAA;
        CellId::derive_raw(&pk, &token)
    }

    fn make_turn_hash(seed: u8) -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = seed;
        h[31] = seed.wrapping_mul(99);
        h
    }

    #[test]
    fn test_empty_tree() {
        let tree = DerivationTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert!(tree.roots().is_empty());
    }

    #[test]
    fn test_record_root_derivation() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);

        // Root node: original mint, no parent.
        let root = DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        };

        tree.record_derivation(root.clone());
        assert_eq!(tree.len(), 1);
        assert_eq!(tree.roots().len(), 1);

        let fetched = tree.get(&cell_a, 0).unwrap();
        assert_eq!(fetched.cell, cell_a);
        assert_eq!(fetched.slot, 0);
        assert!(fetched.parent.is_none());
    }

    #[test]
    fn test_three_level_derivation_tree() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);

        // Root: cell_a, slot 0 (original mint)
        let root = DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        };
        tree.record_derivation(root);

        // Child: cell_b, slot 0 (granted from cell_a slot 0)
        let child = DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        };
        tree.record_derivation(child);

        // Grandchild: cell_c, slot 0 (introduced from cell_b slot 0)
        let grandchild = DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_b,
                source_slot: 0,
                derivation_type: DerivationType::Introduce,
            }),
            created_at: 300,
            created_by_turn: make_turn_hash(3),
        };
        tree.record_derivation(grandchild);

        // Check tree structure.
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.roots().len(), 1);

        // Ancestors of grandchild: [child, root]
        let ancestors = tree.ancestors(&cell_c, 0);
        assert_eq!(ancestors.len(), 2);
        assert_eq!(ancestors[0].cell, cell_b);
        assert_eq!(ancestors[1].cell, cell_a);

        // Descendants of root: [child, grandchild]
        let descendants = tree.descendants(&cell_a, 0);
        assert_eq!(descendants.len(), 2);

        // is_descendant_of checks
        assert!(tree.is_descendant_of((&cell_c, 0), (&cell_a, 0)));
        assert!(tree.is_descendant_of((&cell_b, 0), (&cell_a, 0)));
        assert!(!tree.is_descendant_of((&cell_a, 0), (&cell_c, 0)));
    }

    #[test]
    fn test_revoke_child_affects_grandchild() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);

        // Build 3-level tree: A -> B -> C
        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_b,
                source_slot: 0,
                derivation_type: DerivationType::Introduce,
            }),
            created_at: 300,
            created_by_turn: make_turn_hash(3),
        });

        // Revoke child (cell_b, slot 0).
        let mut revocation_set = HashSet::new();
        revocation_set.insert((cell_b, 0));

        // Grandchild should have a revoked ancestor.
        assert!(tree.has_revoked_ancestor(&cell_c, 0, &revocation_set));

        // The child itself is revoked.
        assert!(tree.has_revoked_ancestor(&cell_b, 0, &revocation_set));

        // Root is NOT affected.
        assert!(!tree.has_revoked_ancestor(&cell_a, 0, &revocation_set));
    }

    #[test]
    fn test_revoke_root_affects_all_descendants() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);

        // Build 3-level tree: A -> B -> C
        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_b,
                source_slot: 0,
                derivation_type: DerivationType::Delegate,
            }),
            created_at: 300,
            created_by_turn: make_turn_hash(3),
        });

        // Revoke root (cell_a, slot 0).
        let mut revocation_set = HashSet::new();
        revocation_set.insert((cell_a, 0));

        // ALL descendants should be affected.
        assert!(tree.has_revoked_ancestor(&cell_a, 0, &revocation_set));
        assert!(tree.has_revoked_ancestor(&cell_b, 0, &revocation_set));
        assert!(tree.has_revoked_ancestor(&cell_c, 0, &revocation_set));
    }

    #[test]
    fn test_unrelated_cap_not_affected() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);
        let cell_d = make_cell_id(4);

        // Tree 1: A -> B -> C
        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_b,
                source_slot: 0,
                derivation_type: DerivationType::Introduce,
            }),
            created_at: 300,
            created_by_turn: make_turn_hash(3),
        });

        // Tree 2: D (independent root, unrelated)
        tree.record_derivation(DerivationNode {
            cell: cell_d,
            slot: 0,
            parent: None,
            created_at: 150,
            created_by_turn: make_turn_hash(4),
        });

        // Revoke root of tree 1.
        let mut revocation_set = HashSet::new();
        revocation_set.insert((cell_a, 0));

        // D is completely unaffected.
        assert!(!tree.has_revoked_ancestor(&cell_d, 0, &revocation_set));

        // B and C are affected.
        assert!(tree.has_revoked_ancestor(&cell_b, 0, &revocation_set));
        assert!(tree.has_revoked_ancestor(&cell_c, 0, &revocation_set));
    }

    #[test]
    fn test_derivation_path_and_commitment() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);

        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        });
        tree.record_derivation(DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_b,
                source_slot: 0,
                derivation_type: DerivationType::Unseal,
            }),
            created_at: 300,
            created_by_turn: make_turn_hash(3),
        });

        // Path from grandchild to root: [C, B, A]
        let path = tree.derivation_path(&cell_c, 0);
        assert_eq!(path.len(), 3);
        assert_eq!(path[0].cell, cell_c);
        assert_eq!(path[1].cell, cell_b);
        assert_eq!(path[2].cell, cell_a);

        // Path commitment should be deterministic.
        let commit1 = tree.path_commitment(&cell_c, 0);
        let commit2 = tree.path_commitment(&cell_c, 0);
        assert_eq!(commit1, commit2);

        // Different paths should have different commitments.
        let commit_b = tree.path_commitment(&cell_b, 0);
        assert_ne!(commit1, commit_b);
    }

    #[test]
    fn test_derivation_edge_hash_deterministic() {
        let cell_a = make_cell_id(1);
        let edge = DerivationEdge {
            source_cell: cell_a,
            source_slot: 3,
            derivation_type: DerivationType::Grant,
        };

        let h1 = edge.hash();
        let h2 = edge.hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_derivation_record_to_node() {
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let turn_hash = make_turn_hash(5);

        let record = DerivationRecord {
            target_cell: cell_b,
            target_slot: 1,
            edge: DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            },
            created_at: 500,
        };

        let node = record.to_node(turn_hash);
        assert_eq!(node.cell, cell_b);
        assert_eq!(node.slot, 1);
        assert_eq!(node.created_at, 500);
        assert_eq!(node.created_by_turn, turn_hash);
        assert!(node.parent.is_some());
        let parent = node.parent.unwrap();
        assert_eq!(parent.source_cell, cell_a);
        assert_eq!(parent.source_slot, 0);
    }

    #[test]
    fn test_revocation_hash_deterministic() {
        let cell = make_cell_id(1);
        let h1 = DerivationTree::revocation_hash(&cell, 0);
        let h2 = DerivationTree::revocation_hash(&cell, 0);
        assert_eq!(h1, h2);

        // Different slot -> different hash.
        let h3 = DerivationTree::revocation_hash(&cell, 1);
        assert_ne!(h1, h3);
    }

    #[test]
    fn test_multiple_children_from_same_parent() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(2);
        let cell_c = make_cell_id(3);
        let cell_d = make_cell_id(4);

        // Root: A
        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });

        // B derived from A (grant)
        tree.record_derivation(DerivationNode {
            cell: cell_b,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Grant,
            }),
            created_at: 200,
            created_by_turn: make_turn_hash(2),
        });

        // C derived from A (introduce)
        tree.record_derivation(DerivationNode {
            cell: cell_c,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Introduce,
            }),
            created_at: 250,
            created_by_turn: make_turn_hash(3),
        });

        // D derived from A (delegate)
        tree.record_derivation(DerivationNode {
            cell: cell_d,
            slot: 0,
            parent: Some(DerivationEdge {
                source_cell: cell_a,
                source_slot: 0,
                derivation_type: DerivationType::Delegate,
            }),
            created_at: 275,
            created_by_turn: make_turn_hash(4),
        });

        // A should have 3 descendants.
        let desc = tree.descendants(&cell_a, 0);
        assert_eq!(desc.len(), 3);

        // Revoking A should affect all three.
        let mut revocation_set = HashSet::new();
        revocation_set.insert((cell_a, 0));
        assert!(tree.has_revoked_ancestor(&cell_b, 0, &revocation_set));
        assert!(tree.has_revoked_ancestor(&cell_c, 0, &revocation_set));
        assert!(tree.has_revoked_ancestor(&cell_d, 0, &revocation_set));
    }

    #[test]
    fn test_node_not_in_tree_returns_false_for_revocation() {
        let tree = DerivationTree::new();
        let cell_a = make_cell_id(1);

        // Node not in the tree — no ancestors to check.
        let revocation_set = HashSet::new();
        assert!(!tree.has_revoked_ancestor(&cell_a, 0, &revocation_set));
    }

    #[test]
    fn test_is_descendant_of_self_is_true() {
        let mut tree = DerivationTree::new();
        let cell_a = make_cell_id(1);

        tree.record_derivation(DerivationNode {
            cell: cell_a,
            slot: 0,
            parent: None,
            created_at: 100,
            created_by_turn: make_turn_hash(1),
        });

        // A node is considered a descendant of itself (reflexive).
        assert!(tree.is_descendant_of((&cell_a, 0), (&cell_a, 0)));
    }
}
