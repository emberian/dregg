//! Structured action set using BLAKE3 hashes for secure membership checks.
//!
//! Replaces string-based comma-separated action matching with hash-set membership.
//! This eliminates the substring vulnerability (e.g., `"threadwrite"` matching `"write"`)
//! and provides a circuit-friendly representation for ZK proofs.

use serde::{Deserialize, Serialize};

/// A single named permission, represented as a BLAKE3 hash of the action name.
///
/// Using a cryptographic hash ensures:
/// - No substring collisions (each action is an independent 32-byte identity)
/// - Efficient comparison (constant-time equality on fixed-size values)
/// - ZK-friendly (hashes compose into Merkle trees naturally)
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ActionId(pub [u8; 32]);

impl ActionId {
    /// Create an ActionId from a human-readable action name.
    ///
    /// The name is hashed with BLAKE3 to produce a unique 32-byte identifier.
    pub fn from_name(name: &str) -> Self {
        Self(*blake3::hash(name.as_bytes()).as_bytes())
    }

    /// Well-known action: read access.
    pub const READ: ActionId = ActionId(hex_const(
        "a9cc9a632386985a99c73c4c75981fb8b29caaed5bc1046b47f40b57d2d8f8c0",
    ));

    /// Well-known action: write/update access.
    pub const WRITE: ActionId = ActionId(hex_const(
        "e3930a88b657fd5e365f4b81a4ef0dd2594a5bb39e7b4408681dbfaaf5a9ba68",
    ));

    /// Well-known action: delete access.
    pub const DELETE: ActionId = ActionId(hex_const(
        "b9f665a80ba3af1628e0214e66b05d47e1476fc8519f99a8a06ec89bf0ff448b",
    ));

    /// Well-known action: execute access.
    pub const EXECUTE: ActionId = ActionId(hex_const(
        "5381d6d395f7f4437aec78942de726af4c3f4fb6492567eedef744db0f034019",
    ));

    /// Well-known action: delegate permission to others.
    pub const DELEGATE: ActionId = ActionId(hex_const(
        "3dcf79005744d4c73e21d8c594c709f553e901751b1f1b8229b2f26f5ac5e126",
    ));

    /// Well-known action: administrative control.
    pub const ADMIN: ActionId = ActionId(hex_const(
        "d289b2da9b7051f36b4e396e0af3e069e78cf119a7fdcb6437b685c4875e9f9e",
    ));

    /// Return the raw bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl std::fmt::Debug for ActionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ActionId({}..)",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl std::fmt::Display for ActionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

/// A set of allowed actions, represented as a sorted Vec of BLAKE3 hashes.
///
/// # Properties
///
/// - **Deterministic**: Actions are sorted by hash value, so the same set
///   always produces the same serialization and Merkle root.
/// - **O(log n) membership**: Binary search on sorted hashes.
/// - **Subset checking**: Efficient set containment for attenuation verification.
/// - **Merkle commitment**: For the ZK path, the sorted hashes form a Merkle
///   sub-tree enabling membership proofs without revealing the full set.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActionSet {
    /// Sorted vector of action hashes.
    actions: Vec<ActionId>,
}

impl ActionSet {
    /// Create an ActionSet from a list of action names.
    ///
    /// The names are hashed and the resulting set is sorted and deduplicated.
    pub fn new(names: &[&str]) -> Self {
        let mut actions: Vec<ActionId> = names.iter().map(|n| ActionId::from_name(n)).collect();
        actions.sort_by(|a, b| a.0.cmp(&b.0));
        actions.dedup();
        Self { actions }
    }

    /// Create an ActionSet from pre-computed ActionIds.
    pub fn from_ids(ids: &[ActionId]) -> Self {
        let mut actions = ids.to_vec();
        actions.sort_by(|a, b| a.0.cmp(&b.0));
        actions.dedup();
        Self { actions }
    }

    /// Create an empty ActionSet.
    pub fn empty() -> Self {
        Self {
            actions: Vec::new(),
        }
    }

    /// Parse from a legacy comma-separated string format.
    ///
    /// This provides backward compatibility with tokens serialized using the
    /// old `"read,write,delete"` format. Each part between commas is trimmed
    /// and hashed independently.
    pub fn from_legacy_string(s: &str) -> Self {
        if s.is_empty() {
            return Self::empty();
        }
        let names: Vec<&str> = s.split(',').map(|part| part.trim()).collect();
        Self::new(&names)
    }

    /// Check if this set contains a specific action.
    ///
    /// O(log n) via binary search on sorted hashes.
    pub fn contains(&self, action: &ActionId) -> bool {
        self.actions
            .binary_search_by(|a| a.0.cmp(&action.0))
            .is_ok()
    }

    /// Check if all actions in `other` are also in `self`.
    ///
    /// Used for attenuation verification: a child token's action set must
    /// be a subset of its parent's action set.
    pub fn is_subset_of(&self, other: &ActionSet) -> bool {
        self.actions.iter().all(|a| other.contains(a))
    }

    /// Check if this set is a superset of `other`.
    pub fn is_superset_of(&self, other: &ActionSet) -> bool {
        other.is_subset_of(self)
    }

    /// Intersect this set with another (AND semantics for caveat attenuation).
    pub fn intersect(&self, other: &ActionSet) -> ActionSet {
        let actions: Vec<ActionId> = self
            .actions
            .iter()
            .filter(|a| other.contains(a))
            .copied()
            .collect();
        Self { actions }
    }

    /// Return the number of actions in the set.
    pub fn len(&self) -> usize {
        self.actions.len()
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }

    /// Iterate over the action IDs in sorted order.
    pub fn iter(&self) -> impl Iterator<Item = &ActionId> {
        self.actions.iter()
    }

    /// Compute a Merkle root over the sorted action hashes.
    ///
    /// For the ZK path, this root commits to the exact set of allowed actions.
    /// A membership proof can then demonstrate that a specific action hash is
    /// in the committed set without revealing the other actions.
    ///
    /// Uses a binary Merkle tree with BLAKE3 for internal nodes.
    /// Leaf nodes are the action hashes themselves (already BLAKE3 outputs).
    pub fn merkle_root(&self) -> [u8; 32] {
        if self.actions.is_empty() {
            return [0u8; 32];
        }
        if self.actions.len() == 1 {
            return self.actions[0].0;
        }

        // Pad to next power of two with zero hashes.
        let n = self.actions.len().next_power_of_two();
        let mut layer: Vec<[u8; 32]> = self.actions.iter().map(|a| a.0).collect();
        layer.resize(n, [0u8; 32]);

        // Build Merkle tree bottom-up.
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
}

/// Compile-time hex string to bytes (for well-known action constants).
///
/// The hex values are the actual BLAKE3 hashes of the action name strings
/// (e.g., `blake3::hash(b"read")`), ensuring that `ActionId::READ` is
/// identical to `ActionId::from_name("read")` at all times.
const fn hex_const(hex: &str) -> [u8; 32] {
    let bytes = hex.as_bytes();
    let mut result = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let hi = hex_digit(bytes[i * 2]);
        let lo = hex_digit(bytes[i * 2 + 1]);
        result[i] = (hi << 4) | lo;
        i += 1;
    }
    result
}

const fn hex_digit(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => 0,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_id_from_name_deterministic() {
        let a1 = ActionId::from_name("read");
        let a2 = ActionId::from_name("read");
        assert_eq!(a1, a2);
    }

    #[test]
    fn test_action_id_different_names_differ() {
        let read = ActionId::from_name("read");
        let write = ActionId::from_name("write");
        assert_ne!(read, write);
    }

    #[test]
    fn test_action_set_contains() {
        let set = ActionSet::new(&["read", "write"]);
        assert!(set.contains(&ActionId::from_name("read")));
        assert!(set.contains(&ActionId::from_name("write")));
        assert!(!set.contains(&ActionId::from_name("delete")));
    }

    #[test]
    fn test_action_set_no_substring_vulnerability() {
        // The whole point: "threadwrite" must NOT match "write"
        let set = ActionSet::new(&["read", "write", "delete"]);
        assert!(!set.contains(&ActionId::from_name("threadwrite")));
        assert!(!set.contains(&ActionId::from_name("readsomething")));
        assert!(!set.contains(&ActionId::from_name("elete")));
        // But actual members do match
        assert!(set.contains(&ActionId::from_name("write")));
        assert!(set.contains(&ActionId::from_name("read")));
        assert!(set.contains(&ActionId::from_name("delete")));
    }

    #[test]
    fn test_action_set_subset() {
        let parent = ActionSet::new(&["read", "write", "delete"]);
        let child = ActionSet::new(&["read", "write"]);
        let unrelated = ActionSet::new(&["read", "execute"]);

        assert!(child.is_subset_of(&parent));
        assert!(!parent.is_subset_of(&child));
        assert!(!unrelated.is_subset_of(&parent)); // execute not in parent
    }

    #[test]
    fn test_action_set_intersect() {
        let a = ActionSet::new(&["read", "write", "delete"]);
        let b = ActionSet::new(&["read", "execute"]);
        let intersection = a.intersect(&b);

        assert_eq!(intersection.len(), 1);
        assert!(intersection.contains(&ActionId::from_name("read")));
        assert!(!intersection.contains(&ActionId::from_name("write")));
        assert!(!intersection.contains(&ActionId::from_name("execute")));
    }

    #[test]
    fn test_action_set_from_legacy_string() {
        let set = ActionSet::from_legacy_string("read,write,delete");
        assert_eq!(set.len(), 3);
        assert!(set.contains(&ActionId::from_name("read")));
        assert!(set.contains(&ActionId::from_name("write")));
        assert!(set.contains(&ActionId::from_name("delete")));
    }

    #[test]
    fn test_action_set_from_legacy_string_with_spaces() {
        let set = ActionSet::from_legacy_string("read, write , delete");
        assert_eq!(set.len(), 3);
        assert!(set.contains(&ActionId::from_name("read")));
        assert!(set.contains(&ActionId::from_name("write")));
        assert!(set.contains(&ActionId::from_name("delete")));
    }

    #[test]
    fn test_action_set_empty() {
        let set = ActionSet::from_legacy_string("");
        assert!(set.is_empty());
        assert!(!set.contains(&ActionId::from_name("read")));
    }

    #[test]
    fn test_action_set_merkle_root_deterministic() {
        let set1 = ActionSet::new(&["read", "write", "delete"]);
        let set2 = ActionSet::new(&["delete", "read", "write"]); // different order, same set
        assert_eq!(set1.merkle_root(), set2.merkle_root());
    }

    #[test]
    fn test_action_set_merkle_root_changes_with_content() {
        let set1 = ActionSet::new(&["read", "write"]);
        let set2 = ActionSet::new(&["read", "write", "delete"]);
        assert_ne!(set1.merkle_root(), set2.merkle_root());
    }

    #[test]
    fn test_action_set_merkle_root_empty() {
        let set = ActionSet::empty();
        assert_eq!(set.merkle_root(), [0u8; 32]);
    }

    #[test]
    fn test_action_set_merkle_root_single() {
        let set = ActionSet::new(&["read"]);
        let expected = ActionId::from_name("read").0;
        assert_eq!(set.merkle_root(), expected);
    }

    #[test]
    fn test_action_set_deduplicates() {
        let set = ActionSet::new(&["read", "read", "write", "write"]);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_well_known_constants_are_nonzero() {
        assert_ne!(ActionId::READ.0, [0u8; 32]);
        assert_ne!(ActionId::WRITE.0, [0u8; 32]);
        assert_ne!(ActionId::DELETE.0, [0u8; 32]);
        assert_ne!(ActionId::EXECUTE.0, [0u8; 32]);
        assert_ne!(ActionId::DELEGATE.0, [0u8; 32]);
        assert_ne!(ActionId::ADMIN.0, [0u8; 32]);
    }

    #[test]
    fn test_well_known_constants_match_from_name() {
        // The well-known constants MUST equal the BLAKE3 hash computed by from_name.
        // If these fail, someone set hand-picked placeholder values instead of real hashes.
        assert_eq!(ActionId::READ, ActionId::from_name("read"));
        assert_eq!(ActionId::WRITE, ActionId::from_name("write"));
        assert_eq!(ActionId::DELETE, ActionId::from_name("delete"));
        assert_eq!(ActionId::EXECUTE, ActionId::from_name("execute"));
        assert_eq!(ActionId::DELEGATE, ActionId::from_name("delegate"));
        assert_eq!(ActionId::ADMIN, ActionId::from_name("admin"));
    }

    #[test]
    fn test_action_set_serialization_roundtrip() {
        let set = ActionSet::new(&["read", "write", "delete"]);
        let bytes = rmp_serde::to_vec(&set).unwrap();
        let restored: ActionSet = rmp_serde::from_slice(&bytes).unwrap();
        assert_eq!(set, restored);
    }
}
