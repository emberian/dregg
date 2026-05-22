//! Revocation subsystem: provider-side registry and legacy cuckoo pre-filter.
//!
//! # Architecture
//!
//! The primary type is [`RevocationRegistry`]: a service provider's revocation
//! registry that maintains both an exact set (for the provider's own O(1) checks)
//! and a sorted Merkle tree (for generating non-membership proofs that users can
//! present to third parties offline).
//!
//! The legacy [`RevocationFilter`] (cuckoo filter) is retained but deprecated as
//! the primary path. It can be used as a high-throughput pre-filter for deployments
//! with extremely high query rates, but is **not a ground truth** due to its
//! inherent false-positive rate.
//!
//! # Strategy Pattern
//!
//! - **Provider-side revocation**: Use `RevocationRegistry::revoke()` and
//!   `RevocationRegistry::is_revoked()` for exact, authoritative checks.
//! - **User-facing proof generation**: Use `RevocationRegistry::prove_non_revocation()`
//!   to produce a Merkle non-membership proof that the user can present offline.
//! - **Root attestation**: Use `RevocationRegistry::publish_root()` to sign the
//!   current tree root, and `RevocationRegistry::attested_root()` to retrieve it.

use rand::SeedableRng;
use rand::rngs::StdRng;
use scalable_cuckoo_filter::{ScalableCuckooFilter, ScalableCuckooFilterBuilder};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

/// Default false-positive rate for the revocation filter.
const DEFAULT_FALSE_POSITIVE_RATE: f64 = 0.001; // 0.1%

/// Default initial capacity (number of expected entries).
const DEFAULT_INITIAL_CAPACITY: usize = 1024;

/// A Send-safe RNG wrapper that implements Default (required by ScalableCuckooFilter's
/// serde deserialization, which skips the rng field and fills it via Default).
#[derive(Debug)]
struct SendRng(StdRng);

impl Clone for SendRng {
    fn clone(&self) -> Self {
        // StdRng doesn't implement Clone in rand 0.9; create a fresh one from OS.
        Self(StdRng::from_os_rng())
    }
}

impl Default for SendRng {
    fn default() -> Self {
        Self(StdRng::from_os_rng())
    }
}

impl rand::RngCore for SendRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }
}

/// Type alias for a cuckoo filter using a Send-safe RNG.
type SendSafeFilter = ScalableCuckooFilter<str, scalable_cuckoo_filter::DefaultHasher, SendRng>;

/// Thread-safe revocation filter backed by a scalable cuckoo filter.
///
/// Provides O(1) revocation checks for token nonces. The filter can be
/// persisted to disk and restored (via serde) for sidecar restarts.
///
/// # Deprecation Notice
///
/// This type is retained for backward compatibility but is **not** a ground truth
/// due to its inherent false-positive rate. For new code, use [`RevocationRegistry`]
/// which provides exact checks and Merkle non-membership proofs.
#[deprecated(
    since = "0.2.0",
    note = "Use RevocationRegistry for exact checks and non-membership proofs. \
            RevocationFilter has false positives and cannot generate proofs."
)]
pub struct RevocationFilter {
    inner: Mutex<SendSafeFilter>,
    count: AtomicU64,
}

#[allow(deprecated)]
impl RevocationFilter {
    /// Create a new empty revocation filter with default parameters.
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(
                ScalableCuckooFilterBuilder::new()
                    .initial_capacity(DEFAULT_INITIAL_CAPACITY)
                    .false_positive_probability(DEFAULT_FALSE_POSITIVE_RATE)
                    .rng(SendRng(StdRng::from_os_rng()))
                    .finish(),
            ),
            count: AtomicU64::new(0),
        }
    }

    /// Create a revocation filter with custom capacity and FPR.
    pub fn with_capacity(capacity: usize, false_positive_rate: f64) -> Self {
        Self {
            inner: Mutex::new(
                ScalableCuckooFilterBuilder::new()
                    .initial_capacity(capacity)
                    .false_positive_probability(false_positive_rate)
                    .rng(SendRng(StdRng::from_os_rng()))
                    .finish(),
            ),
            count: AtomicU64::new(0),
        }
    }

    /// Mark a token nonce as revoked.
    ///
    /// After this call, `is_revoked(nonce)` will return `true` for this nonce.
    pub fn revoke(&self, nonce: &str) {
        let mut filter = self.inner.lock().unwrap();
        filter.insert(nonce);
        self.count.fetch_add(1, Ordering::Relaxed);
    }

    /// Check whether a token nonce has been revoked.
    ///
    /// Returns `true` if the nonce is (probably) in the filter.
    /// False positive rate is controlled by the filter's FPR parameter.
    /// False negatives are impossible — if a nonce was revoked, this returns `true`.
    pub fn is_revoked(&self, nonce: &str) -> bool {
        let filter = self.inner.lock().unwrap();
        filter.contains(nonce)
    }

    /// Number of nonces that have been revoked (approximate — counts insertions).
    pub fn revoked_count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }

    /// Serialize the filter to bytes for persistence.
    pub fn to_bytes(&self) -> Result<Vec<u8>, rmp_serde::encode::Error> {
        let filter = self.inner.lock().unwrap();
        let snapshot = RevocationSnapshot {
            filter: filter.clone(),
            count: self.count.load(Ordering::Relaxed),
        };
        rmp_serde::to_vec(&snapshot)
    }

    /// Restore a filter from serialized bytes.
    pub fn from_bytes(data: &[u8]) -> Result<Self, rmp_serde::decode::Error> {
        let snapshot: RevocationSnapshot = rmp_serde::from_slice(data)?;
        Ok(Self {
            inner: Mutex::new(snapshot.filter),
            count: AtomicU64::new(snapshot.count),
        })
    }
}

#[allow(deprecated)]
impl Default for RevocationFilter {
    fn default() -> Self {
        Self::new()
    }
}

/// Serializable snapshot of the revocation filter state.
#[derive(Serialize, Deserialize)]
struct RevocationSnapshot {
    filter: SendSafeFilter,
    count: u64,
}

// =============================================================================
// RevocationRegistry — Strategy Pattern (exact set + Merkle tree)
// =============================================================================

/// Errors from the revocation registry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RevocationError {
    /// The token is already revoked; cannot produce a non-membership proof.
    TokenRevoked,
    /// The tree is in an inconsistent state.
    InternalError(String),
}

impl std::fmt::Display for RevocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TokenRevoked => write!(f, "token is revoked"),
            Self::InternalError(msg) => write!(f, "internal error: {msg}"),
        }
    }
}

impl std::error::Error for RevocationError {}

/// A Merkle membership proof for a single element in the sorted revocation tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembershipProof {
    /// The leaf hash whose membership is proved.
    pub leaf_hash: [u8; 32],
    /// Index of the element in the sorted leaf list.
    pub index: usize,
    /// Sibling hashes along the path from leaf to root (bottom-up).
    pub siblings: Vec<[u8; 32]>,
}

/// A non-membership proof: demonstrates that a token ID is NOT in the revocation set.
///
/// Uses the adjacent-neighbor technique: shows two consecutive leaves in the sorted
/// tree that bracket the absent value, plus Merkle membership proofs for each
/// neighbor proving they ARE in the tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The leaf hash of the absent token.
    pub absent_hash: [u8; 32],
    /// The leaf just before the absent one (if any).
    pub left_neighbor: Option<[u8; 32]>,
    /// The leaf just after the absent one (if any).
    pub right_neighbor: Option<[u8; 32]>,
    /// Merkle membership proof for the left neighbor.
    pub left_proof: Option<MembershipProof>,
    /// Merkle membership proof for the right neighbor.
    pub right_proof: Option<MembershipProof>,
    /// Root of the revocation tree at proof generation time.
    pub root: [u8; 32],
}

/// An attested (signed) root from the revocation registry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedRevocationRoot {
    /// The Merkle root of the sorted revocation tree.
    pub merkle_root: [u8; 32],
    /// The number of revoked tokens at the time of attestation.
    pub count: u64,
    /// Unix timestamp (seconds) when this root was signed.
    pub timestamp: i64,
    /// The provider's public key that signed this root.
    pub signer: [u8; 32],
    /// Ed25519 signature over `signing_message()`.
    #[serde(with = "sig_bytes")]
    pub signature: [u8; 64],
}

/// Serde helper for `[u8; 64]` since serde's derive doesn't support arrays > 32.
mod sig_bytes {
    use serde::de::{self, Visitor};
    use serde::{Deserializer, Serializer};
    use std::fmt;

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        ser.serialize_bytes(bytes)
    }

    struct ByteArrayVisitor;

    impl<'de> Visitor<'de> for ByteArrayVisitor {
        type Value = [u8; 64];

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "64 bytes")
        }

        fn visit_bytes<E: de::Error>(self, v: &[u8]) -> Result<Self::Value, E> {
            v.try_into()
                .map_err(|_| E::custom(format!("expected 64 bytes, got {}", v.len())))
        }

        fn visit_seq<A: de::SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
            let mut arr = [0u8; 64];
            for (i, byte) in arr.iter_mut().enumerate() {
                *byte = seq
                    .next_element()?
                    .ok_or_else(|| de::Error::invalid_length(i, &self))?;
            }
            Ok(arr)
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        de.deserialize_bytes(ByteArrayVisitor)
    }
}

impl AttestedRevocationRoot {
    /// Compute the message that was (or should be) signed.
    pub fn signing_message(merkle_root: &[u8; 32], count: u64, timestamp: i64) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-token attested-revocation-root v1");
        hasher.update(merkle_root);
        hasher.update(&count.to_le_bytes());
        hasher.update(&timestamp.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// A sorted Merkle tree over revoked token leaf hashes.
///
/// Supports O(log n) membership proofs and non-membership proofs via
/// the adjacent-neighbor technique (same approach as `cell/src/nullifier_set.rs`).
#[derive(Clone, Debug)]
struct SortedRevocationTree {
    /// Sorted list of leaf hashes (each is blake3 of the token ID).
    leaves: Vec<[u8; 32]>,
}

impl SortedRevocationTree {
    fn new() -> Self {
        Self { leaves: Vec::new() }
    }

    /// Insert a leaf hash, maintaining sorted order. Returns false if already present.
    fn insert(&mut self, leaf_hash: [u8; 32]) -> bool {
        match self.leaves.binary_search(&leaf_hash) {
            Ok(_) => false, // duplicate
            Err(idx) => {
                self.leaves.insert(idx, leaf_hash);
                true
            }
        }
    }

    /// Check if a leaf hash is in the tree.
    fn contains(&self, leaf_hash: &[u8; 32]) -> bool {
        self.leaves.binary_search(leaf_hash).is_ok()
    }

    /// Compute the Merkle root of all leaves.
    fn root(&self) -> [u8; 32] {
        if self.leaves.is_empty() {
            return [0u8; 32];
        }
        let hashed_leaves: Vec<[u8; 32]> = self.leaves.iter().map(|l| Self::leaf_hash(l)).collect();
        Self::merkle_root_from_level(&hashed_leaves)
    }

    /// Generate a membership proof for the element at the given index.
    fn prove_membership(&self, index: usize) -> MembershipProof {
        let hashed_leaves: Vec<[u8; 32]> = self.leaves.iter().map(|l| Self::leaf_hash(l)).collect();
        let siblings = Self::merkle_path(&hashed_leaves, index);
        MembershipProof {
            leaf_hash: self.leaves[index],
            index,
            siblings,
        }
    }

    /// Generate a non-membership proof for a leaf hash that is NOT in the tree.
    fn prove_non_membership(&self, absent_hash: &[u8; 32]) -> Option<NonMembershipProof> {
        match self.leaves.binary_search(absent_hash) {
            Ok(_) => None, // IS in the tree
            Err(idx) => {
                let left_neighbor = if idx > 0 {
                    Some(self.leaves[idx - 1])
                } else {
                    None
                };
                let right_neighbor = if idx < self.leaves.len() {
                    Some(self.leaves[idx])
                } else {
                    None
                };
                let left_proof = if idx > 0 {
                    Some(self.prove_membership(idx - 1))
                } else {
                    None
                };
                let right_proof = if idx < self.leaves.len() {
                    Some(self.prove_membership(idx))
                } else {
                    None
                };
                Some(NonMembershipProof {
                    absent_hash: *absent_hash,
                    left_neighbor,
                    right_neighbor,
                    left_proof,
                    right_proof,
                    root: self.root(),
                })
            }
        }
    }

    /// Hash a leaf value for the Merkle tree.
    fn leaf_hash(data: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-revocation-leaf v1");
        hasher.update(data);
        *hasher.finalize().as_bytes()
    }

    /// Hash two children into a parent node.
    fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-revocation-node v1");
        hasher.update(left);
        hasher.update(right);
        *hasher.finalize().as_bytes()
    }

    /// Compute the Merkle root from a level of hashes.
    fn merkle_root_from_level(level: &[[u8; 32]]) -> [u8; 32] {
        if level.is_empty() {
            return [0u8; 32];
        }
        let mut current = level.to_vec();
        while current.len() > 1 {
            if current.len() % 2 != 0 {
                current.push([0u8; 32]);
            }
            let mut next = Vec::with_capacity(current.len() / 2);
            for chunk in current.chunks(2) {
                next.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current = next;
        }
        current[0]
    }

    /// Compute the Merkle path (sibling hashes from leaf to root) for a given index.
    fn merkle_path(hashed_leaves: &[[u8; 32]], index: usize) -> Vec<[u8; 32]> {
        if hashed_leaves.len() <= 1 {
            return vec![];
        }
        let mut siblings = Vec::new();
        let mut current_level = hashed_leaves.to_vec();
        let mut idx = index;

        while current_level.len() > 1 {
            if current_level.len() % 2 != 0 {
                current_level.push([0u8; 32]);
            }
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            siblings.push(current_level[sibling_idx]);

            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
            idx /= 2;
        }
        siblings
    }

    /// Verify a membership proof against a given root.
    pub fn verify_membership(proof: &MembershipProof, root: &[u8; 32]) -> bool {
        let mut current = Self::leaf_hash(&proof.leaf_hash);
        let mut idx = proof.index;
        for sibling in &proof.siblings {
            if idx % 2 == 0 {
                current = Self::node_hash(&current, sibling);
            } else {
                current = Self::node_hash(sibling, &current);
            }
            idx /= 2;
        }
        current == *root
    }

    /// Verify a non-membership proof against a given root.
    pub fn verify_non_membership(proof: &NonMembershipProof, root: &[u8; 32]) -> bool {
        if proof.root != *root {
            return false;
        }

        // Check ordering: left < absent < right.
        if let Some(left) = &proof.left_neighbor {
            if *left >= proof.absent_hash {
                return false;
            }
        }
        if let Some(right) = &proof.right_neighbor {
            if *right <= proof.absent_hash {
                return false;
            }
        }

        // Verify left neighbor membership proof.
        if let Some(left) = &proof.left_neighbor {
            match &proof.left_proof {
                Some(membership_proof) => {
                    if membership_proof.leaf_hash != *left {
                        return false;
                    }
                    if !Self::verify_membership(membership_proof, root) {
                        return false;
                    }
                }
                None => return false,
            }
        }

        // Verify right neighbor membership proof.
        if let Some(right) = &proof.right_neighbor {
            match &proof.right_proof {
                Some(membership_proof) => {
                    if membership_proof.leaf_hash != *right {
                        return false;
                    }
                    if !Self::verify_membership(membership_proof, root) {
                        return false;
                    }
                }
                None => return false,
            }
        }

        // Verify adjacency: left and right must be at consecutive indices.
        if let (Some(left_proof), Some(right_proof)) = (&proof.left_proof, &proof.right_proof) {
            if right_proof.index != left_proof.index + 1 {
                return false;
            }
        }

        true
    }

    /// Number of leaves.
    fn len(&self) -> usize {
        self.leaves.len()
    }
}

/// Hash a token ID to its canonical leaf representation for the revocation tree.
fn token_id_leaf_hash(token_id: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-token revocation-id v1");
    hasher.update(token_id.as_bytes());
    *hasher.finalize().as_bytes()
}

/// A service provider's revocation registry.
///
/// Maintains both an exact set (for the provider's own O(1) checks) and a sorted
/// Merkle tree (for generating non-membership proofs that users can present to
/// third parties offline).
///
/// # Thread Safety
///
/// The registry is **not** internally thread-safe. Wrap in `Arc<RwLock<_>>` or
/// `Arc<Mutex<_>>` for concurrent access from multiple tasks.
pub struct RevocationRegistry {
    /// Exact set of revoked token IDs — O(1) lookup, no false positives.
    revoked: HashSet<String>,
    /// Sorted Merkle tree — generates non-membership proofs for users.
    tree: SortedRevocationTree,
    /// Current attested root (signed by the provider). None until first `publish_root()`.
    attested_root: Option<AttestedRevocationRoot>,
}

impl std::fmt::Debug for RevocationRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RevocationRegistry")
            .field("revoked_count", &self.revoked.len())
            .field("tree_leaves", &self.tree.len())
            .field("has_attested_root", &self.attested_root.is_some())
            .finish()
    }
}

impl RevocationRegistry {
    /// Create a new empty revocation registry.
    pub fn new() -> Self {
        Self {
            revoked: HashSet::new(),
            tree: SortedRevocationTree::new(),
            attested_root: None,
        }
    }

    /// Provider revokes a token (updates both the exact set and the Merkle tree).
    ///
    /// Returns `true` if the token was newly revoked, `false` if already revoked.
    pub fn revoke(&mut self, token_id: &str) -> bool {
        if !self.revoked.insert(token_id.to_string()) {
            return false; // already revoked
        }
        let leaf = token_id_leaf_hash(token_id);
        self.tree.insert(leaf);
        true
    }

    /// Provider's own check — exact, O(1), no false positives.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked.contains(token_id)
    }

    /// Number of revoked tokens.
    pub fn revoked_count(&self) -> u64 {
        self.revoked.len() as u64
    }

    /// Get the current Merkle root of the revocation tree.
    pub fn current_root(&self) -> [u8; 32] {
        self.tree.root()
    }

    /// Get the current attested root (if one has been published).
    pub fn attested_root(&self) -> Option<&AttestedRevocationRoot> {
        self.attested_root.as_ref()
    }

    /// Sign and publish the current tree root.
    ///
    /// Call this periodically (e.g., after each batch of revocations) to make
    /// the current state available for non-membership proof verification.
    ///
    /// The `signing_key` should be the provider's Ed25519 signing key. The
    /// `signer_public_key` is the corresponding 32-byte public key bytes.
    pub fn publish_root(&mut self, signing_key: &[u8; 32], signer_public_key: &[u8; 32]) {
        let merkle_root = self.tree.root();
        let count = self.revoked.len() as u64;
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);

        let msg = AttestedRevocationRoot::signing_message(&merkle_root, count, timestamp);

        // Sign using ed25519-dalek compatible signing.
        let sk = ed25519_dalek::SigningKey::from_bytes(signing_key);
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg);

        self.attested_root = Some(AttestedRevocationRoot {
            merkle_root,
            count,
            timestamp,
            signer: *signer_public_key,
            signature: sig.to_bytes(),
        });
    }

    /// Generate a non-membership proof for a user's token.
    ///
    /// Returns `Ok(proof)` if the token is NOT revoked, allowing the user to
    /// present this proof to third parties as evidence of non-revocation.
    ///
    /// Returns `Err(RevocationError::TokenRevoked)` if the token IS revoked.
    pub fn prove_non_revocation(
        &self,
        token_id: &str,
    ) -> Result<NonMembershipProof, RevocationError> {
        if self.revoked.contains(token_id) {
            return Err(RevocationError::TokenRevoked);
        }
        let leaf = token_id_leaf_hash(token_id);
        self.tree.prove_non_membership(&leaf).ok_or_else(|| {
            RevocationError::InternalError(
                "tree contains leaf hash but exact set does not".to_string(),
            )
        })
    }

    /// Verify a non-membership proof against a known root.
    ///
    /// This is a static method so that any party (not just the provider) can
    /// verify proofs offline.
    pub fn verify_non_membership_proof(proof: &NonMembershipProof, root: &[u8; 32]) -> bool {
        SortedRevocationTree::verify_non_membership(proof, root)
    }

    /// Compute the canonical leaf hash for a token ID.
    ///
    /// Useful for clients that want to construct a `RequestNonMembershipProof`
    /// message without revealing the raw token ID (privacy preservation).
    pub fn token_id_to_leaf(token_id: &str) -> [u8; 32] {
        token_id_leaf_hash(token_id)
    }

    /// Serialize the registry for persistence.
    pub fn to_bytes(&self) -> Vec<u8> {
        let snapshot = RegistrySnapshot {
            revoked: self.revoked.iter().cloned().collect(),
            attested_root: self.attested_root.clone(),
        };
        rmp_serde::to_vec(&snapshot).expect("registry serialization should not fail")
    }

    /// Restore a registry from serialized bytes.
    pub fn from_bytes(data: &[u8]) -> Result<Self, rmp_serde::decode::Error> {
        let snapshot: RegistrySnapshot = rmp_serde::from_slice(data)?;
        let mut registry = Self::new();
        for token_id in &snapshot.revoked {
            registry.revoked.insert(token_id.clone());
            let leaf = token_id_leaf_hash(token_id);
            registry.tree.insert(leaf);
        }
        registry.attested_root = snapshot.attested_root;
        Ok(registry)
    }
}

impl Default for RevocationRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Serializable snapshot of the registry state.
#[derive(Serialize, Deserialize)]
struct RegistrySnapshot {
    revoked: Vec<String>,
    attested_root: Option<AttestedRevocationRoot>,
}

/// Optional high-throughput pre-filter wrapper.
///
/// Wraps a `RevocationRegistry` with a cuckoo filter for fast pre-checks.
/// Use this in deployments with extremely high query rates where even the
/// O(1) HashSet lookup is a bottleneck due to lock contention.
///
/// **Not a ground truth.** The cuckoo filter has false positives. Always
/// fall through to `RevocationRegistry::is_revoked()` on positive results.
#[deprecated(note = "Use RevocationRegistry directly; this adds complexity without correctness")]
pub struct RevocationPrefilter {
    /// The fast-path cuckoo filter.
    #[allow(deprecated)]
    pub filter: RevocationFilter,
    /// The authoritative registry.
    pub registry: RevocationRegistry,
}

#[allow(deprecated)]
impl RevocationPrefilter {
    /// Create a new pre-filter backed by a registry.
    pub fn new() -> Self {
        Self {
            filter: RevocationFilter::new(),
            registry: RevocationRegistry::new(),
        }
    }

    /// Revoke a token (updates both filter and registry).
    pub fn revoke(&mut self, token_id: &str) {
        self.filter.revoke(token_id);
        self.registry.revoke(token_id);
    }

    /// Fast pre-check (may have false positives).
    /// On `true`, caller should confirm with `registry.is_revoked()`.
    pub fn maybe_revoked(&self, token_id: &str) -> bool {
        self.filter.is_revoked(token_id)
    }

    /// Exact check via registry.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.registry.is_revoked(token_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_registry_is_empty() {
        let registry = RevocationRegistry::new();
        assert_eq!(registry.revoked_count(), 0);
        assert!(!registry.is_revoked("nonce-123"));
    }

    #[test]
    fn test_revoke_and_check() {
        let mut registry = RevocationRegistry::new();
        registry.revoke("nonce-abc");
        assert!(registry.is_revoked("nonce-abc"));
        assert!(!registry.is_revoked("nonce-xyz"));
        assert_eq!(registry.revoked_count(), 1);
    }

    #[test]
    fn test_multiple_revocations() {
        let mut registry = RevocationRegistry::new();
        for i in 0..100 {
            registry.revoke(&format!("nonce-{i}"));
        }
        assert_eq!(registry.revoked_count(), 100);

        for i in 0..100 {
            assert!(registry.is_revoked(&format!("nonce-{i}")));
        }
    }

    #[test]
    fn test_serialize_deserialize_roundtrip() {
        let mut registry = RevocationRegistry::new();
        registry.revoke("revoked-1");
        registry.revoke("revoked-2");
        registry.revoke("revoked-3");

        let bytes = registry.to_bytes();
        let restored = RevocationRegistry::from_bytes(&bytes).expect("deserialization failed");

        assert_eq!(restored.revoked_count(), 3);
        assert!(restored.is_revoked("revoked-1"));
        assert!(restored.is_revoked("revoked-2"));
        assert!(restored.is_revoked("revoked-3"));
        assert!(!restored.is_revoked("not-revoked"));
    }

    #[test]
    fn test_non_membership_proof() {
        let mut registry = RevocationRegistry::new();
        registry.revoke("revoked-token");
        // Non-revoked token should produce a valid proof
        let proof = registry.prove_non_revocation("valid-token");
        assert!(proof.is_ok(), "should produce proof for non-revoked token");
        // Revoked token should fail proof generation
        let proof = registry.prove_non_revocation("revoked-token");
        assert!(proof.is_err(), "should not produce proof for revoked token");
    }

    #[test]
    fn test_registry_root_changes_on_revocation() {
        let mut registry = RevocationRegistry::new();
        let root_before = registry.current_root();
        registry.revoke("some-token");
        let root_after = registry.current_root();
        assert_ne!(root_before, root_after, "root should change after revocation");
    }

    // =========================================================================
    // RevocationRegistry tests
    // =========================================================================

    #[test]
    fn registry_new_is_empty() {
        let reg = RevocationRegistry::new();
        assert_eq!(reg.revoked_count(), 0);
        assert!(!reg.is_revoked("anything"));
        assert!(reg.attested_root().is_none());
    }

    #[test]
    fn registry_revoke_and_is_revoked_exact() {
        let mut reg = RevocationRegistry::new();
        assert!(reg.revoke("tok-1"));
        assert!(reg.is_revoked("tok-1"));
        assert!(!reg.is_revoked("tok-2"));
        assert_eq!(reg.revoked_count(), 1);
    }

    #[test]
    fn registry_revoke_duplicate_returns_false() {
        let mut reg = RevocationRegistry::new();
        assert!(reg.revoke("tok-1"));
        assert!(!reg.revoke("tok-1"));
        assert_eq!(reg.revoked_count(), 1);
    }

    #[test]
    fn registry_root_changes_on_revoke() {
        let mut reg = RevocationRegistry::new();
        let root0 = reg.current_root();
        reg.revoke("tok-1");
        let root1 = reg.current_root();
        assert_ne!(root0, root1);
        reg.revoke("tok-2");
        let root2 = reg.current_root();
        assert_ne!(root1, root2);
    }

    #[test]
    fn registry_prove_non_revocation_succeeds_for_non_revoked() {
        let mut reg = RevocationRegistry::new();
        reg.revoke("tok-a");
        reg.revoke("tok-c");

        // tok-b is NOT revoked
        let proof = reg.prove_non_revocation("tok-b").unwrap();
        let root = reg.current_root();
        assert!(RevocationRegistry::verify_non_membership_proof(
            &proof, &root
        ));
    }

    #[test]
    fn registry_prove_non_revocation_fails_for_revoked() {
        let mut reg = RevocationRegistry::new();
        reg.revoke("tok-1");

        let result = reg.prove_non_revocation("tok-1");
        assert_eq!(result, Err(RevocationError::TokenRevoked));
    }

    #[test]
    fn registry_prove_non_revocation_empty_tree() {
        let reg = RevocationRegistry::new();
        // With empty tree, any token should produce a valid proof.
        let proof = reg.prove_non_revocation("tok-x").unwrap();
        let root = reg.current_root();
        assert!(RevocationRegistry::verify_non_membership_proof(
            &proof, &root
        ));
    }

    #[test]
    fn registry_proof_invalid_against_wrong_root() {
        let mut reg = RevocationRegistry::new();
        reg.revoke("tok-a");

        let proof = reg.prove_non_revocation("tok-b").unwrap();

        // Tamper: verify against a different root
        let wrong_root = [0xffu8; 32];
        assert!(!RevocationRegistry::verify_non_membership_proof(
            &proof,
            &wrong_root
        ));
    }

    #[test]
    fn registry_publish_and_retrieve_attested_root() {
        let mut reg = RevocationRegistry::new();
        reg.revoke("tok-1");

        // Generate a test keypair
        let sk_bytes = [42u8; 32];
        let sk = ed25519_dalek::SigningKey::from_bytes(&sk_bytes);
        let pk_bytes = sk.verifying_key().to_bytes();

        reg.publish_root(&sk_bytes, &pk_bytes);

        let attested = reg.attested_root().unwrap();
        assert_eq!(attested.merkle_root, reg.current_root());
        assert_eq!(attested.count, 1);
        assert_eq!(attested.signer, pk_bytes);

        // Verify the signature
        let msg = AttestedRevocationRoot::signing_message(
            &attested.merkle_root,
            attested.count,
            attested.timestamp,
        );
        use ed25519_dalek::Verifier;
        let vk = sk.verifying_key();
        let sig = ed25519_dalek::Signature::from_bytes(&attested.signature);
        assert!(vk.verify(&msg, &sig).is_ok());
    }

    #[test]
    fn registry_serialize_roundtrip() {
        let mut reg = RevocationRegistry::new();
        reg.revoke("alpha");
        reg.revoke("beta");
        reg.revoke("gamma");

        let bytes = reg.to_bytes();
        let restored = RevocationRegistry::from_bytes(&bytes).unwrap();

        assert_eq!(restored.revoked_count(), 3);
        assert!(restored.is_revoked("alpha"));
        assert!(restored.is_revoked("beta"));
        assert!(restored.is_revoked("gamma"));
        assert!(!restored.is_revoked("delta"));
        assert_eq!(restored.current_root(), reg.current_root());
    }

    #[test]
    fn registry_many_revocations_proof_still_valid() {
        let mut reg = RevocationRegistry::new();
        for i in 0..50 {
            reg.revoke(&format!("tok-{i:04}"));
        }

        // Prove non-membership for a token not in the set
        let proof = reg.prove_non_revocation("tok-9999").unwrap();
        let root = reg.current_root();
        assert!(RevocationRegistry::verify_non_membership_proof(
            &proof, &root
        ));

        // All revoked tokens should fail proof generation
        for i in 0..50 {
            assert_eq!(
                reg.prove_non_revocation(&format!("tok-{i:04}")),
                Err(RevocationError::TokenRevoked)
            );
        }
    }

    #[test]
    fn registry_token_id_to_leaf_is_deterministic() {
        let h1 = RevocationRegistry::token_id_to_leaf("tok-abc");
        let h2 = RevocationRegistry::token_id_to_leaf("tok-abc");
        assert_eq!(h1, h2);

        let h3 = RevocationRegistry::token_id_to_leaf("tok-xyz");
        assert_ne!(h1, h3);
    }
}
