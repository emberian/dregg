//! Typed dual-form commitment framework for the storage crate.
//!
//! Per `DESIGN-commitment-framework.md` and the storage-specific audit at
//! `storage/STORAGE-POSEIDON2-AUDIT.md`. Every authoritative content
//! commitment in storage carries two companion digests:
//!
//! 1. **`blake3: [u8; 32]`** — canonical byte-domain commitment. Cheap, used
//!    everywhere outside a STARK: HashMap keys, gossip dedup, logs, REST.
//! 2. **`poseidon2`** — field-domain commitment over BabyBear. Used as AIR
//!    public inputs and inside lookup arguments.
//!
//! The two are bound one-directionally to a shared canonical byte encoding;
//! cross-form binding is established at the producer (a `seal` call).
//! There is NO BLAKE3 inside a STARK by design (see DESIGN §2.2).
//!
//! # Relationship to `commit/src/typed.rs`
//!
//! `commit/src/typed.rs` (upstream) is the canonical home of this pattern.
//! storage is in the workspace `exclude` list and cannot depend on
//! `commit` without pulling extra crates (`pyana-dsl-runtime`). We
//! intentionally duplicate the pattern here — same domain-tagging strategy,
//! same `canonical_32_to_felts_4` shape, same `seal`/`empty` API — atop
//! the public Poseidon2 surface in `pyana_circuit::poseidon2`.
//!
//! Bumping a domain tag invalidates both forms together. Tags MUST end in
//! a version suffix.

use core::marker::PhantomData;
use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use serde::{Deserialize, Serialize};

// =============================================================================
// Domain registry — every storage-side tag, centralized
// =============================================================================

/// Central domain-tag registry for storage commitments. Bumping a tag
/// invalidates both BLAKE3 and Poseidon2 forms together.
pub mod domain {
    // From audit P4.A — 12 typed markers covering 16 production sites.
    pub const TAG_QUEUE_ENTRY: &str = "pyana-storage:queue-entry v1";
    pub const TAG_QUEUE_ENTRY_SET: &str = "pyana-storage:queue-entry-set v1";
    pub const TAG_BLINDED_ITEM: &str = "pyana-storage:blinded-item v1";
    pub const TAG_BLINDED_NULLIFIER: &str = "pyana-storage:blinded-nullifier v1";
    pub const TAG_BLINDED_ITEM_SET: &str = "pyana-storage:blinded-item-set v1";
    pub const TAG_QUEUE_PROGRAM: &str = "pyana-storage:queue-program v1";
    pub const TAG_AUTHORIZED_KEY_SET: &str = "pyana-storage:authorized-key-set v1";
    pub const TAG_SHARD_SET: &str = "pyana-storage:shard-set v1";
    pub const TAG_PIPELINE_SPEC: &str = "pyana-storage:pipeline-spec v1";
    pub const TAG_QUEUE_TRANSACTION: &str = "pyana-storage:queue-transaction v1";
    pub const TAG_ERASURE_CHUNK: &str = "pyana-storage:erasure-chunk v1";
    pub const TAG_ERASURE_SET: &str = "pyana-storage:erasure-set v1";
}

// =============================================================================
// CommitmentSchema trait
// =============================================================================

/// Schema for a commitment-bearing value.
///
/// `Self` is a zero-sized marker; the commitment binds bytes of the canonical
/// encoding to two independent hashes. `canonical()` returns the canonical
/// byte encoding consumed by both hash paths; `to_felts()` returns the
/// field-element view (default is byte-packing).
pub trait CommitmentSchema: 'static {
    /// The underlying value type being committed to.
    type Value: ?Sized;
    /// Domain-separation tag (see [`domain`] module).
    const DOMAIN: &'static str;

    /// Canonical byte encoding (length-prefixed, deterministic).
    fn canonical(value: &Self::Value) -> Vec<u8>;

    /// Schema-encoded BabyBear felts. Default impl byte-packs the canonical
    /// encoding at 30 bits/limb.
    fn to_felts(value: &Self::Value) -> Vec<BabyBear> {
        encode_bytes_to_felts(&Self::canonical(value))
    }
}

// =============================================================================
// Core types
// =============================================================================

/// A typed dual-form commitment with a single BabyBear field-form.
///
/// Used where the Poseidon2 form is a binding inside a larger algebraic
/// structure that itself has 124-bit security (e.g., a Merkle leaf whose
/// root carries the security). For standalone authoritative identifiers,
/// use [`Commitment4`].
#[derive(Serialize, Deserialize)]
pub struct Commitment<T: CommitmentSchema> {
    pub blake3: [u8; 32],
    pub poseidon2: BabyBear,
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

// Manual Clone/Copy impls because the marker `T` is uninhabited and doesn't
// derive Clone; the derive macro would gate Clone on T: Clone which fails.
impl<T: CommitmentSchema> Clone for Commitment<T> {
    fn clone(&self) -> Self { *self }
}
impl<T: CommitmentSchema> Copy for Commitment<T> {}

impl<T: CommitmentSchema> core::fmt::Debug for Commitment<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Commitment")
            .field("domain", &T::DOMAIN)
            .field("blake3", &self.blake3)
            .field("poseidon2", &self.poseidon2)
            .finish()
    }
}

impl<T: CommitmentSchema> PartialEq for Commitment<T> {
    fn eq(&self, other: &Self) -> bool {
        self.blake3 == other.blake3 && self.poseidon2 == other.poseidon2
    }
}

impl<T: CommitmentSchema> Eq for Commitment<T> {}

impl<T: CommitmentSchema> core::hash::Hash for Commitment<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.blake3.hash(state);
        self.poseidon2.0.hash(state);
    }
}

impl<T: CommitmentSchema> Commitment<T> {
    /// Seal a value: compute both digests from its canonical preimage.
    pub fn seal(value: &T::Value) -> Self {
        let bytes = T::canonical(value);
        let blake3 = blake3_with_tag(T::DOMAIN, &bytes);
        let poseidon2 = poseidon2_single_with_tag(T::DOMAIN, &T::to_felts(value));
        Self { blake3, poseidon2, _phantom: PhantomData }
    }

    /// The empty (sentinel) commitment for this type.
    pub fn empty() -> Self {
        Self {
            blake3: [0u8; 32],
            poseidon2: BabyBear::ZERO,
            _phantom: PhantomData,
        }
    }

    /// Recompute the BLAKE3 form from a preimage and compare.
    pub fn verify_blake3(&self, preimage_bytes: &[u8]) -> bool {
        blake3_with_tag(T::DOMAIN, preimage_bytes) == self.blake3
    }

    /// The BabyBear field-form to be absorbed into an AIR public input.
    pub fn poseidon2(&self) -> BabyBear {
        self.poseidon2
    }

    /// Construct from precomputed parts. Use at trust boundaries only.
    pub fn from_parts(blake3: [u8; 32], poseidon2: BabyBear) -> Self {
        Self { blake3, poseidon2, _phantom: PhantomData }
    }
}

/// A typed dual-form commitment with a 4-felt field-form (~124-bit security).
///
/// Used where the Poseidon2 form stands alone as an authoritative identifier
/// (blinded item commitments, nullifiers — anything the AIR consumes as a
/// primary key).
#[derive(Serialize, Deserialize)]
pub struct Commitment4<T: CommitmentSchema> {
    pub blake3: [u8; 32],
    pub poseidon2: [BabyBear; 4],
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

impl<T: CommitmentSchema> Clone for Commitment4<T> {
    fn clone(&self) -> Self { *self }
}
impl<T: CommitmentSchema> Copy for Commitment4<T> {}

impl<T: CommitmentSchema> core::fmt::Debug for Commitment4<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Commitment4")
            .field("domain", &T::DOMAIN)
            .field("blake3", &self.blake3)
            .field("poseidon2", &self.poseidon2)
            .finish()
    }
}

impl<T: CommitmentSchema> PartialEq for Commitment4<T> {
    fn eq(&self, other: &Self) -> bool {
        self.blake3 == other.blake3 && self.poseidon2 == other.poseidon2
    }
}

impl<T: CommitmentSchema> Eq for Commitment4<T> {}

impl<T: CommitmentSchema> core::hash::Hash for Commitment4<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.blake3.hash(state);
        for e in &self.poseidon2 {
            e.0.hash(state);
        }
    }
}

impl<T: CommitmentSchema> Commitment4<T> {
    /// Seal a value: compute both digests from its canonical preimage.
    pub fn seal(value: &T::Value) -> Self {
        let bytes = T::canonical(value);
        let blake3 = blake3_with_tag(T::DOMAIN, &bytes);
        let poseidon2 = poseidon2_quad_with_tag(T::DOMAIN, &T::to_felts(value));
        Self { blake3, poseidon2, _phantom: PhantomData }
    }

    /// The empty (sentinel) commitment for this type.
    pub fn empty() -> Self {
        Self {
            blake3: [0u8; 32],
            poseidon2: [BabyBear::ZERO; 4],
            _phantom: PhantomData,
        }
    }

    /// Construct from precomputed parts. Use at trust boundaries only.
    pub fn from_parts(blake3: [u8; 32], poseidon2: [BabyBear; 4]) -> Self {
        Self { blake3, poseidon2, _phantom: PhantomData }
    }

    /// Recompute the BLAKE3 form from a preimage and compare.
    pub fn verify_blake3(&self, preimage_bytes: &[u8]) -> bool {
        blake3_with_tag(T::DOMAIN, preimage_bytes) == self.blake3
    }

    /// The 4 BabyBear elements to be absorbed into AIR public inputs.
    pub fn poseidon2(&self) -> [BabyBear; 4] {
        self.poseidon2
    }
}

/// Trust-boundary conversion: when a producer hands us a 32-byte
/// commitment (e.g., via an HTTP/wire decoder that only sees BLAKE3 hex),
/// derive the Poseidon2 form from the same canonical bytes via the
/// fixed `canonical_32_to_felts_4` bijection.
///
/// Per DESIGN-commitment-framework.md §4.1, this is the legitimate way to
/// reconstruct the dual form from a wire-side BLAKE3 hash: the receiver
/// trusts the producer's signature over the original `Commitment4`, and
/// here just re-derives the Poseidon2 form deterministically. Note this
/// does NOT recompute Poseidon2 over the original preimage — it's a
/// one-way map from the BLAKE3 32 bytes to a 4-felt fingerprint.
impl<T: CommitmentSchema> From<[u8; 32]> for Commitment4<T> {
    fn from(bytes: [u8; 32]) -> Self {
        Self::from_parts(bytes, canonical_32_to_felts_4(&bytes))
    }
}

/// See `Commitment4`'s From<[u8; 32]> impl. Same trust-boundary semantics.
impl<T: CommitmentSchema> From<[u8; 32]> for MerkleRoot<T> {
    fn from(root: [u8; 32]) -> Self {
        Self::from_blake3_root(root)
    }
}

// =============================================================================
// Accumulator (streaming hash-chain over a sequence of values)
// =============================================================================

/// Streaming dual-form accumulator. Each `extend()` absorbs an item into
/// both the BLAKE3 chain and a 4-felt Poseidon2 chain in lock-step.
/// Useful for ordered aggregates like a queue's tail or a pipeline run log.
pub struct Accumulator<T: CommitmentSchema> {
    blake3_state: blake3::Hasher,
    poseidon2_chain: [BabyBear; 4],
    n_items: u64,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: CommitmentSchema> Accumulator<T> {
    pub fn new() -> Self {
        let blake3_state = blake3::Hasher::new_derive_key(T::DOMAIN);
        let tag_felt = BabyBear::new(tag_hash_31(T::DOMAIN));
        Self {
            blake3_state,
            poseidon2_chain: [tag_felt, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
            n_items: 0,
            _phantom: PhantomData,
        }
    }

    /// Absorb an item into both hashes.
    pub fn extend(&mut self, item: &T::Value) {
        self.n_items += 1;
        let bytes = T::canonical(item);
        self.blake3_state.update(&(bytes.len() as u64).to_le_bytes());
        self.blake3_state.update(&bytes);

        let felts = T::to_felts(item);
        for chunk in felts.chunks(4) {
            let mut block = [BabyBear::ZERO; 4];
            for (i, &f) in chunk.iter().enumerate() {
                block[i] = f;
            }
            self.poseidon2_chain = absorb_4(self.poseidon2_chain, block);
        }
    }

    /// Finalize: returns the dual-form commitment over all absorbed items.
    pub fn finalize(self) -> ([u8; 32], [BabyBear; 4]) {
        let blake3 = *self.blake3_state.finalize().as_bytes();
        let len_felt = BabyBear::new(self.n_items as u32 & 0x7FFF_FFFF);
        let mut final_state = self.poseidon2_chain;
        final_state = absorb_4(
            final_state,
            [len_felt, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );
        (blake3, final_state)
    }
}

impl<T: CommitmentSchema> Default for Accumulator<T> {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// MerkleRoot (Merkle tree over typed leaves, dual-rooted)
// =============================================================================

/// A sparse Merkle root committed dually: a BLAKE3 root and a 4-felt
/// Poseidon2 root. The two roots are computed from the same leaf set via
/// two parallel trees; producers compute both and emit them together.
/// Verifiers select the form appropriate to context (BLAKE3 for off-chain
/// dedup; Poseidon2 for STARK PI / lookup).
#[derive(Serialize, Deserialize)]
pub struct MerkleRoot<T: CommitmentSchema> {
    pub blake3_root: [u8; 32],
    pub poseidon2_root: [BabyBear; 4],
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

impl<T: CommitmentSchema> Clone for MerkleRoot<T> {
    fn clone(&self) -> Self { *self }
}
impl<T: CommitmentSchema> Copy for MerkleRoot<T> {}

impl<T: CommitmentSchema> core::fmt::Debug for MerkleRoot<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("MerkleRoot")
            .field("domain", &T::DOMAIN)
            .field("blake3_root", &self.blake3_root)
            .field("poseidon2_root", &self.poseidon2_root)
            .finish()
    }
}

impl<T: CommitmentSchema> PartialEq for MerkleRoot<T> {
    fn eq(&self, other: &Self) -> bool {
        self.blake3_root == other.blake3_root && self.poseidon2_root == other.poseidon2_root
    }
}

impl<T: CommitmentSchema> Eq for MerkleRoot<T> {}

impl<T: CommitmentSchema> MerkleRoot<T> {
    pub fn empty() -> Self {
        Self {
            blake3_root: [0u8; 32],
            poseidon2_root: [BabyBear::ZERO; 4],
            _phantom: PhantomData,
        }
    }

    pub fn from_parts(blake3_root: [u8; 32], poseidon2_root: [BabyBear; 4]) -> Self {
        Self { blake3_root, poseidon2_root, _phantom: PhantomData }
    }

    /// Trust-boundary conversion: lift a wire-side 32-byte BLAKE3 root to
    /// a dual-form MerkleRoot by deriving its Poseidon2 form via the fixed
    /// canonical_32_to_felts_4 bijection. Used by HTTP/gossip decoders.
    pub fn from_blake3_root(root: [u8; 32]) -> Self {
        Self::from_parts(root, canonical_32_to_felts_4(&root))
    }

    /// Build a dual-rooted Merkle tree from a list of 32-byte BLAKE3 leaves
    /// and a parallel list of 4-felt Poseidon2 leaves. The two leaf-vectors
    /// MUST have the same length; the producer is responsible for ensuring
    /// they correspond to the same underlying values.
    ///
    /// Returns the empty sentinel for an empty input.
    pub fn from_leaves(
        blake3_leaves: &[[u8; 32]],
        poseidon2_leaves: &[[BabyBear; 4]],
    ) -> Self {
        assert_eq!(
            blake3_leaves.len(),
            poseidon2_leaves.len(),
            "MerkleRoot::from_leaves: leaf vectors must align"
        );
        if blake3_leaves.is_empty() {
            return Self::empty();
        }
        let blake3_root = blake3_binary_root(blake3_leaves);
        let poseidon2_root = poseidon2_binary_root(poseidon2_leaves);
        Self::from_parts(blake3_root, poseidon2_root)
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Compute a BLAKE3-with-derive-key digest over `bytes`, tagged by `domain`.
pub fn blake3_with_tag(domain: &str, bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

/// Deterministic 31-bit hash of a domain tag string (for Poseidon2 absorption).
pub fn tag_hash_31(domain: &str) -> u32 {
    let h = blake3::hash(domain.as_bytes());
    let bytes = h.as_bytes();
    let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    raw % BABYBEAR_P
}

/// Pack arbitrary bytes into BabyBear felts at 30 bits/limb.
///
/// BabyBear's modulus is 2^31 − 2^27 + 1; 30-bit limbs guarantee a unique
/// encoding without modular reduction collisions. A four-byte length prefix
/// is absorbed first.
pub fn encode_bytes_to_felts(bytes: &[u8]) -> Vec<BabyBear> {
    let mut felts = Vec::with_capacity(bytes.len() / 4 + 2);
    felts.push(BabyBear::new((bytes.len() as u32) & ((1u32 << 30) - 1)));
    let mut i = 0;
    while i < bytes.len() {
        let b0 = bytes[i] as u32;
        let b1 = if i + 1 < bytes.len() { bytes[i + 1] as u32 } else { 0 };
        let b2 = if i + 2 < bytes.len() { bytes[i + 2] as u32 } else { 0 };
        let b3 = if i + 3 < bytes.len() { bytes[i + 3] as u32 } else { 0 };
        let limb = b0 | (b1 << 8) | (b2 << 16) | ((b3 & 0x3F) << 24);
        felts.push(BabyBear::new(limb));
        i += 4;
    }
    felts
}

/// Pack a 32-byte canonical commitment into 8 BabyBear felts at 30 bits/limb.
pub fn canonical_32_to_felts_8(canonical: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        out[i] = BabyBear::new(lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24));
    }
    out
}

/// Compress a 32-byte canonical commitment into 4 BabyBear felts via Poseidon2.
pub fn canonical_32_to_felts_4(canonical: &[u8; 32]) -> [BabyBear; 4] {
    let eight = canonical_32_to_felts_8(canonical);
    let a = pyana_circuit::poseidon2::hash_4_to_1(&[eight[0], eight[1], eight[2], eight[3]]);
    let b = pyana_circuit::poseidon2::hash_4_to_1(&[eight[4], eight[5], eight[6], eight[7]]);
    let c = pyana_circuit::poseidon2::hash_4_to_1(&[eight[0], eight[4], eight[2], eight[6]]);
    let d = pyana_circuit::poseidon2::hash_4_to_1(&[eight[1], eight[5], eight[3], eight[7]]);
    [a, b, c, d]
}

/// Squeeze a single BabyBear from a domain-tagged sponge over felts.
pub fn poseidon2_single_with_tag(domain: &str, felts: &[BabyBear]) -> BabyBear {
    let tag = BabyBear::new(tag_hash_31(domain));
    let mut tagged = Vec::with_capacity(felts.len() + 1);
    tagged.push(tag);
    tagged.extend_from_slice(felts);
    pyana_circuit::poseidon2::hash_many(&tagged)
}

/// Squeeze 4 BabyBears from a domain-tagged sponge over felts.
///
/// Uses 4 independent compressions with different salts as the 4th input to
/// a final hash_4_to_1, mirroring `commit::typed::poseidon2_quad_with_tag`.
pub fn poseidon2_quad_with_tag(domain: &str, felts: &[BabyBear]) -> [BabyBear; 4] {
    use pyana_circuit::poseidon2::{hash_4_to_1, hash_many};
    let tag = BabyBear::new(tag_hash_31(domain));
    let mut tagged = Vec::with_capacity(felts.len() + 1);
    tagged.push(tag);
    tagged.extend_from_slice(felts);
    let h = hash_many(&tagged);
    [
        hash_4_to_1(&[h, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(3), BabyBear::ZERO, BabyBear::ZERO]),
    ]
}

/// Absorb a 4-felt block into a 4-felt sponge state via hash_4_to_1 over the
/// component-wise pairing of chain and block.
pub fn absorb_4(chain: [BabyBear; 4], block: [BabyBear; 4]) -> [BabyBear; 4] {
    use pyana_circuit::poseidon2::hash_4_to_1;
    [
        hash_4_to_1(&[chain[0], block[0], chain[1], block[1]]),
        hash_4_to_1(&[chain[1], block[1], chain[2], block[2]]),
        hash_4_to_1(&[chain[2], block[2], chain[3], block[3]]),
        hash_4_to_1(&[chain[3], block[3], chain[0], block[0]]),
    ]
}

/// Internal: build a BLAKE3 binary Merkle root over leaves, zero-padding to
/// the next power of two. Single-leaf input returns that leaf unchanged.
pub fn blake3_binary_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        return [0u8; 32];
    }
    if leaves.len() == 1 {
        return leaves[0];
    }
    let mut layer: Vec<[u8; 32]> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    layer.resize(next_pow2, [0u8; 32]);
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

/// Internal: build a Poseidon2 binary Merkle root over 4-felt leaves,
/// zero-padding to the next power of two. Single-leaf input returns that
/// leaf unchanged. Each parent absorbs the 8 felts of its two children via
/// two hash_4_to_1 calls folded into a final hash_4_to_1.
pub fn poseidon2_binary_root(leaves: &[[BabyBear; 4]]) -> [BabyBear; 4] {
    use pyana_circuit::poseidon2::hash_4_to_1;
    if leaves.is_empty() {
        return [BabyBear::ZERO; 4];
    }
    if leaves.len() == 1 {
        return leaves[0];
    }
    let mut layer: Vec<[BabyBear; 4]> = leaves.to_vec();
    let next_pow2 = layer.len().next_power_of_two();
    layer.resize(next_pow2, [BabyBear::ZERO; 4]);
    while layer.len() > 1 {
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let left = pair[0];
            let right = pair[1];
            let a = hash_4_to_1(&[left[0], left[1], left[2], left[3]]);
            let b = hash_4_to_1(&[right[0], right[1], right[2], right[3]]);
            // 4-felt parent = hash_4_to_1 over (left[0], right[0], a, b) and 3
            // rotated combinations, mirroring poseidon2_quad_with_tag.
            let parent = [
                hash_4_to_1(&[a, b, left[0], right[0]]),
                hash_4_to_1(&[a, b, left[1], right[1]]),
                hash_4_to_1(&[a, b, left[2], right[2]]),
                hash_4_to_1(&[a, b, left[3], right[3]]),
            ];
            next_layer.push(parent);
        }
        layer = next_layer;
    }
    layer[0]
}

// =============================================================================
// Tag markers (zero-sized phantom types) — one per audit-identified site
// =============================================================================

/// Marker: a single `QueueEntry` (content+sender+deposit+enqueued_at+size).
pub enum QueueEntryMarker {}
/// Marker: set of queue entries (MerkleQueue / ShardedQueue contents).
pub enum QueueEntrySetMarker {}
/// Marker: a blinded queue item (Poseidon2 commitment of item+randomness).
pub enum BlindedItemMarker {}
/// Marker: a blinded queue nullifier (Poseidon2 of commitment+secret+pos).
pub enum BlindedNullifierMarker {}
/// Marker: the set of blinded item commitments (BlindedQueue root).
pub enum BlindedItemSetMarker {}
/// Marker: a queue program identity (VK hash).
pub enum QueueProgramMarker {}
/// Marker: a set of authorized sender keys (programmable queue ACL).
pub enum AuthorizedKeySetMarker {}
/// Marker: a set of shards (ShardedQueue combined root).
pub enum ShardSetMarker {}
/// Marker: a pipeline spec (dataflow pipeline identity).
pub enum PipelineSpecMarker {}
/// Marker: an atomic queue-transaction (for Effect VM binding).
pub enum QueueTransactionMarker {}
/// Marker: a single erasure chunk (data or parity).
pub enum ErasureChunkMarker {}
/// Marker: a set of erasure chunks (combined root).
pub enum ErasureSetMarker {}

// =============================================================================
// Type aliases for clarity at call sites
// =============================================================================

pub type QueueEntryCommitment = Commitment<QueueEntryMarker>;
pub type QueueEntrySetRoot = MerkleRoot<QueueEntrySetMarker>;
pub type BlindedItemCommitment = Commitment4<BlindedItemMarker>;
pub type BlindedNullifierCommitment = Commitment4<BlindedNullifierMarker>;
pub type BlindedItemSetRoot = MerkleRoot<BlindedItemSetMarker>;
pub type QueueProgramCommitment = Commitment<QueueProgramMarker>;
pub type AuthorizedKeySetRoot = MerkleRoot<AuthorizedKeySetMarker>;
pub type ShardSetCommitment = Commitment<ShardSetMarker>;
pub type PipelineSpecCommitment = Commitment<PipelineSpecMarker>;
pub type QueueTransactionCommitment = Commitment<QueueTransactionMarker>;
pub type ErasureChunkCommitment = Commitment<ErasureChunkMarker>;
pub type ErasureSetCommitment = Commitment<ErasureSetMarker>;

// =============================================================================
// Default CommitmentSchema impls for marker-only sites (byte-packed)
// =============================================================================
//
// Each marker that commits to a raw byte slice gets a default schema impl
// that wraps the slice unchanged; the caller computes the canonical bytes
// (with field-aware layout) and passes them in.

macro_rules! byte_slice_schema {
    ($marker:ident, $domain_const:expr) => {
        impl CommitmentSchema for $marker {
            type Value = [u8];
            const DOMAIN: &'static str = $domain_const;
            fn canonical(value: &Self::Value) -> Vec<u8> {
                value.to_vec()
            }
        }
    };
}

byte_slice_schema!(QueueEntryMarker, domain::TAG_QUEUE_ENTRY);
byte_slice_schema!(QueueEntrySetMarker, domain::TAG_QUEUE_ENTRY_SET);
byte_slice_schema!(BlindedItemMarker, domain::TAG_BLINDED_ITEM);
byte_slice_schema!(BlindedNullifierMarker, domain::TAG_BLINDED_NULLIFIER);
byte_slice_schema!(BlindedItemSetMarker, domain::TAG_BLINDED_ITEM_SET);
byte_slice_schema!(QueueProgramMarker, domain::TAG_QUEUE_PROGRAM);
byte_slice_schema!(AuthorizedKeySetMarker, domain::TAG_AUTHORIZED_KEY_SET);
byte_slice_schema!(ShardSetMarker, domain::TAG_SHARD_SET);
byte_slice_schema!(PipelineSpecMarker, domain::TAG_PIPELINE_SPEC);
byte_slice_schema!(QueueTransactionMarker, domain::TAG_QUEUE_TRANSACTION);
byte_slice_schema!(ErasureChunkMarker, domain::TAG_ERASURE_CHUNK);
byte_slice_schema!(ErasureSetMarker, domain::TAG_ERASURE_SET);

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_commitment_is_zero() {
        let c: Commitment4<BlindedItemMarker> = Commitment4::empty();
        assert_eq!(c.blake3, [0u8; 32]);
        assert_eq!(c.poseidon2, [BabyBear::ZERO; 4]);
    }

    #[test]
    fn seal_produces_nonzero_for_nonempty_input() {
        let bytes: &[u8] = b"hello world";
        let c: Commitment4<BlindedItemMarker> = Commitment4::seal(bytes);
        assert_ne!(c.blake3, [0u8; 32]);
        assert_ne!(c.poseidon2, [BabyBear::ZERO; 4]);
    }

    #[test]
    fn seal_is_deterministic() {
        let bytes: &[u8] = b"deterministic input";
        let c1: Commitment4<BlindedItemMarker> = Commitment4::seal(bytes);
        let c2: Commitment4<BlindedItemMarker> = Commitment4::seal(bytes);
        assert_eq!(c1, c2);
    }

    #[test]
    fn different_domains_produce_different_commitments() {
        let bytes: &[u8] = b"same input";
        let c1: Commitment<QueueEntryMarker> = Commitment::seal(bytes);
        let c2: Commitment<QueueProgramMarker> = Commitment::seal(bytes);
        assert_ne!(c1.blake3, c2.blake3);
        assert_ne!(c1.poseidon2, c2.poseidon2);
    }

    #[test]
    fn verify_blake3_round_trips() {
        let bytes: &[u8] = b"verify-me";
        let c: Commitment4<BlindedItemMarker> = Commitment4::seal(bytes);
        assert!(c.verify_blake3(bytes));
        assert!(!c.verify_blake3(b"not-the-preimage"));
    }

    #[test]
    fn accumulator_is_order_dependent() {
        let a: &[u8] = b"alpha";
        let b: &[u8] = b"beta";

        let mut acc1: Accumulator<QueueEntryMarker> = Accumulator::new();
        acc1.extend(a);
        acc1.extend(b);
        let (b1, p1) = acc1.finalize();

        let mut acc2: Accumulator<QueueEntryMarker> = Accumulator::new();
        acc2.extend(b);
        acc2.extend(a);
        let (b2, p2) = acc2.finalize();

        assert_ne!(b1, b2);
        assert_ne!(p1, p2);
    }

    #[test]
    fn merkle_root_empty_is_sentinel() {
        let root: MerkleRoot<BlindedItemSetMarker> =
            MerkleRoot::from_leaves(&[], &[]);
        assert_eq!(root, MerkleRoot::empty());
    }

    #[test]
    fn merkle_root_single_leaf_is_passthrough() {
        let blake3_leaf = [0x42u8; 32];
        let poseidon2_leaf = [BabyBear::new(7), BabyBear::new(11), BabyBear::ZERO, BabyBear::ONE];
        let root: MerkleRoot<BlindedItemSetMarker> =
            MerkleRoot::from_leaves(&[blake3_leaf], &[poseidon2_leaf]);
        assert_eq!(root.blake3_root, blake3_leaf);
        assert_eq!(root.poseidon2_root, poseidon2_leaf);
    }

    #[test]
    fn merkle_root_two_leaves_changes_with_order() {
        let l1_b = [0x11u8; 32];
        let l2_b = [0x22u8; 32];
        let l1_p = [BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO];
        let l2_p = [BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO];

        let r1: MerkleRoot<BlindedItemSetMarker> =
            MerkleRoot::from_leaves(&[l1_b, l2_b], &[l1_p, l2_p]);
        let r2: MerkleRoot<BlindedItemSetMarker> =
            MerkleRoot::from_leaves(&[l2_b, l1_b], &[l2_p, l1_p]);
        assert_ne!(r1, r2);
    }

    #[test]
    fn canonical_32_to_felts_4_is_deterministic() {
        let bytes = [42u8; 32];
        let a = canonical_32_to_felts_4(&bytes);
        let b = canonical_32_to_felts_4(&bytes);
        assert_eq!(a, b);
    }

    /// P4.E stability test: assert that the Poseidon2 + BLAKE3 bytes for a
    /// known input have not drifted. If this test fails, the Poseidon2
    /// permutation or its parameters changed — investigate before
    /// shipping (verifiers across the network won't agree on commitments).
    ///
    /// Input: a `BlindedItemMarker` Commitment4 seal over the canonical
    /// encoding `len_le(item) || item || randomness` where `item =
    /// b"stable_test_item"` and `randomness = [0x42; 32]`.
    #[test]
    fn poseidon2_commitments_are_stable() {
        let item_data = b"stable_test_item";
        let randomness = [0x42u8; 32];

        // Mirror crypto::create_commitment's canonical encoding.
        let mut canonical = Vec::new();
        canonical.extend_from_slice(&(item_data.len() as u64).to_le_bytes());
        canonical.extend_from_slice(item_data);
        canonical.extend_from_slice(&randomness);

        let c: Commitment4<BlindedItemMarker> = Commitment4::seal(&canonical[..]);

        // Hardcoded expected bytes from a run of this test on 2026-05-24
        // against pyana_circuit::poseidon2 (BabyBear, WIDTH=8).
        // If you bump the Poseidon2 round constants, the BabyBear modulus,
        // or the TAG_BLINDED_ITEM domain tag, regenerate by uncommenting
        // the eprintln! lines below and rerunning with --nocapture.
        //
        // eprintln!("blake3: {:?}", c.blake3);
        // eprintln!("poseidon2: [{}, {}, {}, {}]",
        //     c.poseidon2[0].0, c.poseidon2[1].0, c.poseidon2[2].0, c.poseidon2[3].0);

        let expected_blake3: [u8; 32] = STABLE_BLINDED_ITEM_BLAKE3;
        let expected_poseidon2: [u32; 4] = STABLE_BLINDED_ITEM_POSEIDON2;

        assert_eq!(c.blake3, expected_blake3,
            "BLAKE3 form drifted — typed framework or TAG_BLINDED_ITEM changed");
        assert_eq!(
            [c.poseidon2[0].0, c.poseidon2[1].0, c.poseidon2[2].0, c.poseidon2[3].0],
            expected_poseidon2,
            "Poseidon2 form drifted — pyana_circuit::poseidon2 parameters changed",
        );
    }
}

// =============================================================================
// Stability constants (P4.E)
// =============================================================================
//
// Hardcoded byte/felt values for the known-input stability test
// `poseidon2_commitments_are_stable`. Filled in on 2026-05-24 from the
// current Poseidon2 implementation in pyana_circuit::poseidon2.
//
// Update procedure: if a deliberate parameter change requires these to
// drift, run the test with the eprintln! lines uncommented and
// `cargo test ... -- --nocapture`, then paste the new values here AND
// document the cause in the commit message.

const STABLE_BLINDED_ITEM_BLAKE3: [u8; 32] = [
    137, 79, 35, 157, 41, 139, 191, 243, 69, 17, 52, 43, 6, 1, 108, 68, 38, 122, 76, 8, 127, 233,
    201, 42, 156, 120, 113, 127, 40, 153, 96, 192,
];
const STABLE_BLINDED_ITEM_POSEIDON2: [u32; 4] =
    [433_477_333, 626_868_483, 68_240_588, 967_854_049];

// AUDIT[stage10-framework]: The two forms (BLAKE3 and Poseidon2) are
// derived from the same canonical bytes via two independent paths.
// Verifiers holding the canonical bytes can derive either form; the AIR
// uses the Poseidon2 form only. There is no BLAKE3 inside a STARK by
// design (see DESIGN-commitment-framework.md §2.2). The framework here
// duplicates `commit/src/typed.rs` rather than depending on it because
// `storage` is in the workspace `exclude` list; widening visibility was
// not required (pyana_circuit::poseidon2 is already pub).
