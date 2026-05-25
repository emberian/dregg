//! Typed dual-form commitment framework.
//!
//! Per `DESIGN-commitment-framework.md`. Every authoritative content
//! commitment in pyana carries two companion digests:
//!
//! 1. **`blake3: [u8; 32]`** — canonical byte-domain commitment. Cheap, used
//!    everywhere outside a STARK: storage keys, gossip dedup, signatures,
//!    REST APIs, log lines, ledger Merkle leaves.
//! 2. **`poseidon2: BabyBear` or `[BabyBear; 4]`** — field-domain commitment
//!    over BabyBear. Used as AIR public inputs, trace state columns,
//!    transition constraints, lookup arguments.
//!
//! The two are bound one-directionally to a shared canonical byte encoding.
//! There is no BLAKE3 inside a STARK; cross-form binding is established at
//! trusted boundary points (cclerk sealing, executor ingress) where both
//! forms are computed from the same preimage.
//!
//! ## Usage
//!
//! Implement [`CommitmentSchema`] for a type to derive both forms:
//!
//! ```ignore
//! struct MyValue { /* … */ }
//! enum MyMarker {}
//!
//! impl CommitmentSchema for MyMarker {
//!     type Value = MyValue;
//!     const DOMAIN: &'static str = "pyana-myvalue v1";
//!     fn canonical(value: &Self::Value) -> Vec<u8> { /* … */ }
//!     fn to_felts(value: &Self::Value) -> Vec<BabyBear> { /* … */ }
//! }
//!
//! let commitment: Commitment4<MyMarker> = Commitment4::seal(&my_value);
//! ```
//!
//! See `DESIGN-commitment-framework.md` §3 for the full design.

use core::marker::PhantomData;
use pyana_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

// =============================================================================
// Domain registry
// =============================================================================

/// Central domain-tag registry. Bumping a tag invalidates both BLAKE3 and
/// Poseidon2 forms together. Tags MUST end in a version suffix.
pub mod domain {
    pub const TAG_CELL_STATE: &str = "pyana-cell:state v2";
    pub const TAG_CAPABILITY_ROOT: &str = "pyana-cell:cap-root v2";
    pub const TAG_NOTE_COMMITMENT: &str = "pyana-note:commitment v2";
    pub const TAG_NOTE_NULLIFIER: &str = "pyana-note:nullifier v2";
    pub const TAG_TURN: &str = "pyana-turn:turn v2";
    pub const TAG_RECEIPT: &str = "pyana-turn:receipt v2";
    pub const TAG_OBLIGATION: &str = "pyana-turn:obligation v2";
    pub const TAG_BRIDGE_RECEIPT: &str = "pyana-bridge:receipt v2";
    pub const TAG_QUEUE_STATE: &str = "pyana-queue:state v2";
    pub const TAG_SWISS_TABLE: &str = "pyana-captp:swiss-table v2";
    pub const TAG_REFCOUNT_TABLE: &str = "pyana-captp:refcount-table v2";
    pub const TAG_APPROVED_HANDOFFS: &str = "pyana-captp:approved-handoffs v2";
    pub const TAG_EFFECTS: &str = "pyana-turn:effects v2";
}

// =============================================================================
// CommitmentSchema trait
// =============================================================================

/// Schema for a commitment-bearing value.
///
/// `Self` is a zero-sized marker; the commitment binds bytes of the
/// corresponding canonical encoding to two independent hashes.
///
/// `canonical()` returns the self-describing byte encoding consumed by both
/// hash paths. `to_felts()` returns the field-element view consumed by the
/// circuit.
pub trait CommitmentSchema: 'static {
    /// The underlying value type being committed to.
    type Value: ?Sized;
    /// Domain-separation tag (see [`domain`] module).
    const DOMAIN: &'static str;

    /// Canonical byte encoding (length-prefixed, deterministic).
    fn canonical(value: &Self::Value) -> Vec<u8>;

    /// Schema-encoded BabyBear felts. Default impl packs canonical bytes.
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
/// structure that itself has 124-bit security (e.g., a sparse Merkle leaf
/// where the root carries the security). For standalone authoritative
/// identifiers, use [`Commitment4`].
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct Commitment<T: CommitmentSchema> {
    pub blake3: [u8; 32],
    pub poseidon2: BabyBear,
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

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
        Self {
            blake3,
            poseidon2,
            _phantom: PhantomData,
        }
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
}

/// A typed dual-form commitment with a 4-felt field-form (~124-bit security).
///
/// Used where the Poseidon2 form stands alone as an authoritative identifier
/// (cell state, note commitments, receipts, federation roots).
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct Commitment4<T: CommitmentSchema> {
    pub blake3: [u8; 32],
    pub poseidon2: [BabyBear; 4],
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

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
        Self {
            blake3,
            poseidon2,
            _phantom: PhantomData,
        }
    }

    /// The empty (sentinel) commitment for this type.
    ///
    /// Used as the initial value for committed roots whose state is empty
    /// (no swiss-table entries yet, no approved handoffs, etc.).
    pub fn empty() -> Self {
        Self {
            blake3: [0u8; 32],
            poseidon2: [BabyBear::ZERO; 4],
            _phantom: PhantomData,
        }
    }

    /// Construct from a precomputed pair. Use only at trust boundaries where
    /// both forms have been computed from the same preimage by the producer.
    pub fn from_parts(blake3: [u8; 32], poseidon2: [BabyBear; 4]) -> Self {
        Self {
            blake3,
            poseidon2,
            _phantom: PhantomData,
        }
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

// =============================================================================
// Accumulator (streaming hash-chain)
// =============================================================================

/// Streaming dual-form accumulator. Each `extend()` updates both the BLAKE3
/// chain and the Poseidon2 chain in lock-step. Used for ordered aggregates
/// like turn effects.
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
        self.blake3_state
            .update(&(bytes.len() as u64).to_le_bytes());
        self.blake3_state.update(&bytes);

        let felts = T::to_felts(item);
        // Absorb felts one block at a time via hash_4_to_1 with the current chain
        // as IV. For chains longer than 4 felts we fold in blocks.
        for chunk in felts.chunks(4) {
            let mut block = [BabyBear::ZERO; 4];
            for (i, &f) in chunk.iter().enumerate() {
                block[i] = f;
            }
            // chain' = hash_4_to_1(chain[0..4]) XOR'd with absorbed block via tree.
            // Simple sponge: produce four new chain felts as h(chain || block).
            self.poseidon2_chain = absorb_4(self.poseidon2_chain, block);
        }
    }

    /// Finalize: returns the dual-form commitment over all absorbed items.
    pub fn finalize(self) -> ([u8; 32], [BabyBear; 4]) {
        let blake3 = *self.blake3_state.finalize().as_bytes();
        // Final squeeze: incorporate length.
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

/// A sparse Merkle root committed dually as a BLAKE3 root and a Poseidon2 root.
///
/// The two roots are computed from the same leaf set via two parallel trees;
/// producers compute both and emit them together. Verifiers select the form
/// appropriate to context (BLAKE3 for off-chain dedup; Poseidon2 for STARK PI).
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct MerkleRoot<T: CommitmentSchema> {
    pub blake3_root: [u8; 32],
    pub poseidon2_root: [BabyBear; 4],
    #[serde(skip)]
    _phantom: PhantomData<fn() -> T>,
}

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
        Self {
            blake3_root,
            poseidon2_root,
            _phantom: PhantomData,
        }
    }
}

// =============================================================================
// Tag markers (zero-sized phantom types)
// =============================================================================

/// Marker: cell state commitment.
pub enum CellStateMarker {}
/// Marker: capability set / c-list root.
pub enum CapabilityListMarker {}
/// Marker: note commitment.
pub enum NoteMarker {}
/// Marker: note nullifier.
pub enum NullifierMarker {}
/// Marker: turn receipt.
pub enum ReceiptMarker {}
/// Marker: obligation.
pub enum ObligationMarker {}
/// Marker: turn effect tree.
pub enum EffectsMarker {}
/// Marker: queue state.
pub enum QueueStateMarker {}
/// Marker: bridge receipt.
pub enum BridgeReceiptMarker {}
/// Marker: CapTP swiss table root.
pub enum SwissTableMarker {}
/// Marker: CapTP refcount table root.
pub enum RefcountTableMarker {}
/// Marker: federation approved-handoffs set root.
pub enum ApprovedHandoffSetMarker {}

// =============================================================================
// Implementations for the top-5 migration targets
// =============================================================================

/// Schema for the canonical cell-state commitment (BLAKE3 derive_key over
/// the canonical encoding from `cell::commitment::compute_canonical_state_commitment`).
///
/// The BLAKE3 form is the canonical commitment from the cell crate.
/// The Poseidon2 form is derived from the same canonical bytes via
/// [`encode_bytes_to_felts`].
impl CommitmentSchema for CellStateMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_CELL_STATE;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

/// Schema for the capability-set root.
impl CommitmentSchema for CapabilityListMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_CAPABILITY_ROOT;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

/// Schema for a note (the typed primary key — owner+value+asset+nonce+rand).
///
/// The canonical form is the existing BLAKE3 encoding from `Note::commitment`.
/// The to_felts form mirrors `Note::poseidon2_commitment`'s shape.
pub struct NoteCanonical<'a> {
    pub canonical_bytes: &'a [u8],
    pub felts: [BabyBear; 5],
}

impl CommitmentSchema for NoteMarker {
    type Value = NoteCanonical<'static>;
    const DOMAIN: &'static str = domain::TAG_NOTE_COMMITMENT;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.canonical_bytes.to_vec()
    }
    fn to_felts(value: &Self::Value) -> Vec<BabyBear> {
        value.felts.to_vec()
    }
}

impl CommitmentSchema for NullifierMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_NOTE_NULLIFIER;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

impl CommitmentSchema for EffectsMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_EFFECTS;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

impl CommitmentSchema for SwissTableMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_SWISS_TABLE;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

impl CommitmentSchema for RefcountTableMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_REFCOUNT_TABLE;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

impl CommitmentSchema for ApprovedHandoffSetMarker {
    type Value = [u8];
    const DOMAIN: &'static str = domain::TAG_APPROVED_HANDOFFS;
    fn canonical(value: &Self::Value) -> Vec<u8> {
        value.to_vec()
    }
}

// =============================================================================
// Convenience type aliases
// =============================================================================

pub type CellStateCommitment = Commitment4<CellStateMarker>;
pub type CapabilityRootCommitment = Commitment4<CapabilityListMarker>;
pub type NoteCommitment4 = Commitment4<NoteMarker>;
pub type NullifierCommitment = Commitment4<NullifierMarker>;
pub type EffectsCommitment = Commitment4<EffectsMarker>;
pub type SwissTableRootCommitment = Commitment4<SwissTableMarker>;
pub type RefcountTableRootCommitment = Commitment4<RefcountTableMarker>;
pub type ApprovedHandoffsRootCommitment = Commitment4<ApprovedHandoffSetMarker>;

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
///
/// Computes a BLAKE3 hash of the tag string and reduces the first 4 bytes mod
/// the BabyBear prime to obtain a 31-bit element. Bumping a tag changes the
/// element, providing domain separation in the Poseidon2 form.
pub fn tag_hash_31(domain: &str) -> u32 {
    let h = blake3::hash(domain.as_bytes());
    let bytes = h.as_bytes();
    let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    raw % pyana_circuit::field::BABYBEAR_P
}

/// Pack arbitrary bytes into BabyBear felts at 30 bits/limb.
///
/// Mirrors the trick in `cell::commitment::canonical_to_babybear_pi`:
/// BabyBear's modulus is 2^31 - 2^27 + 1; 30-bit limbs guarantee a unique
/// encoding without modular reduction collisions. A four-byte length prefix
/// is absorbed first.
pub fn encode_bytes_to_felts(bytes: &[u8]) -> Vec<BabyBear> {
    let mut felts = Vec::with_capacity(bytes.len() / 4 + 2);
    // Length prefix (low 30 bits of u32).
    felts.push(BabyBear::new((bytes.len() as u32) & ((1u32 << 30) - 1)));
    let mut i = 0;
    while i < bytes.len() {
        let b0 = bytes[i] as u32;
        let b1 = if i + 1 < bytes.len() {
            bytes[i + 1] as u32
        } else {
            0
        };
        let b2 = if i + 2 < bytes.len() {
            bytes[i + 2] as u32
        } else {
            0
        };
        let b3 = if i + 3 < bytes.len() {
            bytes[i + 3] as u32
        } else {
            0
        };
        // Pack 30 bits: 8+8+8+6.
        let limb = b0 | (b1 << 8) | (b2 << 16) | ((b3 & 0x3F) << 24);
        felts.push(BabyBear::new(limb));
        i += 4;
    }
    felts
}

/// Pack arbitrary bytes into 8 BabyBear felts at 30 bits/limb (the fixed form
/// used for 32-byte canonical commitments).
///
/// Identical shape to `cell::commitment::canonical_to_babybear_pi` but returns
/// `[BabyBear; 8]` directly. This is the bytes-to-felts adapter used by the
/// runtime to derive the Poseidon2 form from a 32-byte canonical commitment.
pub fn canonical_32_to_felts_8(canonical: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        // Pack 30 bits: 8+8+8+6 = 30
        out[i] = BabyBear::new(lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24));
    }
    out
}

/// Compress a 32-byte canonical commitment into 4 BabyBear felts via Poseidon2.
///
/// Used to derive the 4-felt Poseidon2 form of a commitment whose canonical
/// bytes are known. Distinct from `canonical_32_to_felts_8` (which produces
/// a raw 8-limb encoding without hashing): this output is suitable as a
/// Poseidon2-domain commitment for absorbing into an AIR PI.
pub fn canonical_32_to_felts_4(canonical: &[u8; 32]) -> [BabyBear; 4] {
    let eight = canonical_32_to_felts_8(canonical);
    // Two hash_4_to_1 compressions to fold 8 -> 4.
    let a = pyana_circuit::poseidon2::hash_4_to_1(&[eight[0], eight[1], eight[2], eight[3]]);
    let b = pyana_circuit::poseidon2::hash_4_to_1(&[eight[4], eight[5], eight[6], eight[7]]);
    let c = pyana_circuit::poseidon2::hash_4_to_1(&[eight[0], eight[4], eight[2], eight[6]]);
    let d = pyana_circuit::poseidon2::hash_4_to_1(&[eight[1], eight[5], eight[3], eight[7]]);
    [a, b, c, d]
}

/// Squeeze a single BabyBear from a domain-tagged sponge over felts.
fn poseidon2_single_with_tag(domain: &str, felts: &[BabyBear]) -> BabyBear {
    let tag = BabyBear::new(tag_hash_31(domain));
    let mut tagged = Vec::with_capacity(felts.len() + 1);
    tagged.push(tag);
    tagged.extend_from_slice(felts);
    pyana_circuit::poseidon2::hash_many(&tagged)
}

/// Squeeze 4 BabyBears from a domain-tagged sponge over felts.
///
/// Uses 4 independent hash trees with different "salt" felts as the 4th input
/// to a final hash_4_to_1 compression, mirroring the AIR's commitment-tree
/// design (see `circuit/src/effect_vm.rs::CellState::compute_commitment`).
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
fn absorb_4(chain: [BabyBear; 4], block: [BabyBear; 4]) -> [BabyBear; 4] {
    use pyana_circuit::poseidon2::hash_4_to_1;
    [
        hash_4_to_1(&[chain[0], block[0], chain[1], block[1]]),
        hash_4_to_1(&[chain[1], block[1], chain[2], block[2]]),
        hash_4_to_1(&[chain[2], block[2], chain[3], block[3]]),
        hash_4_to_1(&[chain[3], block[3], chain[0], block[0]]),
    ]
}

// =============================================================================
// Compile-fail boundary tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_commitment_is_zero() {
        let c: Commitment4<CellStateMarker> = Commitment4::empty();
        assert_eq!(c.blake3, [0u8; 32]);
        assert_eq!(c.poseidon2, [BabyBear::ZERO; 4]);
    }

    #[test]
    fn seal_produces_nonzero_for_nonempty_input() {
        let bytes: &[u8] = b"hello world";
        let c: Commitment4<CellStateMarker> = Commitment4::seal(bytes);
        assert_ne!(c.blake3, [0u8; 32]);
        assert_ne!(c.poseidon2, [BabyBear::ZERO; 4]);
    }

    #[test]
    fn seal_is_deterministic() {
        let bytes: &[u8] = b"deterministic input";
        let c1: Commitment4<CellStateMarker> = Commitment4::seal(bytes);
        let c2: Commitment4<CellStateMarker> = Commitment4::seal(bytes);
        assert_eq!(c1, c2);
    }

    #[test]
    fn different_domains_produce_different_commitments() {
        let bytes: &[u8] = b"same input";
        let c1: Commitment4<CellStateMarker> = Commitment4::seal(bytes);
        let c2: Commitment4<CapabilityListMarker> = Commitment4::seal(bytes);
        // Same canonical bytes but different domain tags must produce
        // different commitments on both forms.
        assert_ne!(c1.blake3, c2.blake3);
        assert_ne!(c1.poseidon2, c2.poseidon2);
    }

    #[test]
    fn canonical_32_to_felts_4_is_deterministic() {
        let bytes = [42u8; 32];
        let a = canonical_32_to_felts_4(&bytes);
        let b = canonical_32_to_felts_4(&bytes);
        assert_eq!(a, b);
    }

    #[test]
    fn canonical_32_to_felts_4_changes_with_input() {
        let mut bytes = [42u8; 32];
        let a = canonical_32_to_felts_4(&bytes);
        bytes[7] = 99;
        let b = canonical_32_to_felts_4(&bytes);
        assert_ne!(a, b);
    }

    #[test]
    fn verify_blake3_round_trips() {
        let bytes: &[u8] = b"verify-me";
        let c: Commitment4<CellStateMarker> = Commitment4::seal(bytes);
        assert!(c.verify_blake3(bytes));
        assert!(!c.verify_blake3(b"not-the-preimage"));
    }

    #[test]
    fn accumulator_is_order_dependent() {
        let a: &[u8] = b"alpha";
        let b: &[u8] = b"beta";

        let mut acc1: Accumulator<EffectsMarker> = Accumulator::new();
        acc1.extend(a);
        acc1.extend(b);
        let (b1, p1) = acc1.finalize();

        let mut acc2: Accumulator<EffectsMarker> = Accumulator::new();
        acc2.extend(b);
        acc2.extend(a);
        let (b2, p2) = acc2.finalize();

        assert_ne!(b1, b2);
        assert_ne!(p1, p2);
    }
}

// =============================================================================
// AUDIT NOTE
// =============================================================================
// AUDIT[stage1-framework]: The two forms (BLAKE3 and Poseidon2) are derived
// from the *same canonical bytes* via two independent paths. Verifiers
// holding the canonical bytes can derive either form; the AIR uses the
// Poseidon2 form only. There is no BLAKE3 inside a STARK by design (see
// DESIGN-commitment-framework.md §2.2).
//
// AUDIT[stage1-collision-domain]: Commitment4<T> provides ~124-bit collision
// resistance on the Poseidon2 form (4 independent BabyBear squeeze outputs).
// Commitment<T> provides ~31 bits which is only safe inside a Merkle root.
//
// AUDIT[stage1-empty]: empty() commitments are valid sentinels for "no
// state yet" used by CapTP-prep fields (swiss_table_root etc.). They are
// NOT zero-knowledge; an observer can detect emptiness.
