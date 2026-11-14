//! # dregg-blocklace
//!
//! # Trust Model
//!
//! This crate operates at the **CONSENSUS-TRUSTLESS** trust level.
//!
//! - **Soundness**: Finality is verified by ALL participants. Once a block reaches
//!   finality (via the constitution's supermajority rule), it cannot be reverted without
//!   violating the BFT assumption (>1/3 Byzantine). The DAG structure is self-validating:
//!   hash links make it impossible to rewrite history without detection.
//! - **Assumptions**: Honest supermajority (2f+1 of 3f+1 nodes). Network eventually
//!   delivers messages (partial synchrony). Block creators sign their blocks (Ed25519).
//!   BLAKE3 is collision-resistant (for content addressing).
//! - **Verifiable by**: Every participant independently. Any node can verify:
//!   - Block integrity (hash matches content)
//!   - Block authenticity (signature matches creator)
//!   - Causal ordering (all predecessors exist and are valid)
//!   - Finality (supermajority acknowledgment per the constitution)
//!
//! ## Trust Boundaries
//! - The blocklace does NOT verify payload semantics (that is the executor's job)
//! - The blocklace DOES guarantee total ordering and finality
//! - Dissemination is best-effort (liveness) but does not affect safety
//!
//! ## Key Invariants
//! 1. Authenticated block IDs are content-addressed. Ordering-only projections retain the
//!    authenticated source id even when their unsigned skeleton has a different encoding.
//! 2. Blocks are inserted only if all predecessors are present (causal closure)
//! 3. Finalized blocks form an immutable prefix of the DAG
//! 4. The topological order is a valid linearization of the causal DAG
//!
//! Blocklace: a DAG-based data structure for Byzantine fault-tolerant consensus.
//!
//! This crate implements:
//! - Block creation and validation (content-addressed, hash-linked DAG)
//! - Cordial dissemination protocol (efficient gossip-based block propagation)
//!
//! ## Cordial Dissemination
//!
//! The key principle from the Cordial Miners paper: "send to others blocks you
//! know and think they need." Block pointers encode what each node knows,
//! enabling efficient catch-up without explicit protocol messages.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │  Blocklace (DAG of blocks with causal links)                        │
//! │     ↓                                                               │
//! │  Disseminator (cordial dissemination engine)                         │
//! │     ├── blocks_to_send(peer) → causally-closed delta                │
//! │     ├── received_from(peer, block) → update peer knowledge          │
//! │     └── handle_message(msg) → process Push/Pull/PullResponse        │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

pub mod addressing;
pub mod constitution;
pub mod cross_reference;
pub mod delegation;
pub mod dissemination;
pub mod dregg_bridge;
pub mod evidence;
pub mod finality;
pub mod ordering;
pub mod pq;
pub mod signer;

pub use pq::{MlDsaPublicKey, MlDsaSigningKey};
pub use signer::HybridBlockSigner;

/// THE one quorum formula (strict supermajority `⌊2n/3⌋ + 1`); see
/// [`ordering::supermajority_threshold`]. `dregg_federation::quorum_threshold`
/// delegates here.
pub use ordering::supermajority_threshold;

use std::collections::{HashMap, HashSet, VecDeque};

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};

/// A block identifier: the BLAKE3 hash of the block's canonical encoding.
pub type BlockId = [u8; 32];

/// A node identifier: the public key (32 bytes) of the block creator.
pub type NodeKey = [u8; 32];

/// A block in the blocklace DAG.
///
/// Each block references its predecessors (causal dependencies) and is signed
/// by its creator. The block ID is the BLAKE3 hash of (creator || sequence ||
/// predecessors || payload).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    /// The creator's public key.
    pub creator: NodeKey,
    /// Monotonic sequence number for this creator (0-indexed).
    pub sequence: u64,
    /// Block IDs this block depends on (causal predecessors).
    pub predecessors: Vec<BlockId>,
    /// Application-level payload.
    pub payload: Vec<u8>,
    /// Signature over the block hash by the creator (64 bytes, Ed25519).
    /// Set to zeros for unsigned/test blocks.
    #[serde(with = "serde_sig64")]
    pub signature: [u8; 64],
    /// The POST-QUANTUM half of the HYBRID signature: an ML-DSA-65 (FIPS 204)
    /// signature over the SAME canonical bytes as the ed25519 half (`id()`),
    /// produced by the key DERIVED from the creator's ed25519 seed
    /// ([`pq::MlDsaSigningKey::from_seed`]). Empty (`vec![]`) is the
    /// PQ-absent/unsigned sentinel — it fails [`Block::verify_signature`]
    /// closed. A hybrid block carries [`pq::SIG_LEN`] (3309) bytes here.
    ///
    /// The verifier PINS this against the creator's ENROLLED ML-DSA public key
    /// (the committee roster), NOT a key carried in the block — so a quantum
    /// adversary who forges the ed25519 half still cannot inject blocks under
    /// another creator's identity. Adding this field is a postcard flag-day
    /// (blocks are internal wire); all nodes must upgrade together.
    #[serde(default)]
    pub pq_signature: Vec<u8>,
}

/// Serde helper for 64-byte arrays (Ed25519 signatures).
/// Serde only implements Serialize/Deserialize for arrays up to [T; 32].
pub(crate) mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        AsRef::<[u8]>::as_ref(bytes).serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

impl Block {
    /// Compute the canonical block ID (BLAKE3 hash of the block's content).
    ///
    /// The hash covers: creator, sequence, predecessors (sorted), and payload.
    /// It does NOT cover the signature (so the signature can be verified against
    /// the hash without circular dependency).
    pub fn id(&self) -> BlockId {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-blocklace-block-v1");
        hasher.update(&self.creator);
        hasher.update(&self.sequence.to_le_bytes());
        hasher.update(&(self.predecessors.len() as u32).to_le_bytes());
        let mut sorted_preds = self.predecessors.clone();
        sorted_preds.sort();
        for pred in &sorted_preds {
            hasher.update(pred);
        }
        hasher.update(&(self.payload.len() as u32).to_le_bytes());
        hasher.update(&self.payload);
        *hasher.finalize().as_bytes()
    }

    /// Create a new unsigned block.
    ///
    /// The signature is left zeroed. Such a block is **rejected by
    /// [`Blocklace::insert`]** (feed-integrity requires an authentic Ed25519
    /// signature over `id()`); use [`Block::new_signed`] / [`Block::sign`] for a
    /// block that the strand-integrity write path will accept. `new` remains for
    /// constructing the unsigned skeleton prior to signing and for the unsigned
    /// *ordering projection* (`Blocklace::insert_unverified`), which does not
    /// touch the wire.
    pub fn new(
        creator: NodeKey,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        Self {
            creator,
            sequence,
            predecessors,
            payload,
            signature: [0u8; 64],
            pq_signature: Vec::new(),
        }
    }

    /// Create and Ed25519-sign a block with the given signing key.
    ///
    /// The `creator` is the signing key's public key, and the signature covers
    /// the block's canonical `id()` (BLAKE3 of creator/seq/preds/payload). The
    /// resulting block passes [`Block::verify_signature`] and is accepted by the
    /// feed-integrity [`Blocklace::insert`].
    /// ⚠ A ONE-SHOT: it pays a full ML-DSA-65 keygen for this block alone. A
    /// caller that authors more than one block for one identity should hold a
    /// [`HybridBlockSigner`] and call [`Block::new_signed_by`], which is
    /// byte-identical.
    pub fn new_signed(
        signing_key: &SigningKey,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        Self::new_signed_by(
            &HybridBlockSigner::new(signing_key.clone()),
            sequence,
            predecessors,
            payload,
        )
    }

    /// Create and HYBRID-sign a block with an identity whose ML-DSA key was
    /// derived ONCE, at the signer's construction. Byte-identical to
    /// [`Block::new_signed`] on the same seed; this is the form that does not pay
    /// a keygen per block.
    pub fn new_signed_by(
        signer: &HybridBlockSigner,
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Self {
        let mut block = Self::new(signer.ed25519(), sequence, predecessors, payload);
        block.sign_by(signer);
        block
    }

    /// Sign (or re-sign) this block in place with `signing_key`, producing the
    /// HYBRID (ed25519 ∧ ML-DSA-65) signature.
    ///
    /// Sets `creator` to the key's public key, `signature` to the Ed25519
    /// signature over `id()`, and `pq_signature` to the ML-DSA-65 signature over
    /// the SAME `id()`. The ML-DSA key is DERIVED from the ed25519 seed
    /// (`signing_key.to_bytes()`) via [`pq::MlDsaSigningKey::from_seed`] — the
    /// creator never manages a separate PQ key, and the enrolled PQ public key
    /// is a deterministic function of the ed25519 identity. Returns the ed25519
    /// signature for convenience.
    /// ⚠ A ONE-SHOT: it pays a full ML-DSA-65 keygen per call. Use
    /// [`Block::sign_by`] with a held [`HybridBlockSigner`] to sign more than one
    /// block for one identity; the bytes are identical either way.
    pub fn sign(&mut self, signing_key: &SigningKey) -> [u8; 64] {
        self.sign_by(&HybridBlockSigner::new(signing_key.clone()))
    }

    /// Sign (or re-sign) this block in place with a held HYBRID identity — the
    /// same bytes [`Block::sign`] produces, with no key derivation however many
    /// blocks this identity signs.
    pub fn sign_by(&mut self, signer: &HybridBlockSigner) -> [u8; 64] {
        self.creator = signer.ed25519();
        let id = self.id();
        let sig = signer.classical().sign(&id);
        self.signature = sig.to_bytes();
        // POST-QUANTUM half: sign the SAME canonical bytes with the identity's
        // held ML-DSA key. `None` only on a transient OS-entropy failure during
        // hedged ML-DSA signing; leaving the PQ half empty makes the block fail
        // `verify_signature` closed (never a half-signed block that passes).
        self.pq_signature = signer.sign_pq(&id).unwrap_or_default();
        self.signature
    }

    /// The enrollable ML-DSA-65 public key for a creator whose ed25519 signing
    /// key is `signing_key` — the roster entry a verifier PINS this creator's
    /// blocks against. Convenience for genesis enrollment and tests; equal to
    /// [`pq::public_from_ed25519_seed`] on the key's seed.
    ///
    /// ⚠ A ONE-SHOT — it pays a full ML-DSA-65 keygen. A holder of a
    /// [`HybridBlockSigner`] reads the same key off
    /// [`HybridBlockSigner::pq_public_key`] for free.
    pub fn pq_public_key(signing_key: &SigningKey) -> pq::MlDsaPublicKey {
        HybridBlockSigner::new(signing_key.clone())
            .pq_public_key()
            .clone()
    }

    /// Whether this block carries BOTH halves of a (syntactically) non-zero
    /// hybrid signature.
    ///
    /// A zeroed ed25519 signature or an empty ML-DSA half is the unsigned
    /// sentinel produced by [`Block::new`]; neither can be a valid hybrid
    /// signature, so such a block is rejected on insert (fails closed).
    pub fn is_signed(&self) -> bool {
        self.signature != [0u8; 64] && !self.pq_signature.is_empty()
    }

    /// Verify this block's HYBRID signature: Ed25519 against its `creator`
    /// pubkey AND ML-DSA-65 against the creator's ENROLLED PQ public key.
    ///
    /// Returns `Ok(())` iff BOTH halves verify over `id()`:
    /// - the ed25519 `signature` verifies against the self-carried `creator`
    ///   (the ed25519 identity IS the creator id), and
    /// - the `pq_signature` verifies against `enrolled_pq` — the committee
    ///   roster's ML-DSA key for this creator, NOT a key carried in the block.
    ///
    /// Rejects the unsigned sentinel, a malformed pubkey, and any forged or
    /// mismatched half. Because the PQ half is pinned to the enrolled key, a
    /// quantum adversary who forges the ed25519 half — or who signs the PQ half
    /// under their OWN fresh ML-DSA key — cannot pass: their key is not the one
    /// enrolled for `creator`.
    pub fn verify_signature(&self, enrolled_pq: &pq::MlDsaPublicKey) -> Result<(), InsertError> {
        if !self.is_signed() {
            return Err(InsertError::Unsigned {
                creator: self.creator,
                sequence: self.sequence,
            });
        }
        // (a) Classical half: real Ed25519 verification against `creator`.
        let vk =
            VerifyingKey::from_bytes(&self.creator).map_err(|_| InsertError::BadSignature {
                creator: self.creator,
                sequence: self.sequence,
            })?;
        let sig = ed25519_dalek::Signature::from_bytes(&self.signature);
        vk.verify_strict(&self.id(), &sig)
            .map_err(|_| InsertError::BadSignature {
                creator: self.creator,
                sequence: self.sequence,
            })?;
        // (b) Post-quantum half: ML-DSA-65 pinned to the ENROLLED roster key.
        if !enrolled_pq.verify(&self.id(), &self.pq_signature) {
            return Err(InsertError::BadPqSignature {
                creator: self.creator,
                sequence: self.sequence,
            });
        }
        Ok(())
    }

    /// Serialize the block to bytes for wire transmission.
    ///
    /// Uses postcard's compact binary format.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("block serialization should not fail")
    }

    /// Deserialize a block from bytes.
    ///
    /// Returns `None` if the bytes are malformed.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes(bytes).ok()
    }
}

/// Proof that a creator equivocated: two distinct blocks at the same
/// `(creator, sequence)`.
///
/// The equivocation is *attributable* (both blocks name `creator`) and
/// *detectable* (the pair is retained in the lace, not overwritten). This is
/// the strand-layer analogue of `finality.rs::EquivocationProof`, and it is the
/// representation `ordering.rs::EquivocationIndex::equivocates_in_past` (renamed
/// from `has_equivocation_in_past`; corrected 2026-07-16) consumes when it
/// scans for two same-creator blocks at one round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquivocationProof {
    /// The equivocating creator's public key.
    pub creator: NodeKey,
    /// The sequence number at which the fork occurred.
    pub sequence: u64,
    /// The block already present at `(creator, sequence)`.
    pub existing: BlockId,
    /// The conflicting block presented at the same `(creator, sequence)`.
    pub conflicting: BlockId,
}

/// Why a block could not be inserted as a valid strand extension.
///
/// `insert` is the feed-integrity write path (SSB-style: append-only,
/// Ed25519-signed, monotone-seq, no-equivocation-without-detection). Every
/// rejection is one of these; the previous `Vec<BlockId>` (missing
/// predecessors) is preserved as the [`InsertError::MissingPredecessors`]
/// variant so the dissemination layer can still buffer pending blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InsertError {
    /// Causal closure failed: these predecessor IDs are not yet present.
    MissingPredecessors(Vec<BlockId>),
    /// The block carries no signature (the zeroed sentinel from `Block::new`).
    Unsigned { creator: NodeKey, sequence: u64 },
    /// The block's Ed25519 signature does not verify against `creator`.
    BadSignature { creator: NodeKey, sequence: u64 },
    /// The block's ML-DSA-65 (post-quantum) signature does not verify against
    /// the creator's ENROLLED PQ public key. This is the half a quantum
    /// adversary cannot forge: the ed25519 half may be valid, but the PQ half
    /// was not signed by the key enrolled for `creator`.
    BadPqSignature { creator: NodeKey, sequence: u64 },
    /// No ML-DSA-65 public key is enrolled for `creator`, so the block's
    /// post-quantum half cannot be pinned to a trusted key. Fails CLOSED: the
    /// block is rejected rather than trusting a self-carried or derived key.
    UnenrolledCreator { creator: NodeKey, sequence: u64 },
    /// The block's sequence does not extend the creator's known chain
    /// (it regresses to or below the creator's current tip sequence).
    SeqRegression {
        creator: NodeKey,
        /// The sequence the block claims.
        attempted: u64,
        /// The creator's current tip sequence (the block must exceed it).
        tip_sequence: u64,
    },
    /// A second, different block was presented at an existing `(creator,
    /// sequence)`. The block is retained as detectable evidence (NOT silently
    /// overwriting the tip); the proof attributes the fork.
    Equivocation(EquivocationProof),
}

impl InsertError {
    /// If this error is a closure failure, the missing predecessor IDs.
    ///
    /// Lets the dissemination layer buffer a block whose predecessors have not
    /// yet arrived, exactly as the old `Err(Vec<BlockId>)` contract did.
    pub fn missing_predecessors(&self) -> Option<&[BlockId]> {
        match self {
            InsertError::MissingPredecessors(m) => Some(m),
            _ => None,
        }
    }
}

impl std::fmt::Display for InsertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InsertError::MissingPredecessors(m) => {
                write!(f, "missing {} predecessor(s)", m.len())
            }
            InsertError::Unsigned { sequence, .. } => {
                write!(f, "block at seq {sequence} is unsigned")
            }
            InsertError::BadSignature { sequence, .. } => {
                write!(f, "block at seq {sequence} has an invalid signature")
            }
            InsertError::BadPqSignature { sequence, .. } => {
                write!(
                    f,
                    "block at seq {sequence} has an invalid post-quantum (ML-DSA) signature"
                )
            }
            InsertError::UnenrolledCreator { sequence, .. } => {
                write!(
                    f,
                    "block at seq {sequence} has no enrolled ML-DSA key for its creator"
                )
            }
            InsertError::SeqRegression {
                attempted,
                tip_sequence,
                ..
            } => write!(f, "seq {attempted} does not extend tip seq {tip_sequence}"),
            InsertError::Equivocation(p) => write!(
                f,
                "equivocation by creator at seq {} (existing vs conflicting block)",
                p.sequence
            ),
        }
    }
}

impl std::error::Error for InsertError {}

/// The local blocklace: stores all known blocks and their relationships.
#[derive(Clone, Debug, Default)]
pub struct Blocklace {
    /// All blocks by their ID.
    pub(crate) blocks: HashMap<BlockId, Block>,
    /// Forward edges: block_id -> set of blocks that reference it as a predecessor.
    successors: HashMap<BlockId, HashSet<BlockId>>,
    /// The latest block ID per creator (tip of each creator's chain).
    tips: HashMap<NodeKey, BlockId>,
    /// The highest sequence number we have accepted per creator (the strand
    /// length). A new block must strictly exceed this to be a valid extension.
    tip_sequence: HashMap<NodeKey, u64>,
    /// Creators caught equivocating (a fork was presented). Once detected, the
    /// creator's tip is withdrawn — there is no single honest feed head.
    equivocators: HashSet<NodeKey>,
    /// Detected equivocation proofs (attributable fork evidence).
    equivocation_proofs: Vec<EquivocationProof>,
    /// Blocks with no successors (the current DAG frontier).
    frontier: HashSet<BlockId>,
    /// Reverse index `(creator, sequence) -> first stored block id` at that
    /// position. Maintained on every stored block (first-wins). Lets
    /// [`find_conflict`] answer "is there already a block at this
    /// (creator, sequence)?" in O(1) instead of scanning all blocks. The
    /// retained value is the FIRST block seen at the position — the canonical
    /// fork witness against which a later equivocating block is compared.
    by_creator_seq: HashMap<(NodeKey, u64), BlockId>,
    /// The enrolled ML-DSA-65 committee roster: `creator (ed25519 pubkey) ->
    /// enrolled ML-DSA public key`. The strand-integrity [`Blocklace::insert`]
    /// PINS a block's post-quantum half to the enrolled key for its creator —
    /// it never trusts a key carried in the block. A creator absent from the
    /// roster is rejected ([`InsertError::UnenrolledCreator`], fail-closed).
    /// Populated out-of-band from the trusted committee roster (genesis), via
    /// [`Blocklace::enroll_pq`].
    pq_roster: HashMap<NodeKey, pq::MlDsaPublicKey>,
}

impl Blocklace {
    /// Create a new empty blocklace.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enroll a creator's ML-DSA-65 public key into the committee roster.
    ///
    /// After enrollment, [`Blocklace::insert`] PINS every block by `creator` to
    /// `pubkey` for its post-quantum half. This is the trusted, out-of-band
    /// enrollment (genesis committee roster) — the block never carries its own
    /// PQ key. Re-enrolling a creator replaces the key (e.g. committee
    /// rotation). The enrollable key is [`Block::pq_public_key`] /
    /// [`pq::public_from_ed25519_seed`] on the creator's ed25519 seed.
    pub fn enroll_pq(&mut self, creator: NodeKey, pubkey: pq::MlDsaPublicKey) {
        self.pq_roster.insert(creator, pubkey);
    }

    /// The enrolled ML-DSA committee roster (`creator -> enrolled PQ pubkey`).
    pub fn pq_roster(&self) -> &HashMap<NodeKey, pq::MlDsaPublicKey> {
        &self.pq_roster
    }

    /// Insert a block into the blocklace, enforcing **feed integrity**.
    ///
    /// This is the strand-integrity write path. A block is accepted only if it
    /// is a valid extension of its creator's append-only, Ed25519-signed,
    /// monotone-sequence feed (a Secure-Scuttlebutt strand). Specifically:
    ///
    /// 1. **Authenticity (HYBRID)** — the block's Ed25519 signature must verify
    ///    against its `creator` pubkey AND its ML-DSA-65 signature must verify
    ///    against the creator's ENROLLED PQ key (the committee roster pinned via
    ///    [`Blocklace::enroll_pq`], never a self-carried key). The unsigned
    ///    sentinel, any forged/mismatched half, and an unenrolled creator are
    ///    rejected fail-closed: [`InsertError::Unsigned`] /
    ///    [`InsertError::BadSignature`] / [`InsertError::BadPqSignature`] /
    ///    [`InsertError::UnenrolledCreator`].
    /// 2. **Causal closure** — all predecessors must already be present
    ///    ([`InsertError::MissingPredecessors`]).
    /// 3. **Sequence monotonicity** — the block's `sequence` must strictly
    ///    exceed the creator's current tip sequence; it may not regress or
    ///    repeat ([`InsertError::SeqRegression`]).
    /// 4. **No silent equivocation** — if a *different* block already exists at
    ///    this `(creator, sequence)`, the new block is **retained as detectable
    ///    evidence** (not used to overwrite the tip), an [`EquivocationProof`]
    ///    is recorded, the creator's tip is withdrawn, and
    ///    [`InsertError::Equivocation`] is returned. The fork is never lost.
    ///
    /// Returns `Ok(block_id)` if the block was inserted (or already exists).
    pub fn insert(&mut self, block: Block) -> Result<BlockId, InsertError> {
        let block_id = block.id();

        // Already have it (idempotent).
        if self.blocks.contains_key(&block_id) {
            return Ok(block_id);
        }

        // (1) Authenticity: HYBRID verification — ed25519 against `creator`
        // AND ML-DSA-65 PINNED to the creator's ENROLLED roster key. A creator
        // with no enrolled PQ key is rejected (fail-closed): we never trust a
        // self-carried or on-the-fly-derived key for the post-quantum half.
        match self.pq_roster.get(&block.creator) {
            Some(enrolled_pq) => block.verify_signature(enrolled_pq)?,
            None => {
                return Err(InsertError::UnenrolledCreator {
                    creator: block.creator,
                    sequence: block.sequence,
                });
            }
        }

        // (2) Causal closure: all predecessors must be present.
        let missing: Vec<BlockId> = block
            .predecessors
            .iter()
            .filter(|p| !self.blocks.contains_key(*p))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(InsertError::MissingPredecessors(missing));
        }

        // (4) Equivocation: a distinct block already present at this
        // (creator, sequence) is a fork. Scan the creator's stored blocks for a
        // same-sequence, different-id block. (Same-creator blocks are sparse;
        // this is the strand-level dual of `ordering.rs::EquivocationIndex::
        // equivocates_in_past` (renamed from `has_equivocation_in_past`; corrected
        // 2026-07-16), which groups same-creator blocks by round and flags `len > 1`.)
        if let Some(existing_id) = self.find_conflict(&block, block_id) {
            // Retain the conflicting block as DETECTABLE EVIDENCE — do NOT
            // overwrite the tip (the old bug silently replaced tips[creator]).
            self.store_block(block_id, &block);
            self.blocks.insert(block_id, block.clone());
            // Withdraw the creator's honest feed head: there is no single tip.
            self.equivocators.insert(block.creator);
            self.tips.remove(&block.creator);
            let proof = EquivocationProof {
                creator: block.creator,
                sequence: block.sequence,
                existing: existing_id,
                conflicting: block_id,
            };
            self.equivocation_proofs.push(proof.clone());
            return Err(InsertError::Equivocation(proof));
        }

        // (3) Sequence monotonicity: the block must extend the creator's chain.
        // (Skipped for a creator already known to equivocate — they have no
        // honest tip to extend, but the evidence is still retained above.)
        if !self.equivocators.contains(&block.creator)
            && let Some(&tip_seq) = self.tip_sequence.get(&block.creator)
            && block.sequence <= tip_seq
        {
            return Err(InsertError::SeqRegression {
                creator: block.creator,
                attempted: block.sequence,
                tip_sequence: tip_seq,
            });
        }

        // All checks passed: link, record the tip, and store.
        self.store_block(block_id, &block);
        if !self.equivocators.contains(&block.creator) {
            self.tips.insert(block.creator, block_id);
            self.tip_sequence.insert(block.creator, block.sequence);
        }
        self.blocks.insert(block_id, block);

        Ok(block_id)
    }

    /// Insert a block WITHOUT signature/sequence/equivocation enforcement.
    ///
    /// This is the **unsigned ordering projection** path: the node mirrors
    /// already-finalized, already-authenticated blocks (from the live
    /// `finality.rs` lace) into a `lib::Blocklace` purely to run `ordering::tau`
    /// over them. Those mirror blocks are unsigned skeletons by construction
    /// (`node/blocklace_sync.rs` rebuilds them from finality blocks) and carry
    /// no wire authority, so feed-integrity does not apply — only causal closure
    /// does. It does NOT touch the wire and is never the reception path.
    ///
    /// Returns `Err(missing)` if predecessors are absent. Like the old `insert`,
    /// it overwrites the tip — acceptable here because the source lace already
    /// enforced integrity.
    pub fn insert_unverified(&mut self, block: Block) -> Result<BlockId, Vec<BlockId>> {
        self.insert_ordering_projection(block.id(), block)
    }

    /// Store an authenticated source block's unsigned ordering projection under its SOURCE id.
    /// The source id, not the hash of the lossy skeleton, is the consensus tie-break.
    /// Callers must authenticate the source first; this is never a reception API.
    /// Predecessors must use source ids too. No signature or content-hash check is performed.
    pub fn insert_ordering_projection(
        &mut self,
        block_id: BlockId,
        block: Block,
    ) -> Result<BlockId, Vec<BlockId>> {
        if self.blocks.contains_key(&block_id) {
            return Ok(block_id);
        }
        let missing: Vec<BlockId> = block
            .predecessors
            .iter()
            .filter(|p| !self.blocks.contains_key(*p))
            .copied()
            .collect();
        if !missing.is_empty() {
            return Err(missing);
        }
        self.store_block(block_id, &block);
        self.tips.insert(block.creator, block_id);
        self.tip_sequence
            .entry(block.creator)
            .and_modify(|s| *s = (*s).max(block.sequence))
            .or_insert(block.sequence);
        self.blocks.insert(block_id, block);
        Ok(block_id)
    }

    /// Wire frontier/successor edges for a newly-accepted block.
    fn store_block(&mut self, block_id: BlockId, block: &Block) {
        for pred in &block.predecessors {
            self.frontier.remove(pred);
            self.successors.entry(*pred).or_default().insert(block_id);
        }
        self.frontier.insert(block_id);
        self.successors.entry(block_id).or_default();
        // First-wins: keep the canonical (earliest stored) block at this
        // (creator, sequence). A later equivocating block does NOT overwrite
        // the witness the conflict check returns.
        self.by_creator_seq
            .entry((block.creator, block.sequence))
            .or_insert(block_id);
    }

    /// Find a stored block by the same creator at the same sequence with a
    /// different id (the fork witness). Returns the existing block's id.
    fn find_conflict(&self, block: &Block, block_id: BlockId) -> Option<BlockId> {
        // O(1) via the reverse index: the canonical (first-stored) block at
        // this (creator, sequence), if any, distinct from the candidate.
        // Equivalent to the historical full scan — that scan returned an
        // arbitrary same-(creator, sequence) block with a different id; the
        // index returns the canonical witness, which is exactly such a block.
        match self.by_creator_seq.get(&(block.creator, block.sequence)) {
            Some(&id) if id != block_id => Some(id),
            _ => None,
        }
    }

    /// Creators caught equivocating (a fork was detected on insert).
    pub fn equivocators(&self) -> &HashSet<NodeKey> {
        &self.equivocators
    }

    /// All recorded equivocation proofs (attributable, detectable fork evidence).
    pub fn equivocation_proofs(&self) -> &[EquivocationProof] {
        &self.equivocation_proofs
    }

    /// The highest accepted sequence number for a creator (its strand length).
    pub fn tip_sequence_for(&self, creator: &NodeKey) -> Option<u64> {
        self.tip_sequence.get(creator).copied()
    }

    /// Check if a block exists in the blocklace.
    pub fn contains(&self, block_id: &BlockId) -> bool {
        self.blocks.contains_key(block_id)
    }

    /// Get a block by its ID.
    pub fn get(&self, block_id: &BlockId) -> Option<&Block> {
        self.blocks.get(block_id)
    }

    /// Get the current frontier (blocks with no successors).
    pub fn frontier(&self) -> &HashSet<BlockId> {
        &self.frontier
    }

    /// The forward (successor) edges of a block: every stored block that names
    /// `block_id` as a direct predecessor. Returns `None` if the block is
    /// unknown. This is the reverse of the predecessor links, maintained on
    /// insert; it lets referenced-by queries avoid a full block scan.
    pub fn successors_of(&self, block_id: &BlockId) -> Option<&HashSet<BlockId>> {
        self.successors.get(block_id)
    }

    /// Get the tip (latest block) for a given creator.
    pub fn tip_for(&self, creator: &NodeKey) -> Option<&BlockId> {
        self.tips.get(creator)
    }

    /// Get all tips (latest block per creator).
    pub fn tips(&self) -> &HashMap<NodeKey, BlockId> {
        &self.tips
    }

    /// Number of blocks in the blocklace.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the blocklace is empty.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get all block IDs.
    pub fn block_ids(&self) -> HashSet<BlockId> {
        self.blocks.keys().copied().collect()
    }

    /// Get the causal past (all ancestors) of a block, inclusive of the block itself.
    pub fn causal_past(&self, block_id: &BlockId) -> HashSet<BlockId> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(*block_id);

        while let Some(current) = queue.pop_front() {
            if !result.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !result.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }

        result
    }

    /// Union of the causal pasts of several blocks (inclusive of each given
    /// block), computed in a SINGLE shared-visited traversal.
    ///
    /// Equal to `ids.flat_map(|id| self.causal_past(id))` collected into one
    /// set, but each ancestor is visited once total instead of once per
    /// overlapping starting block — the common case for converging DAG tips,
    /// where pasts share most of their history. Unknown ids contribute only
    /// themselves (matching `causal_past`, which inserts the queried id before
    /// looking it up).
    pub fn causal_past_union<'a, I>(&self, ids: I) -> HashSet<BlockId>
    where
        I: IntoIterator<Item = &'a BlockId>,
    {
        let mut result = HashSet::new();
        let mut queue: VecDeque<BlockId> = VecDeque::new();
        for id in ids {
            queue.push_back(*id);
        }
        while let Some(current) = queue.pop_front() {
            if !result.insert(current) {
                continue;
            }
            if let Some(block) = self.blocks.get(&current) {
                for pred in &block.predecessors {
                    if !result.contains(pred) {
                        queue.push_back(*pred);
                    }
                }
            }
        }
        result
    }

    /// Return blocks in topological order (predecessors before dependents).
    pub fn topological_order(&self) -> Vec<BlockId> {
        let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
        for (id, block) in &self.blocks {
            let pred_count = block
                .predecessors
                .iter()
                .filter(|p| self.blocks.contains_key(*p))
                .count();
            in_degree.insert(*id, pred_count);
        }

        let mut queue: VecDeque<BlockId> = VecDeque::new();
        let mut initial: Vec<BlockId> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&id, _)| id)
            .collect();
        initial.sort();
        queue.extend(initial);

        let mut result = Vec::with_capacity(self.blocks.len());
        while let Some(block_id) = queue.pop_front() {
            result.push(block_id);
            if let Some(succs) = self.successors.get(&block_id) {
                let mut next: Vec<BlockId> = Vec::new();
                for succ in succs {
                    if let Some(deg) = in_degree.get_mut(succ) {
                        *deg -= 1;
                        if *deg == 0 {
                            next.push(*succ);
                        }
                    }
                }
                next.sort();
                queue.extend(next);
            }
        }

        result
    }

    /// Get blocks in topological order, filtered to only include the given set.
    pub fn topological_subset(&self, subset: &HashSet<BlockId>) -> Vec<BlockId> {
        self.topological_order()
            .into_iter()
            .filter(|id| subset.contains(id))
            .collect()
    }
}

#[cfg(test)]
mod finality_tests;

#[cfg(test)]
pub(crate) mod test_committee;

#[cfg(test)]
mod tests {
    use super::*;

    use crate::test_committee;

    /// A deterministic signing key per creator byte (so `creator` byte ↔ key).
    fn key_for(creator: u8) -> SigningKey {
        test_committee::signing_key(creator)
    }

    /// A signed block whose `creator` is the pubkey of `key_for(creator)`.
    ///
    /// Signed through the shared test committee, so authoring a block costs a
    /// signature rather than a signature plus a full ML-DSA-65 keygen. The bytes
    /// are identical to `Block::new_signed(&key_for(creator), ..)`.
    fn make_block(creator: u8, seq: u64, preds: Vec<BlockId>, payload: &[u8]) -> Block {
        Block::new_signed_by(
            test_committee::signer(creator),
            seq,
            preds,
            payload.to_vec(),
        )
    }

    /// A blocklace with the deterministic test creators (`key_for(0..=32)`)
    /// pre-enrolled in the ML-DSA roster — so hybrid `insert` can PIN their
    /// post-quantum halves. Every `make_block(c, ..)` used below has `c <= 32`.
    fn test_lace() -> Blocklace {
        let mut lace = Blocklace::new();
        for c in 0u8..=32 {
            let signer = test_committee::signer(c);
            lace.enroll_pq(signer.ed25519(), signer.pq_public_key().clone());
        }
        lace
    }

    #[test]
    fn block_id_deterministic() {
        let b = make_block(1, 0, vec![], b"hello");
        let id1 = b.id();
        let id2 = b.id();
        assert_eq!(id1, id2);
    }

    #[test]
    fn block_id_varies_on_content() {
        let b1 = make_block(1, 0, vec![], b"hello");
        let b2 = make_block(1, 0, vec![], b"world");
        assert_ne!(b1.id(), b2.id());
    }

    #[test]
    fn insert_genesis() {
        let mut lace = test_lace();
        let b = make_block(1, 0, vec![], b"genesis");
        let id = lace.insert(b).unwrap();
        assert!(lace.contains(&id));
        assert_eq!(lace.len(), 1);
        assert!(lace.frontier().contains(&id));
    }

    #[test]
    fn insert_with_predecessor() {
        let mut lace = test_lace();
        let b1 = make_block(1, 0, vec![], b"first");
        let id1 = lace.insert(b1).unwrap();

        let b2 = make_block(1, 1, vec![id1], b"second");
        let id2 = lace.insert(b2).unwrap();

        assert_eq!(lace.len(), 2);
        assert!(!lace.frontier().contains(&id1));
        assert!(lace.frontier().contains(&id2));
    }

    #[test]
    fn insert_missing_predecessor_fails() {
        let mut lace = test_lace();
        let fake_pred = [0xAA; 32];
        let b = make_block(1, 0, vec![fake_pred], b"orphan");
        let err = lace.insert(b).unwrap_err();
        assert_eq!(
            err.missing_predecessors().map(|m| m.to_vec()),
            Some(vec![fake_pred])
        );
    }

    #[test]
    fn causal_past() {
        let mut lace = test_lace();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let past = lace.causal_past(&id3);
        assert!(past.contains(&id1));
        assert!(past.contains(&id2));
        assert!(past.contains(&id3));
        assert_eq!(past.len(), 3);
    }

    #[test]
    fn topological_order_respects_causality() {
        let mut lace = test_lace();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        let b2 = make_block(2, 0, vec![], b"b");
        let id2 = lace.insert(b2).unwrap();
        let b3 = make_block(1, 1, vec![id1, id2], b"c");
        let id3 = lace.insert(b3).unwrap();

        let order = lace.topological_order();
        let pos1 = order.iter().position(|x| *x == id1).unwrap();
        let pos2 = order.iter().position(|x| *x == id2).unwrap();
        let pos3 = order.iter().position(|x| *x == id3).unwrap();
        assert!(pos1 < pos3);
        assert!(pos2 < pos3);
    }

    #[test]
    fn tips_tracking() {
        let mut lace = test_lace();
        let creator = key_for(1).verifying_key().to_bytes();
        let b1 = make_block(1, 0, vec![], b"a");
        let id1 = lace.insert(b1).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), id1);
        assert_eq!(lace.tip_sequence_for(&creator), Some(0));

        let b2 = make_block(1, 1, vec![id1], b"b");
        let id2 = lace.insert(b2).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), id2);
        assert_eq!(lace.tip_sequence_for(&creator), Some(1));
    }

    #[test]
    fn duplicate_insert_is_idempotent() {
        let mut lace = test_lace();
        let b = make_block(1, 0, vec![], b"dup");
        let id1 = lace.insert(b.clone()).unwrap();
        let id2 = lace.insert(b).unwrap();
        assert_eq!(id1, id2);
        assert_eq!(lace.len(), 1);
    }

    // ─── Feed-integrity (A1 fix) tests ───────────────────────────────────────

    /// Unsigned blocks (the `Block::new` zero-signature sentinel) are rejected:
    /// the write path requires real Ed25519 authenticity.
    #[test]
    fn unsigned_block_rejected() {
        let mut lace = test_lace();
        let creator = key_for(1).verifying_key().to_bytes();
        let unsigned = Block::new(creator, 0, vec![], b"nosig".to_vec());
        assert!(!unsigned.is_signed());
        match lace.insert(unsigned) {
            Err(InsertError::Unsigned { .. }) => {}
            other => panic!("expected Unsigned rejection, got {other:?}"),
        }
        assert_eq!(lace.len(), 0, "unsigned block must not be stored");
    }

    /// A block whose signature does not verify against `creator` (forged/tampered)
    /// is rejected by real Ed25519 verification.
    #[test]
    fn bad_signature_rejected() {
        let mut lace = test_lace();
        // Sign with key 1, then claim a *different* payload so the signature no
        // longer matches the recomputed id (tamper after signing).
        let mut tampered = make_block(1, 0, vec![], b"original");
        tampered.payload = b"tampered".to_vec(); // id changes, signature stale
        assert!(tampered.is_signed());
        match lace.insert(tampered) {
            Err(InsertError::BadSignature { .. }) => {}
            other => panic!("expected BadSignature rejection, got {other:?}"),
        }

        // Also: an ed25519 signature by the WRONG key for this creator is
        // rejected. Give it a (syntactically present) PQ half so it reaches the
        // ed25519 check — the classical half fails because creator 1 did not
        // produce it.
        let mut wrong_signer = Block::new(
            key_for(1).verifying_key().to_bytes(),
            0,
            vec![],
            b"x".to_vec(),
        );
        let sig = key_for(2).sign(&wrong_signer.id());
        wrong_signer.signature = sig.to_bytes(); // ed signed by 2, claims creator 1
        let (_pk, pq2) = pq::MlDsaSigningKey::from_seed(&key_for(2).to_bytes());
        wrong_signer.pq_signature = pq2.sign(&wrong_signer.id()).unwrap();
        match lace.insert(wrong_signer) {
            Err(InsertError::BadSignature { .. }) => {}
            other => panic!("expected BadSignature for wrong signer, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }

    /// A block whose sequence does not extend the creator's chain (regresses to
    /// or below the current tip sequence) is rejected.
    #[test]
    fn seq_regression_rejected() {
        let mut lace = test_lace();
        let creator = key_for(1).verifying_key().to_bytes();

        let g0 = make_block(1, 0, vec![], b"g0");
        let id0 = lace.insert(g0).unwrap();
        let g1 = make_block(1, 5, vec![id0], b"g1"); // jump to seq 5 (allowed: strictly >)
        let id1 = lace.insert(g1).unwrap();
        assert_eq!(lace.tip_sequence_for(&creator), Some(5));

        // A new block at seq 3 (< tip, and no block occupies seq 3) regresses:
        // it does not extend the creator's append-only chain. (A *different*
        // block at an already-occupied seq is an equivocation, tested
        // separately; regression is the un-occupied below-tip case.)
        let stale_lt = make_block(1, 3, vec![id1], b"stale-lt");
        match lace.insert(stale_lt) {
            Err(InsertError::SeqRegression {
                attempted: 3,
                tip_sequence: 5,
                ..
            }) => {}
            other => panic!("expected SeqRegression(3 vs 5), got {other:?}"),
        }

        // A new block at seq 2 (also < tip, unoccupied) likewise regresses.
        let stale_lt2 = make_block(1, 2, vec![id0], b"stale-lt2");
        match lace.insert(stale_lt2) {
            Err(InsertError::SeqRegression {
                attempted: 2,
                tip_sequence: 5,
                ..
            }) => {}
            other => panic!("expected SeqRegression(2 vs 5), got {other:?}"),
        }

        // The honest tip is unchanged and seq 6 still extends fine.
        assert_eq!(*lace.tip_for(&creator).unwrap(), id1);
        let g6 = make_block(1, 6, vec![id1], b"g6");
        assert!(lace.insert(g6).is_ok());
        assert_eq!(lace.tip_sequence_for(&creator), Some(6));
    }

    /// Equivocation (two distinct blocks at the same `(creator, sequence)`) is
    /// DETECTED, not silently lost: the conflicting block is retained as
    /// evidence, an attributable proof is recorded, and the creator's tip is
    /// withdrawn. This is the heart of the A1 fix — the old `insert` silently
    /// overwrote `tips[creator]` and kept both forks as live state.
    #[test]
    fn equivocation_detected_not_lost() {
        let mut lace = test_lace();
        let creator = key_for(9).verifying_key().to_bytes();

        // Shared genesis so both forks are causally closed.
        let g = make_block(1, 0, vec![], b"genesis");
        let gid = lace.insert(g).unwrap();

        // Two distinct seq-1 blocks by creator 9 (a fork).
        let f1 = make_block(9, 1, vec![gid], b"fork-a");
        let f1_id = lace.insert(f1).unwrap();
        assert_eq!(*lace.tip_for(&creator).unwrap(), f1_id);

        let f2 = make_block(9, 1, vec![gid], b"fork-b");
        let f2_id = f2.id();
        let err = lace.insert(f2).unwrap_err();

        // The fork is reported as an attributable, detectable proof.
        match &err {
            InsertError::Equivocation(proof) => {
                assert_eq!(proof.creator, creator);
                assert_eq!(proof.sequence, 1);
                assert_eq!(proof.existing, f1_id);
                assert_eq!(proof.conflicting, f2_id);
            }
            other => panic!("expected Equivocation, got {other:?}"),
        }

        // BOTH forked blocks are retained (evidence is never lost) — this is
        // exactly what `ordering.rs::EquivocationIndex::equivocates_in_past`
        // (renamed from `has_equivocation_in_past`; corrected 2026-07-16) scans for.
        assert!(lace.contains(&f1_id), "first fork retained");
        assert!(
            lace.contains(&f2_id),
            "conflicting fork retained as evidence"
        );

        // The creator is flagged and the honest tip is WITHDRAWN (no single
        // live feed head — the old bug left a silently-overwritten tip).
        assert!(lace.equivocators().contains(&creator));
        assert!(lace.tip_for(&creator).is_none(), "tip withdrawn on fork");
        assert_eq!(lace.equivocation_proofs().len(), 1);
    }

    /// `causal_past_union` must equal the set-union of per-block `causal_past`
    /// over a converging DAG (shared history) — the shared-visited traversal
    /// is only valid if it computes exactly that union.
    #[test]
    fn causal_past_union_equals_per_block_union() {
        let mut lace = test_lace();
        // Diamond + tails: a shared genesis, two mid blocks, a join, and
        // separate tips — so the tips' pasts overlap heavily.
        let g = make_block(1, 0, vec![], b"g");
        let gid = lace.insert(g).unwrap();
        let a = make_block(2, 0, vec![gid], b"a");
        let aid = lace.insert(a).unwrap();
        let b = make_block(3, 0, vec![gid], b"b");
        let bid = lace.insert(b).unwrap();
        let join = make_block(1, 1, vec![aid, bid], b"join");
        let jid = lace.insert(join).unwrap();
        let t1 = make_block(2, 1, vec![aid, jid], b"t1");
        let t1id = lace.insert(t1).unwrap();
        let t2 = make_block(3, 1, vec![bid, jid], b"t2");
        let t2id = lace.insert(t2).unwrap();

        let tips = [t1id, t2id, jid, aid];
        // Reference: union the per-block pasts.
        let mut reference: HashSet<BlockId> = HashSet::new();
        for id in &tips {
            reference.extend(lace.causal_past(id));
        }
        let union = lace.causal_past_union(tips.iter());
        assert_eq!(union, reference);

        // An unknown id contributes only itself (matches causal_past).
        let unknown = [0x77u8; 32];
        let with_unknown = lace.causal_past_union([&unknown, &t1id].into_iter());
        let mut ref2 = lace.causal_past(&unknown);
        ref2.extend(lace.causal_past(&t1id));
        assert_eq!(with_unknown, ref2);
    }

    /// Differential: the O(1) `find_conflict` index must agree with the
    /// historical O(n) linear scan over `blocks` for every candidate block —
    /// both on WHETHER a conflict exists and on returning a VALID conflict
    /// (same creator+sequence, different id). Drives a varied
    /// enqueue/equivocate sequence so the index is exercised in the presence
    /// of already-stored forks.
    #[test]
    fn find_conflict_matches_linear_scan() {
        // Reference: the original full-scan semantics.
        fn linear_scan(lace: &Blocklace, block: &Block, block_id: BlockId) -> Option<BlockId> {
            lace.blocks.iter().find_map(|(id, existing)| {
                if existing.creator == block.creator
                    && existing.sequence == block.sequence
                    && *id != block_id
                {
                    Some(*id)
                } else {
                    None
                }
            })
        }

        let mut lace = test_lace();
        let g = make_block(1, 0, vec![], b"genesis");
        let gid = lace.insert(g).unwrap();

        // A spread of candidate blocks: honest extensions, exact duplicates,
        // and deliberate forks at occupied (creator, sequence) positions.
        let mut candidates: Vec<Block> = Vec::new();
        for creator in 1u8..=4 {
            for seq in 0u64..4 {
                for payload in [b"x".as_slice(), b"y", b"z"] {
                    candidates.push(make_block(creator, seq, vec![gid], payload));
                }
            }
        }

        for cand in &candidates {
            let cid = cand.id();
            // Index result vs reference scan — existence must match exactly.
            let idx = lace.find_conflict(cand, cid);
            let scan = linear_scan(&lace, cand, cid);
            assert_eq!(
                idx.is_some(),
                scan.is_some(),
                "conflict existence disagreement for creator {:?} seq {}",
                cand.creator,
                cand.sequence
            );
            // When a conflict is reported, it must be a genuine fork witness:
            // same (creator, sequence), distinct id.
            if let Some(existing_id) = idx {
                assert_ne!(existing_id, cid);
                let existing = lace.blocks.get(&existing_id).expect("witness stored");
                assert_eq!(existing.creator, cand.creator);
                assert_eq!(existing.sequence, cand.sequence);
            }
            // Apply (insert is idempotent on dup id; equivocation path stores
            // the fork as evidence), keeping the live state advancing so later
            // candidates see prior forks.
            let _ = lace.insert(cand.clone());
        }
    }

    // ─── HYBRID PQ (ed25519 ∧ ML-DSA-65) enroll+PIN tests ────────────────────

    /// An honest hybrid block — creator signs both halves with its from-seed
    /// keys, verified against its ENROLLED ML-DSA key — passes, and is accepted
    /// by the strand-integrity `insert`.
    #[test]
    fn hybrid_honest_block_passes() {
        let creator_key = key_for(7);
        let enrolled = Block::pq_public_key(&creator_key);
        let block = Block::new_signed(&creator_key, 0, vec![], b"honest".to_vec());
        assert!(block.is_signed(), "hybrid block carries both halves");
        assert!(
            !block.pq_signature.is_empty(),
            "PQ half is present (~{} bytes)",
            pq::SIG_LEN
        );
        // Direct block-verify against the enrolled key.
        assert!(block.verify_signature(&enrolled).is_ok());
        // And through the pinned write path.
        let mut lace = test_lace();
        assert!(lace.insert(block).is_ok());
    }

    /// THE adversarial test: a block with a VALID ed25519 half from committee
    /// member P, but an ML-DSA half signed under an ATTACKER's OWN fresh ML-DSA
    /// key (≠ P's enrolled key) MUST be rejected. This is the quantum-adversary
    /// scenario: the classical half is (assume) forgeable, but the PQ half is
    /// pinned to P's enrolled key, which the attacker does not hold.
    #[test]
    fn hybrid_attacker_pq_key_rejected() {
        let p_key = key_for(7); // committee member P (ed25519 identity)
        let p_enrolled = Block::pq_public_key(&p_key); // P's ENROLLED ML-DSA key

        // Build an HONEST-LOOKING block: valid ed25519 half by P over id().
        let mut forged = Block::new(
            p_key.verifying_key().to_bytes(),
            0,
            vec![],
            b"inject".to_vec(),
        );
        let ed_sig = p_key.sign(&forged.id());
        forged.signature = ed_sig.to_bytes(); // ed25519 half is genuinely P's

        // The ATTACKER controls the PQ half but NOT P's from-seed ML-DSA key.
        // They generate their own ML-DSA key (a different seed) and sign the id.
        let attacker_seed = [0xAB_u8; 32];
        let (attacker_pq_pub, attacker_pq_sk) = pq::MlDsaSigningKey::from_seed(&attacker_seed);
        forged.pq_signature = attacker_pq_sk.sign(&forged.id()).unwrap();
        assert_ne!(
            attacker_pq_pub, p_enrolled,
            "attacker key must differ from P's enrolled key"
        );

        // The forged PQ half is a VALID ML-DSA signature — under the ATTACKER's
        // key. It MUST NOT verify against P's ENROLLED key.
        assert!(
            attacker_pq_pub.verify(&forged.id(), &forged.pq_signature),
            "sanity: the forged sig is valid under the attacker's own key"
        );
        match forged.verify_signature(&p_enrolled) {
            Err(InsertError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature, got {other:?}"),
        }

        // And it is rejected by the pinned write path (P is enrolled correctly).
        let mut lace = test_lace();
        match lace.insert(forged) {
            Err(InsertError::BadPqSignature { .. }) => {}
            other => panic!("expected BadPqSignature on insert, got {other:?}"),
        }
        assert_eq!(lace.len(), 0, "forged block must not be stored");
    }

    /// A block with a missing / empty PQ half fails CLOSED (never treated as a
    /// valid ed25519-only block).
    #[test]
    fn hybrid_missing_pq_half_fails_closed() {
        let p_key = key_for(7);
        let enrolled = Block::pq_public_key(&p_key);

        // Valid ed25519 half, but NO PQ half (the empty sentinel).
        let mut ed_only = Block::new(p_key.verifying_key().to_bytes(), 0, vec![], b"x".to_vec());
        let ed_sig = p_key.sign(&ed_only.id());
        ed_only.signature = ed_sig.to_bytes();
        assert!(ed_only.pq_signature.is_empty());
        assert!(!ed_only.is_signed(), "empty PQ half ⇒ not fully signed");
        match ed_only.verify_signature(&enrolled) {
            Err(InsertError::Unsigned { .. }) => {}
            other => panic!("expected Unsigned (fail-closed), got {other:?}"),
        }
        let mut lace = test_lace();
        match lace.insert(ed_only) {
            Err(InsertError::Unsigned { .. }) => {}
            other => panic!("expected Unsigned on insert, got {other:?}"),
        }
    }

    /// A creator with NO enrolled ML-DSA key is rejected fail-closed — the
    /// write path never trusts a self-carried or on-the-fly-derived PQ key.
    #[test]
    fn hybrid_unenrolled_creator_rejected() {
        // A fully-valid hybrid block by creator 200, but the lace has NOT
        // enrolled 200 (test_lace only enrolls 0..=32).
        let block = Block::new_signed(&key_for(200), 0, vec![], b"stranger".to_vec());
        assert!(block.is_signed());
        let mut lace = test_lace();
        match lace.insert(block) {
            Err(InsertError::UnenrolledCreator { .. }) => {}
            other => panic!("expected UnenrolledCreator, got {other:?}"),
        }
        assert_eq!(lace.len(), 0);
    }
}
