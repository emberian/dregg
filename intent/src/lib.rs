//! Distributed Intent Engine for Pyana.
//!
//! # Trust Model
//!
//! This crate is **TRANSITIONING** from executor-trusted to trustless.
//!
//! ## Current State: Executor-Trusted
//! - **Matching** ([`matcher`]): The executor currently evaluates intent matches. A
//!   compromised executor could suppress valid matches or forge fake ones.
//! - **Solver** ([`solver`]): Ring trade discovery runs on the executor. A malicious
//!   executor could front-run, censor, or produce suboptimal solutions.
//! - **Fulfillment** ([`fulfillment`]): Match proofs are verified by the executor.
//!
//! ## Target State: Trustless (see [`trustless`])
//! The [`trustless`] module implements the 7-layer protocol that removes executor trust:
//! 1. Intents are threshold-encrypted (no party can read before collective decryption)
//! 2. Batch boundaries determined by consensus (no manipulation of intent ordering)
//! 3. Solvers produce STARK proofs of solution validity (verifiable by anyone)
//! 4. Challenge windows with bond slashing enforce optimal solutions
//! 5. Atomic settlement via compound turns
//!
//! ## Soundness
//! - Privacy: Intent matching is local (wallet-side Datalog evaluation reveals nothing)
//! - Anti-censorship: Gossip propagation with stake proofs prevents suppression
//! - Fair ordering: (trustless path) threshold encryption prevents front-running
//!
//! ## Assumptions
//! - (Current) Federation executor honestly evaluates matches and solves rings
//! - (Trustless) Threshold t-of-n assumption for decryption ceremony
//! - Stake proofs bind to real notes (Poseidon2 Merkle inclusion)
//!
//! ## Verifiable by
//! - (Current) Federation members via replication
//! - (Trustless) Anyone, via STARK proof of solution validity
//!
//! The intent engine inverts the capability discovery model. Instead of pages/services
//! needing to know exactly what capability to request, they broadcast what they NEED
//! or OFFER, and wallets privately match against held capabilities.
//!
//! # Architecture
//!
//! ```text
//! Page/Service                    Gossip Network                  Wallet
//!     |                                |                            |
//!     |--- postIntent(MatchSpec) ----->|--- broadcast(Intent) ----->|
//!     |                                |                            | (local Datalog eval)
//!     |                                |                            | match_intent()
//!     |                                |                            |
//!     |<---- fulfillment (direct) -----|<--- fulfill(Match) --------|
//!     |                                |                            |
//! ```
//!
//! # Privacy model
//!
//! - **Intents are public**: Everyone sees "someone needs capability X for resource Y".
//!   The creator is anonymous (identified only by a commitment, not an identity).
//! - **Matching is private**: The wallet evaluates "can I satisfy this?" using local
//!   Datalog evaluation, without revealing what it holds.
//! - **Fulfillment is private**: The proof reveals only "yes I can satisfy this intent"
//!   -- not what token, what delegation chain, or what else you hold.
//!
//! This IS the progressive disclosure story applied to discovery.

pub mod commit_reveal_fulfillment;
pub mod delay_pool;
pub mod exchange;
pub mod fulfillment;
pub mod generalized;
pub mod gossip;
pub mod lowering;
pub mod matcher;
pub mod partial_fill;
pub mod pir;
pub mod solver;
pub mod sse;
pub mod trustless;
pub mod validation;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Type alias for intent identifiers (content-addressed BLAKE3 hashes).
pub type IntentId = [u8; 32];

/// Constraints governing how an intent may be partially filled.
///
/// For AMM/DEX scenarios, intents often need partial fills: "sell 100 tokens but
/// accept any amount >= 10" or "buy at this price, fill as much as you can."
///
/// When `fill_constraints` is `None` on an intent, the intent is all-or-nothing
/// (legacy behavior). When present, the matcher may produce partial fills.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FillConstraints {
    /// Minimum acceptable partial fill amount. A match providing less than this
    /// is rejected outright.
    pub min_fill_amount: u64,
    /// Maximum fill amount (usually == total desired quantity).
    pub max_fill_amount: u64,
    /// If true, the intent must be filled entirely or not at all (no partials).
    /// This is equivalent to setting `min_fill_amount == max_fill_amount` but
    /// is explicit for clarity and gas-efficient checking.
    pub fill_or_kill: bool,
    /// After a partial fill, this is set to the ID of the residual intent that
    /// tracks the remaining unfilled quantity. `None` before first partial fill.
    pub remaining_after_fill: Option<IntentId>,
    /// Tracks how many times this intent has been split via residual creation.
    /// Incremented each time a residual is spawned. Used to bound the residual
    /// chain depth and prevent unbounded DoS via repeated 1-unit fills.
    #[serde(default)]
    pub generation: u16,
}

/// Maximum depth of the residual chain. After this many splits, no further
/// residuals are created (preventing unbounded chain DoS).
pub const MAX_RESIDUAL_DEPTH: u16 = 10;

/// After this generation, residuals require a fresh stake proof (preventing
/// unlimited free riding on the original stake).
pub const FRESH_STAKE_GENERATION: u16 = 3;

/// Error returned when constructing `FillConstraints` with invalid parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FillConstraintsError {
    /// min_fill_amount is zero (allows zero-value fills).
    ZeroMinFillAmount,
    /// min_fill_amount exceeds max_fill_amount.
    MinExceedsMax { min: u64, max: u64 },
}

impl std::fmt::Display for FillConstraintsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ZeroMinFillAmount => write!(f, "min_fill_amount must be > 0"),
            Self::MinExceedsMax { min, max } => {
                write!(
                    f,
                    "min_fill_amount ({}) must be <= max_fill_amount ({})",
                    min, max
                )
            }
        }
    }
}

impl std::error::Error for FillConstraintsError {}

impl FillConstraints {
    /// Construct validated FillConstraints.
    ///
    /// Enforces:
    /// - `min_fill_amount > 0` (zero-value fills are rejected)
    /// - `min_fill_amount <= max_fill_amount`
    pub fn new(min: u64, max: u64, fill_or_kill: bool) -> Result<Self, FillConstraintsError> {
        if min == 0 {
            return Err(FillConstraintsError::ZeroMinFillAmount);
        }
        if min > max {
            return Err(FillConstraintsError::MinExceedsMax { min, max });
        }
        Ok(Self {
            min_fill_amount: min,
            max_fill_amount: max,
            fill_or_kill,
            remaining_after_fill: None,
            generation: 0,
        })
    }
}

/// A predicate requirement for cross-party verification.
///
/// When a cell posts an intent with predicate requirements, any fulfiller must
/// provide a cryptographic proof that they satisfy each predicate WITHOUT
/// revealing the exact value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PredicateRequirement {
    /// The attribute being proven about (e.g., "balance", "reputation").
    pub attribute: String,
    /// The type of predicate: "gte", "lte", "gt", "lt", "neq", "in_range".
    pub predicate_type: String,
    /// The public threshold for comparison predicates.
    pub threshold: u64,
    /// For "in_range" predicates: the upper bound. Ignored for other types.
    #[serde(default)]
    pub upper_bound: Option<u64>,
    /// Maximum age of the state root in blocks.
    pub state_root_freshness: u64,
}

/// A commitment to an anonymous creator identity.
/// This is NOT a public key -- it's a blinded commitment that can only be
/// opened by the creator. Two intents from the same creator have different
/// CommitmentIds unless they choose to link them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CommitmentId(pub [u8; 32]);

impl CommitmentId {
    /// Generate a fresh random commitment ID.
    pub fn random() -> Self {
        let mut bytes = [0u8; 32];
        getrandom(&mut bytes);
        Self(bytes)
    }

    /// Derive a commitment from a secret and a domain separator.
    pub fn derive(secret: &[u8], domain: &str) -> Self {
        let hash = blake3::derive_key(domain, secret);
        Self(hash)
    }
}

/// A cryptographic proof that a note commitment exists in the Poseidon2 note tree.
///
/// This proves the staker has knowledge of a real note (not just random bytes) by
/// providing a Merkle inclusion proof against the federation's attested note tree root.
///
/// Privacy: This does NOT reveal the note value (that would require opening the commitment,
/// breaking privacy). It only proves the note EXISTS in the tree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StakeProof {
    /// The note commitment being staked.
    pub commitment: pyana_cell::NoteCommitment,
    /// The Poseidon2 Merkle tree root that this proof is valid against.
    pub merkle_root: pyana_circuit::field::BabyBear,
    /// The Poseidon2 Merkle inclusion proof demonstrating the commitment is in the tree.
    pub merkle_proof: pyana_commit::Poseidon2MerkleProof,
    /// Claimed minimum value of the staked note (informational; cannot be verified
    /// without opening the commitment, but allows pool policies to filter).
    pub minimum_value: u64,
}

/// Stake requirement for intent propagation via gossip.
///
/// Intents that wish to propagate over the gossip network must have a committed
/// stake. Local-only intents (from the wallet's own page) may skip the stake
/// requirement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StakeRequirement {
    /// No stake required -- intent is local-only and will not be propagated via gossip.
    None,
    /// A full stake proof with Merkle inclusion against the note tree.
    Proven(StakeProof),
}

impl StakeRequirement {
    /// Check whether this requirement includes a valid stake against a known root.
    pub fn has_valid_stake(&self, known_root: pyana_circuit::field::BabyBear) -> bool {
        match self {
            Self::None => false,
            Self::Proven(proof) => verify_stake(proof, known_root),
        }
    }
}

/// Verify a stake proof against a known note tree root.
///
/// Checks:
/// 1. The proof's merkle_root matches the federation's attested note tree root.
/// 2. The note commitment's field-element representation is a valid member of the tree
///    (via Poseidon2 Merkle proof verification).
///
/// This proves the staker has knowledge of a real note that EXISTS in the tree,
/// preventing spam from entities that have never committed real state.
pub fn verify_stake(stake: &StakeProof, known_root: pyana_circuit::field::BabyBear) -> bool {
    // The proof's root must match the federation's attested root
    if stake.merkle_root != known_root {
        return false;
    }

    // Convert the BLAKE3 note commitment to a Poseidon2 field element
    let leaf = pyana_commit::commitment_to_field(&stake.commitment.0);

    // Verify the Merkle inclusion proof
    pyana_commit::Poseidon2MerkleTree::verify_membership(known_root, leaf, &stake.merkle_proof)
}

/// Verify that an intent has a valid stake proof for gossip propagation.
///
/// Returns true if the intent carries a valid stake proof that verifies against
/// the given known note tree root.
pub fn verify_intent_stake(intent: &Intent, known_root: pyana_circuit::field::BabyBear) -> bool {
    match &intent.stake_proof {
        Some(proof) => verify_stake(proof, known_root),
        None => false,
    }
}

/// Verification mode for match proofs -- how much to reveal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationMode {
    /// Trusted: no proof, direct token presentation (fastest, least private).
    Trusted,
    /// Selective: prove specific facts about the token without revealing all.
    Selective,
    /// Private: full STARK proof that a valid token exists satisfying the intent.
    /// Reveals nothing about which token or what delegation chain.
    Private,
}

/// The kind of intent being broadcast.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntentKind {
    /// "I need a capability matching this spec" -- requesting authorization.
    Need,
    /// "I can provide a capability matching this spec" -- offering authorization.
    Offer,
    /// "Tell me if any matching capability exists" -- discovery query.
    Query,
}

/// A pattern matching a single action on a resource.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActionPattern {
    /// The action required/offered. None = wildcard (any action).
    pub action: Option<String>,
    /// The resource the action applies to. None = any resource.
    pub resource: Option<String>,
}

/// A constraint on matching, expressed in Datalog-compatible terms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Constraint {
    /// The token must grant access to this specific app.
    AppId(String),
    /// The token must grant access to this specific service.
    Service(String),
    /// The token must be valid for this user.
    UserId(String),
    /// The token must not be expired at this timestamp.
    NotExpiredAt(i64),
    /// The token must grant this feature.
    Feature(String),
    /// The token must have been issued by this OAuth provider.
    OAuthProvider(String),
    /// Custom predicate (for extensibility).
    Custom { predicate: String, value: String },
}

/// Specification of what capabilities are needed or offered.
///
/// This is the core matching language: a MatchSpec describes a "shape" of
/// capability that can be matched against held tokens.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchSpec {
    /// What actions are required/offered.
    pub actions: Vec<ActionPattern>,
    /// Datalog-style constraints that must be satisfied.
    pub constraints: Vec<Constraint>,
    /// Minimum budget required (if the intent involves budgeted resources).
    pub min_budget: Option<u64>,
    /// Glob or prefix pattern for resource matching.
    pub resource_pattern: Option<String>,
    /// Compound requirement: ALL of these sub-specs must be satisfiable
    /// by the same wallet (possibly from different tokens).
    #[serde(default)]
    pub compound: Option<Vec<MatchSpec>>,
    /// Cross-party predicate requirements.
    #[serde(default)]
    pub predicate_requirements: Vec<PredicateRequirement>,
    /// When true, resource matching is strict: wildcards ("*") in the
    /// `resource_pattern` are NOT allowed. The token's resource must exactly
    /// match the pattern (no glob expansion). This prevents a broad wildcard
    /// pattern from inadvertently matching narrow-scope tokens.
    ///
    /// Defaults to `false` for backward compatibility (wildcards are powerful
    /// and are the expected default behavior).
    #[serde(default)]
    pub strict_resource_matching: bool,
}

/// A broadcast intent: someone needs/offers/queries a capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Intent {
    /// Content-addressed ID: BLAKE3 hash of the serialized intent body.
    pub id: [u8; 32],
    /// What kind of intent this is.
    pub kind: IntentKind,
    /// What capabilities are needed/offered.
    pub matcher: MatchSpec,
    /// Anonymous creator commitment (not a public identity).
    pub creator: CommitmentId,
    /// Unix timestamp after which this intent expires and should be GC'd.
    pub expiry: u64,
    /// Optional stake proof demonstrating note tree membership (Poseidon2 Merkle proof).
    /// Required for gossip propagation; local intents may omit this.
    pub stake_proof: Option<StakeProof>,
    /// Optional partial fill constraints for AMM/DEX-style intents.
    /// When `None`, the intent is all-or-nothing (must be fully matched).
    /// When `Some`, the matcher may produce partial fills satisfying at least
    /// `min_fill_amount`.
    #[serde(default)]
    pub fill_constraints: Option<FillConstraints>,
}

impl Intent {
    /// Create a new intent, computing its content-addressed ID.
    pub fn new(
        kind: IntentKind,
        matcher: MatchSpec,
        creator: CommitmentId,
        expiry: u64,
        stake_proof: Option<StakeProof>,
    ) -> Self {
        let mut intent = Self {
            id: [0u8; 32],
            kind,
            matcher,
            creator,
            expiry,
            stake_proof,
            fill_constraints: None,
        };
        intent.id = intent.compute_id();
        intent
    }

    /// Create a new intent with fill constraints for partial fill support.
    pub fn new_with_fill(
        kind: IntentKind,
        matcher: MatchSpec,
        creator: CommitmentId,
        expiry: u64,
        stake_proof: Option<StakeProof>,
        fill_constraints: FillConstraints,
    ) -> Self {
        let mut intent = Self {
            id: [0u8; 32],
            kind,
            matcher,
            creator,
            expiry,
            stake_proof,
            fill_constraints: Some(fill_constraints),
        };
        intent.id = intent.compute_id();
        intent
    }

    /// Compute the content-addressed ID from the intent's fields.
    ///
    /// Uses canonical postcard serialization to ensure deterministic hashing
    /// that won't break if Debug formatting changes.
    fn compute_id(&self) -> [u8; 32] {
        // Serialize the semantically-relevant fields in a canonical order.
        // We build a struct specifically for hashing (excludes the `id` field itself).
        // The stake_proof commitment bytes are included in the ID for binding.
        #[derive(Serialize)]
        struct IntentBody<'a> {
            kind: &'a IntentKind,
            matcher: &'a MatchSpec,
            creator: &'a CommitmentId,
            expiry: u64,
            /// We hash the commitment bytes from the stake proof (if present) for ID binding.
            stake_commitment: Option<&'a [u8; 32]>,
            /// Fill constraints are part of the identity (different fill params = different intent).
            fill_constraints: Option<&'a FillConstraints>,
        }

        let body = IntentBody {
            kind: &self.kind,
            matcher: &self.matcher,
            creator: &self.creator,
            expiry: self.expiry,
            stake_commitment: self.stake_proof.as_ref().map(|sp| &sp.commitment.0),
            fill_constraints: self.fill_constraints.as_ref(),
        };

        let canonical = postcard::to_allocvec(&body).unwrap_or_default();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-intent-id-v2");
        hasher.update(&canonical);
        *hasher.finalize().as_bytes()
    }

    /// Check if this intent has expired.
    ///
    /// An intent is expired when `now >= expiry` (i.e., exactly-at-expiry counts
    /// as expired). This avoids fence-post issues where `expiry == now` would
    /// allow processing of an intent that should no longer be valid.
    pub fn is_expired(&self, now: u64) -> bool {
        now >= self.expiry
    }
}

/// A successful match: a held token can satisfy an intent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Match {
    /// The intent that was matched.
    pub intent_id: [u8; 32],
    /// Anonymous commitment of the satisfier.
    pub satisfier: CommitmentId,
    /// Optional STARK proof that the match is valid.
    pub proof: Option<Vec<u8>>,
    /// How much was revealed in the proof.
    pub mode: VerificationMode,
}

// ---------------------------------------------------------------------------
// Epoch-scoped stake nullifiers (anti-Sybil)
// ---------------------------------------------------------------------------

/// Number of blocks per epoch for stake nullifier scoping.
///
/// Each note commitment gets `MAX_STAKE_USES_PER_EPOCH` uses per epoch.
/// Different epochs produce different nullifiers, making cross-epoch uses
/// unlinkable for privacy.
pub const EPOCH_DURATION_BLOCKS: u64 = 1000;

/// Maximum number of times a single note commitment can be used as stake
/// within one epoch. After K uses, the stake is exhausted until the next epoch.
pub const MAX_STAKE_USES_PER_EPOCH: u32 = 5;

/// Compute the current epoch from the block height.
pub fn current_epoch(block_height: u64) -> u64 {
    block_height / EPOCH_DURATION_BLOCKS
}

/// Compute a stake nullifier for a given note commitment, epoch, and use counter.
///
/// The nullifier is: `Poseidon2(commitment_field_elements || epoch_elements || counter_element)`
///
/// Privacy properties:
/// - Different epochs produce different nullifiers (unlinkable across epochs)
/// - Within an epoch, the K uses are distinguishable but not linkable to other epochs
/// - The nullifier does not reveal the underlying note value
pub fn compute_stake_nullifier(commitment: &[u8; 32], epoch: u64, counter: u32) -> [u8; 32] {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2::hash_many;

    // Encode commitment as 8 field elements
    let commitment_elements = BabyBear::encode_hash(commitment);

    // Encode epoch as 2 field elements (high/low 32 bits)
    let epoch_lo = BabyBear::new((epoch & 0x7FFF_FFFF) as u32);
    let epoch_hi = BabyBear::new(((epoch >> 31) & 0x7FFF_FFFF) as u32);

    // Encode counter as 1 field element
    let counter_elem = BabyBear::new(counter);

    // Concatenate all elements and hash
    let mut elements = Vec::with_capacity(11);
    elements.extend_from_slice(&commitment_elements);
    elements.push(epoch_lo);
    elements.push(epoch_hi);
    elements.push(counter_elem);

    // Hash to get a single field element, then expand to 32 bytes deterministically
    // We use a domain-separated BLAKE3 hash of the Poseidon2 output to get 32 bytes
    let poseidon_output = hash_many(&elements);
    let mut hasher = blake3::Hasher::new_derive_key("pyana-stake-nullifier-v1");
    hasher.update(&poseidon_output.as_u32().to_le_bytes());
    // Include raw inputs in the BLAKE3 for collision resistance in the 32-byte domain
    hasher.update(commitment);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(&counter.to_le_bytes());
    *hasher.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Fill a buffer with random bytes (no-std compatible via getrandom).
pub(crate) fn getrandom(buf: &mut [u8]) {
    ::getrandom::fill(buf).expect("getrandom failed");
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::field::BabyBear;
    use pyana_commit::{Poseidon2MerkleTree, commitment_to_field};

    /// Helper: build a small Poseidon2 tree with some notes and return a valid StakeProof
    /// for a given note commitment.
    fn build_stake_proof(commitment: &pyana_cell::NoteCommitment) -> (StakeProof, BabyBear) {
        let mut tree = Poseidon2MerkleTree::with_depth(4);

        // Insert some other notes first
        for i in 0..5u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xAA;
            tree.append(commitment_to_field(&c));
        }

        // Insert the target commitment
        let leaf = commitment_to_field(&commitment.0);
        let pos = tree.append(leaf);

        // Insert more after
        for i in 10..15u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xBB;
            tree.append(commitment_to_field(&c));
        }

        let root = tree.root();
        let merkle_proof = tree.prove_membership(pos).unwrap();

        let stake_proof = StakeProof {
            commitment: *commitment,
            merkle_root: root,
            merkle_proof,
            minimum_value: 100,
        };

        (stake_proof, root)
    }

    #[test]
    fn intent_id_is_deterministic() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: Some("documents/*".into()),
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let creator = CommitmentId([0xAA; 32]);
        let i1 = Intent::new(IntentKind::Need, spec.clone(), creator, 1000, None);
        let i2 = Intent::new(IntentKind::Need, spec, creator, 1000, None);
        assert_eq!(i1.id, i2.id);
    }

    #[test]
    fn different_intents_have_different_ids() {
        let spec1 = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let spec2 = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("write".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let creator = CommitmentId([0xBB; 32]);
        let i1 = Intent::new(IntentKind::Need, spec1, creator, 1000, None);
        let i2 = Intent::new(IntentKind::Need, spec2, creator, 1000, None);
        assert_ne!(i1.id, i2.id);
    }

    #[test]
    fn intent_expiry_check() {
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let creator = CommitmentId([0xCC; 32]);
        let intent = Intent::new(IntentKind::Need, spec, creator, 1000, None);
        assert!(!intent.is_expired(500));
        assert!(!intent.is_expired(999));
        // Issue #8: exactly-at-expiry is now expired (fence-post fix)
        assert!(intent.is_expired(1000));
        assert!(intent.is_expired(1001));
    }

    #[test]
    fn commitment_id_derive_is_deterministic() {
        let c1 = CommitmentId::derive(b"secret", "test-domain");
        let c2 = CommitmentId::derive(b"secret", "test-domain");
        assert_eq!(c1, c2);

        let c3 = CommitmentId::derive(b"other", "test-domain");
        assert_ne!(c1, c3);
    }

    #[test]
    fn verify_stake_valid_proof() {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let (stake_proof, root) = build_stake_proof(&commitment);

        // Valid proof against the correct root
        assert!(verify_stake(&stake_proof, root));
    }

    #[test]
    fn verify_stake_wrong_root_fails() {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let (stake_proof, _root) = build_stake_proof(&commitment);

        // Wrong root should fail
        let wrong_root = BabyBear::new(0xBAD);
        assert!(!verify_stake(&stake_proof, wrong_root));
    }

    #[test]
    fn verify_stake_wrong_commitment_fails() {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let (_stake_proof, root) = build_stake_proof(&commitment);

        // Create a proof with a different commitment but same merkle_proof
        // (the proof won't verify because the leaf doesn't match)
        let wrong_commitment = pyana_cell::NoteCommitment([0xFF; 32]);
        let bad_stake = StakeProof {
            commitment: wrong_commitment,
            merkle_root: root,
            merkle_proof: _stake_proof.merkle_proof,
            minimum_value: 100,
        };
        assert!(!verify_stake(&bad_stake, root));
    }

    #[test]
    fn verify_intent_stake_with_proof() {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let (stake_proof, root) = build_stake_proof(&commitment);

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            9999,
            Some(stake_proof),
        );

        assert!(verify_intent_stake(&intent, root));
    }

    #[test]
    fn verify_intent_stake_none_fails() {
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);

        let root = BabyBear::new(42);
        assert!(!verify_intent_stake(&intent, root));
    }

    #[test]
    fn stake_requirement_has_valid_stake() {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let (stake_proof, root) = build_stake_proof(&commitment);

        let req = StakeRequirement::Proven(stake_proof);
        assert!(req.has_valid_stake(root));

        let req_none = StakeRequirement::None;
        assert!(!req_none.has_valid_stake(root));
    }

    #[test]
    fn current_epoch_computation() {
        assert_eq!(current_epoch(0), 0);
        assert_eq!(current_epoch(999), 0);
        assert_eq!(current_epoch(1000), 1);
        assert_eq!(current_epoch(1001), 1);
        assert_eq!(current_epoch(2000), 2);
        assert_eq!(current_epoch(5999), 5);
    }

    #[test]
    fn stake_nullifier_deterministic() {
        let commitment = [0xDE; 32];
        let n1 = compute_stake_nullifier(&commitment, 0, 0);
        let n2 = compute_stake_nullifier(&commitment, 0, 0);
        assert_eq!(n1, n2);
    }

    #[test]
    fn stake_nullifier_varies_by_epoch() {
        let commitment = [0xDE; 32];
        let n_epoch0 = compute_stake_nullifier(&commitment, 0, 0);
        let n_epoch1 = compute_stake_nullifier(&commitment, 1, 0);
        assert_ne!(
            n_epoch0, n_epoch1,
            "different epochs should produce different nullifiers"
        );
    }

    #[test]
    fn stake_nullifier_varies_by_counter() {
        let commitment = [0xDE; 32];
        let n0 = compute_stake_nullifier(&commitment, 5, 0);
        let n1 = compute_stake_nullifier(&commitment, 5, 1);
        let n2 = compute_stake_nullifier(&commitment, 5, 2);
        assert_ne!(n0, n1);
        assert_ne!(n1, n2);
        assert_ne!(n0, n2);
    }

    #[test]
    fn stake_nullifier_varies_by_commitment() {
        let c1 = [0xAA; 32];
        let c2 = [0xBB; 32];
        let n1 = compute_stake_nullifier(&c1, 0, 0);
        let n2 = compute_stake_nullifier(&c2, 0, 0);
        assert_ne!(
            n1, n2,
            "different commitments should produce different nullifiers"
        );
    }
}
