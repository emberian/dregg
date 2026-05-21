//! Distributed Intent Engine for Pyana.
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

pub mod fulfillment;
pub mod gossip;
pub mod matcher;
pub mod validation;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
        }

        let body = IntentBody {
            kind: &self.kind,
            matcher: &self.matcher,
            creator: &self.creator,
            expiry: self.expiry,
            stake_commitment: self.stake_proof.as_ref().map(|sp| &sp.commitment.0),
        };

        let canonical = postcard::to_allocvec(&body).unwrap_or_default();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-intent-id-v2");
        hasher.update(&canonical);
        *hasher.finalize().as_bytes()
    }

    /// Check if this intent has expired.
    pub fn is_expired(&self, now: u64) -> bool {
        now > self.expiry
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
// Helpers
// ---------------------------------------------------------------------------

/// Fill a buffer with random bytes (no-std compatible via getrandom).
fn getrandom(buf: &mut [u8]) {
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
        };
        let creator = CommitmentId([0xCC; 32]);
        let intent = Intent::new(IntentKind::Need, spec, creator, 1000, None);
        assert!(!intent.is_expired(500));
        assert!(!intent.is_expired(1000));
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
}
