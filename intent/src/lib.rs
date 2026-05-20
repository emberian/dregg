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

/// Stake requirement for intent propagation via gossip.
///
/// Intents that wish to propagate over the gossip network must have a committed
/// stake. Local-only intents (from the wallet's own page) may skip the stake
/// requirement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StakeRequirement {
    /// No stake required -- intent is local-only and will not be propagated via gossip.
    None,
    /// A committed note stake, making the intent eligible for gossip propagation.
    /// The commitment must be well-formed (non-zero, correct length).
    Committed(pyana_cell::NoteCommitment),
}

impl StakeRequirement {
    /// Convert from the legacy `Option<NoteCommitment>` representation.
    pub fn from_option(opt: Option<pyana_cell::NoteCommitment>) -> Self {
        match opt {
            Some(commitment) => Self::Committed(commitment),
            None => Self::None,
        }
    }

    /// Check whether this requirement includes a valid stake.
    pub fn has_valid_stake(&self) -> bool {
        match self {
            Self::None => false,
            Self::Committed(c) => verify_stake_commitment(c),
        }
    }
}

/// Verify that a stake commitment is well-formed.
///
/// Checks:
/// - The commitment is non-zero (all-zeros would be an invalid/empty commitment)
/// - The commitment has proper length (always true for `[u8; 32]`, but checked for semantics)
pub fn verify_stake_commitment(commitment: &pyana_cell::NoteCommitment) -> bool {
    // Reject all-zeros as invalid
    commitment.0 != [0u8; 32]
}

/// Verify that an intent has a valid stake for gossip propagation.
///
/// Returns true if the intent carries a non-zero, well-formed note commitment.
pub fn verify_stake(intent: &Intent) -> bool {
    match &intent.proof_of_stake {
        Some(commitment) => verify_stake_commitment(commitment),
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
    /// Optional stake proving seriousness (a note commitment).
    pub proof_of_stake: Option<pyana_cell::NoteCommitment>,
}

impl Intent {
    /// Create a new intent, computing its content-addressed ID.
    pub fn new(
        kind: IntentKind,
        matcher: MatchSpec,
        creator: CommitmentId,
        expiry: u64,
        proof_of_stake: Option<pyana_cell::NoteCommitment>,
    ) -> Self {
        let mut intent = Self {
            id: [0u8; 32],
            kind,
            matcher,
            creator,
            expiry,
            proof_of_stake,
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
        #[derive(Serialize)]
        struct IntentBody<'a> {
            kind: &'a IntentKind,
            matcher: &'a MatchSpec,
            creator: &'a CommitmentId,
            expiry: u64,
            proof_of_stake: &'a Option<pyana_cell::NoteCommitment>,
        }

        let body = IntentBody {
            kind: &self.kind,
            matcher: &self.matcher,
            creator: &self.creator,
            expiry: self.expiry,
            proof_of_stake: &self.proof_of_stake,
        };

        let canonical = postcard::to_allocvec(&body).unwrap_or_default();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-intent-id-v1");
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
        };
        let spec2 = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("write".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
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
}
