//! Escrow primitives: conditional settlement with timeout-based refund.
//!
//! An escrow locks value from a sender, releasing it to a recipient IF a condition
//! is satisfied, or returning it to the sender after a timeout. This enables
//! trustless exchange patterns like compute-for-payment.
//!
//! # Privacy-preserving escrow
//!
//! The [`CommittedEscrow`] variant hides all party identities and the escrowed
//! amount behind cryptographic commitments. For an anonymous marketplace:
//!
//! - **Creator/recipient identities** are hidden behind BLAKE3 commitments
//!   (hash of CellId + blinding factor).
//! - **Value** is hidden behind a Pedersen commitment (homomorphic, so
//!   conservation can still be verified without revealing the amount).
//! - **Condition** is hidden behind a commitment (hash of condition + nonce).
//!
//! Release and refund require proving knowledge of the commitment openings
//! (via signed statements in this initial implementation; full ZK release
//! requires a presentation proof bound to the escrow_id).

use pyana_cell::CellId;
use pyana_cell::ValueCommitmentBytes;
use serde::{Deserialize, Serialize};

/// The condition that must be satisfied to release an escrow.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum EscrowCondition {
    /// Recipient must present a ZK proof verified against this key.
    ProofPresented {
        /// The verification key that the proof must validate against.
        verification_key: [u8; 32],
    },
    /// Requires signatures from ALL listed parties.
    SignedByAll {
        /// The Ed25519 public keys of all required signers.
        signers: Vec<[u8; 32]>,
    },
    /// A predicate (identified by hash) evaluates to true against state.
    PredicateSatisfied {
        /// The BLAKE3 hash identifying the predicate.
        predicate_hash: [u8; 32],
    },
}

/// A record of an active escrow tracked by the executor (cleartext variant).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EscrowRecord {
    /// The escrow creator (who locked the funds).
    pub creator: CellId,
    /// The intended recipient (who receives funds on release).
    pub recipient: CellId,
    /// The locked amount.
    pub amount: u64,
    /// The condition required for release.
    pub condition: EscrowCondition,
    /// Block height after which refund is allowed.
    pub timeout_height: u64,
    /// Whether this escrow has been resolved (released or refunded).
    pub resolved: bool,
}

// ─── Privacy-Preserving Committed Escrow ─────────────────────────────────────

/// A privacy-preserving escrow record where parties and amounts are hidden
/// behind cryptographic commitments.
///
/// # Commitment scheme
///
/// - **Identity commitments**: `BLAKE3("pyana-escrow-identity-v1:" || cell_id || blinding)`
///   where `blinding` is a 32-byte random nonce known only to the committer.
/// - **Value commitment**: Pedersen commitment `v*V + r*R` (see [`pyana_cell::ValueCommitment`]).
///   Accompanied by a range proof to prevent negative-value inflation.
/// - **Condition commitment**: `BLAKE3("pyana-escrow-condition-v1:" || condition_bytes || nonce)`
///   where `condition_bytes` is the serialized condition and `nonce` is a 32-byte random value.
///
/// # Release protocol (initial implementation)
///
/// To release, the claimer provides an `EscrowClaimAuth` containing an Ed25519 signature
/// over the escrow_id, proving they control the key behind the recipient commitment.
/// The executor verifies this signature against the public key that was used to create
/// the recipient commitment (provided in the claim along with the blinding factor).
///
/// # Future: full ZK release
///
/// A full ZK release would replace `EscrowClaimAuth` with a STARK proof showing:
/// 1. "I know the opening of `recipient_commitment` matching my identity"
/// 2. "I know the opening of `condition_commitment` and the condition is satisfied"
///
/// This would avoid revealing the recipient's public key entirely, requiring only
/// a presentation proof bound to the `escrow_id`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommittedEscrow {
    /// Commitment to the creator's identity: BLAKE3(cell_id || blinding).
    pub creator_commitment: [u8; 32],
    /// Commitment to the recipient's identity: BLAKE3(cell_id || blinding).
    pub recipient_commitment: [u8; 32],
    /// Pedersen commitment to the escrowed value (compressed Ristretto point).
    pub value_commitment: ValueCommitmentBytes,
    /// Commitment to the escrow condition: BLAKE3(condition_bytes || nonce).
    pub condition_commitment: [u8; 32],
    /// Timeout height (public — needed for on-chain enforcement).
    pub timeout_height: u64,
    /// Deterministic escrow identifier (derived from commitments, not revealing).
    pub escrow_id: [u8; 32],
    /// Range proof for the value commitment, proving the committed value is
    /// in `[0, 2^64)` (prevents hidden inflation via negative values).
    pub range_proof: Vec<u8>,
    /// Whether this escrow has been resolved (released or refunded).
    pub resolved: bool,
}

/// Authorization proof for releasing or refunding a committed escrow.
///
/// Since the committed escrow hides party identities, the claimer must prove
/// they are the party named in the relevant commitment (recipient for release,
/// creator for refund).
///
/// # Initial implementation (signed statement)
///
/// The claimer reveals their public key and blinding factor, then provides an
/// Ed25519 signature over the escrow_id. The executor:
/// 1. Recomputes the commitment from (public_key, blinding) and checks it matches.
/// 2. Verifies the signature against the revealed public key.
///
/// This proves identity without requiring the escrow to store the cleartext key,
/// but does reveal the key to the executor at claim time.
///
/// # Future: ZK claim
///
/// Replace this with a presentation proof that proves knowledge of the opening
/// without revealing it. The executor only sees the proof + escrow_id.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EscrowClaimAuth {
    /// The claimer's Ed25519 public key (opening of the identity commitment).
    pub public_key: [u8; 32],
    /// The blinding factor used when creating the identity commitment.
    pub blinding: [u8; 32],
    /// Ed25519 signature over the escrow_id, proving control of `public_key`.
    pub signature: [u8; 64],
}

impl CommittedEscrow {
    /// Compute the deterministic escrow ID from the commitment fields.
    ///
    /// ```text
    /// escrow_id = BLAKE3("pyana-committed-escrow-id-v1:"
    ///     || creator_commitment || recipient_commitment
    ///     || value_commitment || condition_commitment
    ///     || timeout_height_le)
    /// ```
    pub fn compute_escrow_id(
        creator_commitment: &[u8; 32],
        recipient_commitment: &[u8; 32],
        value_commitment: &ValueCommitmentBytes,
        condition_commitment: &[u8; 32],
        timeout_height: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-committed-escrow-id-v1");
        hasher.update(creator_commitment);
        hasher.update(recipient_commitment);
        hasher.update(&value_commitment.0);
        hasher.update(condition_commitment);
        hasher.update(&timeout_height.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Verify that the escrow_id is correctly derived from the commitment fields.
    pub fn verify_id(&self) -> bool {
        let expected = Self::compute_escrow_id(
            &self.creator_commitment,
            &self.recipient_commitment,
            &self.value_commitment,
            &self.condition_commitment,
            self.timeout_height,
        );
        expected == self.escrow_id
    }
}

/// Compute an identity commitment for use in a committed escrow.
///
/// ```text
/// commitment = BLAKE3("pyana-escrow-identity-v1:" || cell_id_bytes || blinding)
/// ```
///
/// The `blinding` must be a cryptographically random 32-byte value, kept secret
/// by the committer until they need to claim the escrow.
pub fn compute_identity_commitment(cell_id: &CellId, blinding: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-escrow-identity-v1");
    hasher.update(cell_id.as_bytes());
    hasher.update(blinding);
    *hasher.finalize().as_bytes()
}

/// Compute a condition commitment for use in a committed escrow.
///
/// ```text
/// commitment = BLAKE3("pyana-escrow-condition-v1:" || condition_bytes || nonce)
/// ```
///
/// The `condition_bytes` should be the deterministic serialization of the condition
/// (e.g., via postcard). The `nonce` prevents rainbow-table attacks against common
/// condition patterns.
pub fn compute_condition_commitment(condition_bytes: &[u8], nonce: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-escrow-condition-v1");
    hasher.update(condition_bytes);
    hasher.update(nonce);
    *hasher.finalize().as_bytes()
}

/// Verify an [`EscrowClaimAuth`] against an identity commitment and escrow_id.
///
/// Returns `true` if:
/// 1. Recomputed commitment from (public_key, blinding) matches `expected_commitment`.
/// 2. The signature over `escrow_id` verifies against `public_key`.
pub fn verify_escrow_claim(
    claim: &EscrowClaimAuth,
    expected_commitment: &[u8; 32],
    escrow_id: &[u8; 32],
) -> bool {
    // Step 1: Recompute the identity commitment from the revealed opening.
    let cell_id = CellId::from_bytes(claim.public_key);
    let recomputed = compute_identity_commitment(&cell_id, &claim.blinding);
    if recomputed != *expected_commitment {
        return false;
    }

    // Step 2: Verify the Ed25519 signature over the escrow_id.
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let verifying_key = match VerifyingKey::from_bytes(&claim.public_key) {
        Ok(k) => k,
        Err(_) => return false,
    };
    let signature = Signature::from_bytes(&claim.signature);
    verifying_key.verify(escrow_id, &signature).is_ok()
}
