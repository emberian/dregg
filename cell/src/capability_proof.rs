//! Proof-carrying capability exercise for sovereign cells.
//!
//! This module enables peer-to-peer capability exercise without federation mediation.
//! Alice holds a capability to Bob's cell; she proves she holds it and sends the proof
//! along with the requested effect directly to Bob. Bob verifies locally and executes.
//!
//! Protocol:
//! 1. Alice proves: "my state contains a capability with these permissions for Bob's cell"
//! 2. Alice sends Bob: (her proof, the requested effect)
//! 3. Bob verifies: proof shows Alice holds a valid cap, effect is within permissions
//! 4. Bob executes the effect on his own cell
//!
//! The `SignedAttestation` variant is the initial implementation (both parties online).
//! The `StarkMembership` variant is for full ZK (Phase 2: holder doesn't reveal slot).

use serde::{Deserialize, Serialize};

use crate::id::CellId;
use crate::permissions::AuthRequired;
use crate::state::FieldElement;

/// Serde helper for `[u8; 64]` (Ed25519 signatures).
mod sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Core types
// ─────────────────────────────────────────────────────────────────────────────

/// A proof that an agent holds a specific capability (for peer-to-peer exercise).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityProof {
    /// The holder's cell ID.
    pub holder_cell: CellId,
    /// The holder's current state commitment.
    pub holder_commitment: [u8; 32],
    /// The target cell this capability is for.
    pub target_cell: CellId,
    /// The permissions level of the capability.
    pub permissions: AuthRequired,
    /// Proof that this capability exists in the holder's state.
    /// (For now: signed attestation. Future: STARK Merkle membership proof)
    pub proof_data: CapabilityProofData,
    /// Timestamp (freshness, unix seconds).
    pub timestamp: i64,
    /// Signature from the holder over the whole thing (Ed25519, 64 bytes).
    #[serde(with = "sig_serde")]
    pub signature: [u8; 64],
}

/// How the holder proves capability membership.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CapabilityProofData {
    /// Signed attestation (simple, no ZK -- holder signs "I have cap X").
    /// Sufficient for peer-to-peer where both parties are online.
    SignedAttestation {
        /// Which slot in the holder's c-list contains the capability.
        capability_slot: u32,
        /// Optional expiry height of the capability itself.
        expires_at: Option<u64>,
    },
    /// STARK proof of Merkle membership of the capability in the holder's state.
    /// (Future: full ZK -- verifier doesn't learn the holder's full c-list)
    StarkMembership {
        /// Serialized STARK proof bytes.
        proof_bytes: Vec<u8>,
        /// Merkle root of the holder's capability tree.
        merkle_root: [u8; 32],
    },
}

// ─────────────────────────────────────────────────────────────────────────────
// Peer effects (subset of Effect exercisable via capability)
// ─────────────────────────────────────────────────────────────────────────────

/// An effect that can be requested via peer-to-peer capability exercise.
///
/// This is a restricted subset of the full `Effect` enum (which lives in `pyana-turn`).
/// Only effects that make sense for a remote capability holder to request on a target
/// cell are included here.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PeerEffect {
    /// Set a state field on the target cell.
    SetField { index: usize, value: FieldElement },
    /// Transfer computrons from the target cell to the holder.
    Transfer { amount: u64 },
    /// Increment the target cell's nonce.
    IncrementNonce,
    /// Emit an event from the target cell.
    EmitEvent { topic: FieldElement, data: Vec<FieldElement> },
}

impl PeerEffect {
    /// What action type does this effect require on the target cell?
    pub fn required_action(&self) -> crate::permissions::Action {
        match self {
            PeerEffect::SetField { .. } => crate::permissions::Action::SetState,
            PeerEffect::Transfer { .. } => crate::permissions::Action::Send,
            PeerEffect::IncrementNonce => crate::permissions::Action::IncrementNonce,
            PeerEffect::EmitEvent { .. } => crate::permissions::Action::Access,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Request / Response
// ─────────────────────────────────────────────────────────────────────────────

/// Request to exercise a capability (sent from holder to target).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityExerciseRequest {
    /// The proof that the holder possesses this capability.
    pub capability_proof: CapabilityProof,
    /// The effects the holder wants to perform on the target cell.
    pub requested_effects: Vec<PeerEffect>,
}

/// Response from the target after processing an exercise request.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityExerciseResponse {
    /// Whether the exercise was accepted.
    pub accepted: bool,
    /// The target's new state commitment (if accepted).
    pub new_target_commitment: Option<[u8; 32]>,
    /// Error description (if rejected).
    pub error: Option<String>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Errors
// ─────────────────────────────────────────────────────────────────────────────

/// Errors that can occur during capability proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapabilityProofError {
    /// The signature over the proof is invalid.
    InvalidSignature,
    /// The holder_commitment doesn't match our last-known view of the holder's state.
    CommitmentMismatch {
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// The capability's permissions are insufficient for the requested effects.
    InsufficientPermissions {
        held: AuthRequired,
        required: AuthRequired,
    },
    /// The proof timestamp is too old (exceeds freshness window).
    StaleTimestamp {
        proof_timestamp: i64,
        current_timestamp: i64,
        max_age_seconds: i64,
    },
    /// The capability has expired (past its expiry height).
    CapabilityExpired {
        expires_at: u64,
        current_height: u64,
    },
    /// The target_cell in the proof doesn't match our cell ID.
    WrongTarget {
        expected: CellId,
        got: CellId,
    },
    /// STARK proof verification failed (for StarkMembership variant).
    StarkVerificationFailed,
}

impl std::fmt::Display for CapabilityProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSignature => write!(f, "invalid signature on capability proof"),
            Self::CommitmentMismatch { .. } => {
                write!(f, "holder commitment does not match expected state")
            }
            Self::InsufficientPermissions { held, required } => {
                write!(
                    f,
                    "capability permissions {:?} insufficient for required {:?}",
                    held, required
                )
            }
            Self::StaleTimestamp {
                proof_timestamp,
                current_timestamp,
                max_age_seconds,
            } => write!(
                f,
                "proof timestamp {} is stale (current: {}, max age: {}s)",
                proof_timestamp, current_timestamp, max_age_seconds
            ),
            Self::CapabilityExpired {
                expires_at,
                current_height,
            } => write!(
                f,
                "capability expired at height {} (current: {})",
                expires_at, current_height
            ),
            Self::WrongTarget { expected, got } => {
                write!(
                    f,
                    "proof targets {:?} but we are {:?}",
                    got, expected
                )
            }
            Self::StarkVerificationFailed => write!(f, "STARK membership proof verification failed"),
        }
    }
}

impl std::error::Error for CapabilityProofError {}

// ─────────────────────────────────────────────────────────────────────────────
// Verification context (Bob's side)
// ─────────────────────────────────────────────────────────────────────────────

/// Parameters for verifying a capability proof (Bob's view).
pub struct VerificationContext {
    /// Our own cell ID (the target).
    pub our_cell_id: CellId,
    /// Our current view of the holder's state commitment (from PeerCellView or last sync).
    pub expected_holder_commitment: [u8; 32],
    /// Current unix timestamp (for freshness check).
    pub current_timestamp: i64,
    /// Maximum age of a proof in seconds before it's considered stale.
    pub max_proof_age_seconds: i64,
    /// Current block height (for capability expiry check).
    pub current_height: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// Implementation
// ─────────────────────────────────────────────────────────────────────────────

impl CapabilityProof {
    /// Compute the signing message for this proof (everything except the signature itself).
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(256);
        msg.extend_from_slice(b"pyana-cap-proof-v1:");
        msg.extend_from_slice(self.holder_cell.as_bytes());
        msg.extend_from_slice(&self.holder_commitment);
        msg.extend_from_slice(self.target_cell.as_bytes());
        // Encode permissions as discriminant byte.
        msg.push(auth_required_discriminant(&self.permissions));
        // Encode proof_data.
        match &self.proof_data {
            CapabilityProofData::SignedAttestation {
                capability_slot,
                expires_at,
            } => {
                msg.push(0u8); // variant discriminant
                msg.extend_from_slice(&capability_slot.to_le_bytes());
                match expires_at {
                    Some(exp) => {
                        msg.push(1u8);
                        msg.extend_from_slice(&exp.to_le_bytes());
                    }
                    None => msg.push(0u8),
                }
            }
            CapabilityProofData::StarkMembership {
                proof_bytes,
                merkle_root,
            } => {
                msg.push(1u8); // variant discriminant
                msg.extend_from_slice(&(proof_bytes.len() as u64).to_le_bytes());
                msg.extend_from_slice(proof_bytes);
                msg.extend_from_slice(merkle_root);
            }
        }
        // Timestamp.
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        msg
    }

    /// Verify this capability proof from the target's perspective.
    ///
    /// Checks:
    /// 1. Signature validity (Ed25519 over the signing message)
    /// 2. Holder commitment matches our last-known view
    /// 3. Target cell matches us
    /// 4. Timestamp freshness
    /// 5. Capability expiry (if applicable)
    pub fn verify(
        &self,
        holder_pubkey: &[u8; 32],
        ctx: &VerificationContext,
    ) -> Result<(), CapabilityProofError> {
        // 1. Verify the target is us.
        if self.target_cell != ctx.our_cell_id {
            return Err(CapabilityProofError::WrongTarget {
                expected: ctx.our_cell_id,
                got: self.target_cell,
            });
        }

        // 2. Check holder_commitment matches expected (our last-known view).
        if self.holder_commitment != ctx.expected_holder_commitment {
            return Err(CapabilityProofError::CommitmentMismatch {
                expected: ctx.expected_holder_commitment,
                got: self.holder_commitment,
            });
        }

        // 3. Check timestamp freshness.
        let age = ctx.current_timestamp - self.timestamp;
        if age > ctx.max_proof_age_seconds || age < -ctx.max_proof_age_seconds {
            return Err(CapabilityProofError::StaleTimestamp {
                proof_timestamp: self.timestamp,
                current_timestamp: ctx.current_timestamp,
                max_age_seconds: ctx.max_proof_age_seconds,
            });
        }

        // 4. Check capability expiry.
        if let CapabilityProofData::SignedAttestation { expires_at, .. } = &self.proof_data {
            if let Some(exp) = expires_at {
                if ctx.current_height > *exp {
                    return Err(CapabilityProofError::CapabilityExpired {
                        expires_at: *exp,
                        current_height: ctx.current_height,
                    });
                }
            }
        }

        // 5. Verify signature.
        let msg = self.signing_message();
        if !verify_ed25519(holder_pubkey, &msg, &self.signature) {
            return Err(CapabilityProofError::InvalidSignature);
        }

        Ok(())
    }

    /// Check whether this proof's permissions are sufficient for the given effects.
    ///
    /// The capability's `permissions` level must satisfy the target cell's requirement
    /// for each effect type. For peer-to-peer exercise, we check that the cap's auth
    /// level is at least as permissive as what the target requires for each action.
    pub fn check_permissions_for_effects(
        &self,
        effects: &[PeerEffect],
        target_permissions: &crate::permissions::Permissions,
    ) -> Result<(), CapabilityProofError> {
        for effect in effects {
            let action = effect.required_action();
            let required = target_permissions.for_action(action);
            // The capability's permissions must be able to satisfy what the target requires.
            // A cap with AuthRequired::None can satisfy anything (it's the most permissive).
            // A cap with AuthRequired::Signature can only satisfy Signature or None requirements.
            if !can_satisfy(&self.permissions, required) {
                return Err(CapabilityProofError::InsufficientPermissions {
                    held: self.permissions.clone(),
                    required: required.clone(),
                });
            }
        }
        Ok(())
    }
}

/// Check if a capability's permission level can satisfy a target's requirement.
///
/// The cap's permission level represents what auth the holder provided to GET the cap.
/// When exercising, we check: does the cap's auth level meet or exceed what the target
/// requires for this action?
///
/// Ordering (most permissive to least):
/// - None: can satisfy any requirement (the cap was freely granted)
/// - Either: can satisfy Signature, Proof, Either, or None requirements
/// - Signature: can satisfy Signature or None requirements
/// - Proof: can satisfy Proof or None requirements
/// - Impossible: cannot satisfy anything
fn can_satisfy(cap_permissions: &AuthRequired, target_requires: &AuthRequired) -> bool {
    match target_requires {
        // Target requires nothing -- any cap suffices.
        AuthRequired::None => true,
        // Target requires impossible -- nothing can satisfy.
        AuthRequired::Impossible => false,
        // Target requires a specific auth kind.
        AuthRequired::Signature => matches!(
            cap_permissions,
            AuthRequired::None | AuthRequired::Signature | AuthRequired::Either
        ),
        AuthRequired::Proof => matches!(
            cap_permissions,
            AuthRequired::None | AuthRequired::Proof | AuthRequired::Either
        ),
        AuthRequired::Either => matches!(
            cap_permissions,
            AuthRequired::None
                | AuthRequired::Signature
                | AuthRequired::Proof
                | AuthRequired::Either
        ),
    }
}

/// Map AuthRequired to a single discriminant byte for signing messages.
fn auth_required_discriminant(auth: &AuthRequired) -> u8 {
    match auth {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
    }
}

/// Ed25519 signature verification (using ed25519-dalek).
#[cfg(feature = "crypto")]
fn verify_ed25519(pubkey_bytes: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    use ed25519_dalek::{Signature, VerifyingKey};
    let Ok(vk) = VerifyingKey::from_bytes(pubkey_bytes) else {
        return false;
    };
    let sig = Signature::from_bytes(signature);
    vk.verify_strict(message, &sig).is_ok()
}

/// Stub verification when crypto feature is disabled (always fails).
#[cfg(not(feature = "crypto"))]
fn verify_ed25519(_pubkey_bytes: &[u8; 32], _message: &[u8], _signature: &[u8; 64]) -> bool {
    false
}

// ─────────────────────────────────────────────────────────────────────────────
// Signing helper (for the holder/Alice side)
// ─────────────────────────────────────────────────────────────────────────────

/// Sign a capability proof with the holder's signing key.
///
/// Constructs the signing message from the proof fields and produces an Ed25519 signature.
#[cfg(feature = "crypto")]
pub fn sign_capability_proof(
    proof: &mut CapabilityProof,
    signing_key: &ed25519_dalek::SigningKey,
) {
    use ed25519_dalek::Signer;
    let msg = proof.signing_message();
    let sig = signing_key.sign(&msg);
    proof.signature = sig.to_bytes();
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "crypto")]
    use ed25519_dalek::SigningKey;

    /// Helper: create a deterministic CellId from a byte.
    fn test_cell_id(seed: u8) -> CellId {
        let pk = [seed; 32];
        let token = [0u8; 32];
        CellId::derive_raw(&pk, &token)
    }

    /// Helper: create a signed proof for testing.
    #[cfg(feature = "crypto")]
    fn make_signed_proof(
        holder_key: &SigningKey,
        holder_cell: CellId,
        target_cell: CellId,
        holder_commitment: [u8; 32],
        permissions: AuthRequired,
        capability_slot: u32,
        expires_at: Option<u64>,
        timestamp: i64,
    ) -> CapabilityProof {
        let mut proof = CapabilityProof {
            holder_cell,
            holder_commitment,
            target_cell,
            permissions,
            proof_data: CapabilityProofData::SignedAttestation {
                capability_slot,
                expires_at,
            },
            timestamp,
            signature: [0u8; 64],
        };
        sign_capability_proof(&mut proof, holder_key);
        proof
    }

    /// Helper: standard verification context.
    fn make_context(
        our_cell_id: CellId,
        expected_commitment: [u8; 32],
        current_timestamp: i64,
        current_height: u64,
    ) -> VerificationContext {
        VerificationContext {
            our_cell_id,
            expected_holder_commitment: expected_commitment,
            current_timestamp,
            max_proof_age_seconds: 300, // 5 minutes
            current_height,
        }
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_valid_exercise_accepted() {
        let holder_key = SigningKey::from_bytes(&[1u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(1);
        let target_cell = test_cell_id(2);
        let commitment = [42u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100);
        assert!(proof.verify(&holder_pubkey, &ctx).is_ok());

        // Also check permissions for a SetField effect.
        let effects = vec![PeerEffect::SetField {
            index: 0,
            value: [0u8; 32],
        }];
        let target_perms = crate::permissions::Permissions::default_user();
        assert!(proof
            .check_permissions_for_effects(&effects, &target_perms)
            .is_ok());
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_wrong_permissions_rejected() {
        let holder_key = SigningKey::from_bytes(&[2u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(3);
        let target_cell = test_cell_id(4);
        let commitment = [43u8; 32];

        // Cap has Impossible permissions -- can't satisfy anything.
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Impossible,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100);
        // Proof itself verifies (signature is fine).
        assert!(proof.verify(&holder_pubkey, &ctx).is_ok());

        // But permissions check fails for SetField (requires Signature on default perms).
        let effects = vec![PeerEffect::SetField {
            index: 0,
            value: [0u8; 32],
        }];
        let target_perms = crate::permissions::Permissions::default_user();
        let result = proof.check_permissions_for_effects(&effects, &target_perms);
        assert!(matches!(
            result,
            Err(CapabilityProofError::InsufficientPermissions { .. })
        ));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_expired_cap_rejected() {
        let holder_key = SigningKey::from_bytes(&[3u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(5);
        let target_cell = test_cell_id(6);
        let commitment = [44u8; 32];

        // Cap expires at height 50, but current height is 100.
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            Some(50), // expires at height 50
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100); // current height 100
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::CapabilityExpired {
                expires_at: 50,
                current_height: 100
            })
        ));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_commitment_mismatch_rejected() {
        let holder_key = SigningKey::from_bytes(&[4u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(7);
        let target_cell = test_cell_id(8);

        let proof_commitment = [45u8; 32];
        let expected_commitment = [99u8; 32]; // Different!

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            proof_commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, expected_commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::CommitmentMismatch { .. })
        ));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_stale_timestamp_rejected() {
        let holder_key = SigningKey::from_bytes(&[5u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(9);
        let target_cell = test_cell_id(10);
        let commitment = [46u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000, // timestamp from the past
        );

        // Current time is 2000, max age is 300s, so 1000 is 1000s old -> stale.
        let ctx = make_context(target_cell, commitment, 2000, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::StaleTimestamp { .. })
        ));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_invalid_signature_rejected() {
        let holder_key = SigningKey::from_bytes(&[6u8; 32]);
        let holder_cell = test_cell_id(11);
        let target_cell = test_cell_id(12);
        let commitment = [47u8; 32];

        let mut proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        // Corrupt the signature.
        proof.signature[0] ^= 0xff;

        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let ctx = make_context(target_cell, commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(result, Err(CapabilityProofError::InvalidSignature)));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_wrong_target_rejected() {
        let holder_key = SigningKey::from_bytes(&[7u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(13);
        let target_cell = test_cell_id(14);
        let wrong_target = test_cell_id(15); // Not us!
        let commitment = [48u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        // Verification context says we are wrong_target, but proof says target_cell.
        let ctx = make_context(wrong_target, commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::WrongTarget { .. })
        ));
    }

    #[test]
    #[cfg(feature = "crypto")]
    fn test_proof_permissions_satisfy_transfer() {
        let holder_key = SigningKey::from_bytes(&[8u8; 32]);
        let holder_cell = test_cell_id(16);
        let target_cell = test_cell_id(17);
        let commitment = [49u8; 32];

        // Cap with Signature permissions can satisfy Send (which requires Signature).
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let effects = vec![PeerEffect::Transfer { amount: 100 }];
        let target_perms = crate::permissions::Permissions::default_user();
        assert!(proof
            .check_permissions_for_effects(&effects, &target_perms)
            .is_ok());

        // Cap with Proof permissions cannot satisfy Send (which requires Signature).
        let proof_only = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Proof,
            1,
            None,
            1000,
        );
        let result = proof_only.check_permissions_for_effects(&effects, &target_perms);
        assert!(matches!(
            result,
            Err(CapabilityProofError::InsufficientPermissions { .. })
        ));
    }

    #[test]
    fn test_can_satisfy_logic() {
        // None cap can satisfy anything except Impossible.
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::None));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Signature));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Proof));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Either));
        assert!(!can_satisfy(&AuthRequired::None, &AuthRequired::Impossible));

        // Signature cap can satisfy Signature, Either, None.
        assert!(can_satisfy(&AuthRequired::Signature, &AuthRequired::None));
        assert!(can_satisfy(
            &AuthRequired::Signature,
            &AuthRequired::Signature
        ));
        assert!(!can_satisfy(&AuthRequired::Signature, &AuthRequired::Proof));
        assert!(can_satisfy(
            &AuthRequired::Signature,
            &AuthRequired::Either
        ));

        // Impossible can satisfy nothing except None.
        assert!(can_satisfy(&AuthRequired::Impossible, &AuthRequired::None));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Signature
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Proof
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Either
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Impossible
        ));
    }
}
