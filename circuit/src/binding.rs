//! Canonical action-binding commitment for STARK proofs.
//!
//! This module defines the single authoritative function for computing the
//! binding commitment that ties a STARK proof to the (action, resource) pair
//! it authorizes. All three layers (prover, wire verifier, turn verifier) MUST
//! use this function to ensure they agree on what the proof is bound to.
//!
//! The binding domain is `(action, resource)` — the semantically meaningful
//! parts of an authorization request. Anti-replay fields (nonce, timestamp)
//! are NOT part of the binding because they change between requests for the
//! same authorization and the proof cannot be bound to values that don't exist
//! at proving time.

use crate::field::BabyBear;
use crate::poseidon2;

/// Domain separation tag for action binding commitments.
const ACTION_BINDING_DSK: &str = "pyana-action-binding-v1";

/// Compute a deterministic action-binding commitment from `(action, resource)`.
///
/// This is the canonical binding domain for STARK proofs. The result is a single
/// BabyBear field element that is:
/// - Appended as the last public input of the STARK proof by the prover
/// - Recomputed by verifiers from the request fields and checked against the proof
///
/// # Binding semantics
///
/// - `action`: The operation being performed (e.g., "read", "write", "admin").
///   Maps to `AuthRequest.action` (token layer), `AuthorizationRequest.action` (wire),
///   and `Action.method` decoded as a string (turn layer).
///
/// - `resource`: The target of the operation (e.g., "api/v1/users", a cell ID).
///   Maps to `AuthRequest.service` or `AuthRequest.app_id` (token layer),
///   `AuthorizationRequest.resource` (wire), and `Action.target` as hex (turn layer).
///
/// # Security
///
/// The commitment is collision-resistant up to the ~31-bit BabyBear field size.
/// The BLAKE3 keyed hash provides domain separation from other protocol uses of
/// the same strings, and Poseidon2 compression ensures the value is in-circuit
/// verifiable.
pub fn compute_action_binding(action: &str, resource: &str) -> BabyBear {
    // Derive the domain separation key from the DSK string.
    let dsk = *blake3::hash(ACTION_BINDING_DSK.as_bytes()).as_bytes();

    // Compute BLAKE3 keyed hash of (action || 0x00 || resource).
    let mut buf = Vec::with_capacity(action.len() + 1 + resource.len());
    buf.extend_from_slice(action.as_bytes());
    buf.push(0x00); // unambiguous separator
    buf.extend_from_slice(resource.as_bytes());

    let digest = blake3::keyed_hash(&dsk, &buf);

    // Compress the 32-byte digest to a single BabyBear element via Poseidon2.
    let limbs = BabyBear::encode_hash(digest.as_bytes());
    poseidon2::hash_many(&limbs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("read", "api/v1/users");
        assert_eq!(a, b);
    }

    #[test]
    fn different_action_different_commitment() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("write", "api/v1/users");
        assert_ne!(a, b);
    }

    #[test]
    fn different_resource_different_commitment() {
        let a = compute_action_binding("read", "api/v1/users");
        let b = compute_action_binding("read", "api/v1/posts");
        assert_ne!(a, b);
    }

    #[test]
    fn separator_prevents_ambiguity() {
        // "read\x00api" != "rea\x00dapi" due to unambiguous separator
        let a = compute_action_binding("read", "api");
        let b = compute_action_binding("rea", "dapi");
        // Extremely unlikely to collide but the separator makes it structurally impossible
        // to confuse action/resource boundaries.
        assert_ne!(a, b);
    }

    #[test]
    fn empty_strings_valid() {
        // Should not panic
        let _ = compute_action_binding("", "");
    }
}
