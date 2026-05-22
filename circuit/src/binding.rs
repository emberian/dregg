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
//!
//! # Security
//!
//! The binding commitment uses 4 BabyBear field elements (124 bits), providing
//! a birthday bound of ~2^62. This follows the same pattern as
//! `AccumulatedHash` in ivc.rs. A single BabyBear element (~31 bits) would only
//! give ~2^15.5 collision resistance, which is uncomfortably low even though
//! exploiting a collision requires a valid token for the colliding action.

use crate::field::BabyBear;
use crate::poseidon2;

/// Domain separation tag for action binding commitments.
const ACTION_BINDING_DSK: &str = "pyana-action-binding-v1";

/// Number of BabyBear elements in an action binding commitment.
/// 4 elements * 31 bits each = 124 bits of collision resistance,
/// requiring ~2^62 work for a birthday attack (well beyond practical).
pub const ACTION_BINDING_WIDTH: usize = 4;

/// A multi-element action binding commitment providing 124-bit security.
///
/// A single BabyBear element only provides ~31 bits, making birthday attacks
/// trivial at 2^15.5 (~46K attempts). Using 4 elements raises this to 2^62.
pub type ActionBinding = [BabyBear; ACTION_BINDING_WIDTH];

/// Compute a deterministic action-binding commitment from `(action, resource)`.
///
/// This is the canonical binding domain for STARK proofs. The result is 4
/// BabyBear field elements (124-bit collision resistance) that are:
/// - Included as public inputs of the STARK proof by the prover
/// - Recomputed by verifiers from the request fields and checked against the proof
///
/// # Binding semantics
///
/// - `action`: The operation being performed (e.g., "read", "write", "admin").
///   Maps to `AuthRequest.action` (token layer), `AuthorizationRequest.action` (wire),
///   and `Action.method` decoded as a string (turn layer).
///
/// - `resource`: The target of the operation (e.g., "api/v1/users", a cell ID).
///   Canonically derived as `app_id.or(service).unwrap_or("")` from the token
///   layer's `AuthRequest`. Maps to `AuthorizationRequest.resource` on the wire.
///   For bridge-mint proofs, the resource is `hex(destination_federation)`.
///
/// # Security
///
/// The commitment uses 4 BabyBear elements (124 bits of collision resistance,
/// birthday bound ~2^62). The BLAKE3 keyed hash provides domain separation from
/// other protocol uses of the same strings, and Poseidon2 squeezing ensures the
/// values are in-circuit verifiable.
pub fn compute_action_binding(action: &str, resource: &str) -> ActionBinding {
    use crate::poseidon2::Poseidon2State;

    // Derive the domain separation key from the DSK string.
    let dsk = *blake3::hash(ACTION_BINDING_DSK.as_bytes()).as_bytes();

    // Compute BLAKE3 keyed hash of (action || 0x00 || resource).
    let mut buf = Vec::with_capacity(action.len() + 1 + resource.len());
    buf.extend_from_slice(action.as_bytes());
    buf.push(0x00); // unambiguous separator
    buf.extend_from_slice(resource.as_bytes());

    let digest = blake3::keyed_hash(&dsk, &buf);

    // Encode the 32-byte digest as 8 BabyBear elements.
    let limbs = BabyBear::encode_hash(digest.as_bytes());

    // Absorb all 8 limbs through Poseidon2 sponge and squeeze 4 elements.
    let mut state = Poseidon2State::new();
    // Domain separation: encode input length in capacity
    state.state[4] = BabyBear::new(8);
    // Absorb first 4 limbs
    state.state[0] = limbs[0];
    state.state[1] = limbs[1];
    state.state[2] = limbs[2];
    state.state[3] = limbs[3];
    state.permute();
    // Absorb remaining 4 limbs
    state.state[0] += limbs[4];
    state.state[1] += limbs[5];
    state.state[2] += limbs[6];
    state.state[3] += limbs[7];
    state.permute();

    // Squeeze 4 elements (124-bit security)
    [
        state.state[0],
        state.state[1],
        state.state[2],
        state.state[3],
    ]
}

/// Compute the legacy single-element action binding (31-bit security).
///
/// **DEPRECATED**: This function provides only ~2^15.5 collision resistance.
/// Use [`compute_action_binding`] (which returns 4 elements) instead.
///
/// This remains available for contexts that need a single summary element
/// (e.g., the narrow accumulated hash in the STARK AIR trace). It is NOT
/// suitable as the sole binding commitment.
pub fn compute_action_binding_narrow(action: &str, resource: &str) -> BabyBear {
    let wide = compute_action_binding(action, resource);
    // Compress 4 elements down to 1 via Poseidon2 for legacy compatibility.
    poseidon2::hash_many(&wide)
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
    fn returns_four_elements() {
        let binding = compute_action_binding("read", "api/v1/users");
        assert_eq!(binding.len(), ACTION_BINDING_WIDTH);
        // All elements should be non-zero (extremely unlikely to have a zero element
        // from Poseidon2, but we mainly check the structure)
        assert_eq!(binding.len(), 4);
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
        let binding = compute_action_binding("", "");
        assert_eq!(binding.len(), 4);
    }

    #[test]
    fn narrow_is_deterministic_compression_of_wide() {
        let wide = compute_action_binding("admin", "system");
        let narrow = compute_action_binding_narrow("admin", "system");
        // The narrow version should be the Poseidon2 hash of the wide elements
        let expected = poseidon2::hash_many(&wide);
        assert_eq!(narrow, expected);
    }
}
