//! Bridge-action binding wrapper.
//!
//! Wraps `pyana_circuit::bridge_action_air` with bridge-side ergonomics: a
//! `PortableActionBinding` type that bundles a serialized STARK proof with
//! its typed parameters, plus prove/verify helpers tied to
//! `pyana_cell::note_bridge`'s shapes.
//!
//! # Why this exists
//!
//! Before this lane, the bridge's proof-to-action binding was encoded only
//! as comments in `turn/src/executor.rs` (see BACKWATER-CRATES-AUDIT.md
//! bridge/ open issue: "proof-to-action binding lives in the executor, not
//! the circuit"). The executor's BridgeMint closure compressed the typed
//! parameters into a single BabyBear felt via Poseidon2 (`bytes_to_babybear`)
//! and used a 30-bit truncation for the u64 amount (CAVEAT-LAYER-COVERAGE.md
//! §6.5). Those compressions are sufficient for the existing `note_spending`
//! AIR's binding (whose primary job is the spending-key + Merkle proof), but
//! they leave a high-bit / high-byte tail unbound at the algebraic level.
//!
//! The sibling AIR in `pyana_circuit::bridge_action_air` carries the full
//! 32 bytes of each hash field (8 limbs × 4 bytes) and the full 64 bits of
//! amount (low 32 + high 32). This module is the bridge-side seam that
//! produces and consumes those proofs.
//!
//! # Combined-proof shape
//!
//! A complete bridge presentation now carries TWO STARK proofs:
//!
//! 1. The `note_spending` proof — proves knowledge of the spending key and
//!    Merkle membership of the note in the source federation's note tree.
//!    Already in `cell::note_bridge::PortableNoteProof`.
//! 2. The `bridge_action` proof — pins the full-fidelity bridge action
//!    parameters. The new piece. Carried as a sidecar of `PortableNoteProof`
//!    via `PortableActionBinding`.
//!
//! At the destination, the executor verifies both: the spending proof
//! attests to spend authority and Merkle membership, and the action proof
//! attests that the typed parameters used to apply the mint match the ones
//! the prover committed to at trace-generation time.

use pyana_circuit::bridge_action_air::{
    BridgeActionWitness, prove_bridge_action, verify_bridge_action,
};
use pyana_circuit::stark::{StarkProof, proof_from_bytes, proof_to_bytes};
use serde::{Deserialize, Serialize};

/// A portable, self-describing bridge-action binding.
///
/// Carries the typed parameters in plaintext (so the executor can dispatch
/// on them without parsing the proof) alongside a serialized STARK proof
/// that algebraically attests to those exact bytes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PortableActionBinding {
    /// The 32-byte spent-note nullifier.
    pub nullifier: [u8; 32],
    /// The 32-byte destination-side commitment (recipient note commitment).
    pub recipient: [u8; 32],
    /// The 32-byte destination federation identity.
    pub destination_federation: [u8; 32],
    /// The full u64 amount.
    pub amount: u64,
    /// The serialized `pyana_circuit::stark::StarkProof` for the
    /// `bridge_action_air::BridgeActionAir`.
    pub proof_bytes: Vec<u8>,
}

/// Produce a `PortableActionBinding` from typed parameters.
///
/// The returned object is suitable for inclusion in a wire-format bridge
/// presentation alongside `pyana_cell::note_bridge::PortableNoteProof`.
pub fn create_action_binding(
    nullifier: [u8; 32],
    recipient: [u8; 32],
    destination_federation: [u8; 32],
    amount: u64,
) -> PortableActionBinding {
    let witness = BridgeActionWitness {
        nullifier,
        recipient,
        destination_federation,
        amount,
    };
    let proof = prove_bridge_action(&witness);
    let proof_bytes = proof_to_bytes(&proof);
    PortableActionBinding {
        nullifier,
        recipient,
        destination_federation,
        amount,
        proof_bytes,
    }
}

/// Errors from `verify_action_binding`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActionBindingError {
    /// The proof bytes did not deserialize as a STARK proof.
    DeserializationFailed { reason: String },
    /// The STARK proof failed the AIR boundary / constraint checks.
    /// This catches any mismatch on nullifier / recipient /
    /// destination_federation / amount limbs.
    AirVerificationFailed { reason: String },
}

impl core::fmt::Display for ActionBindingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ActionBindingError::DeserializationFailed { reason } => {
                write!(f, "bridge-action proof deserialization failed: {reason}")
            }
            ActionBindingError::AirVerificationFailed { reason } => {
                write!(f, "bridge-action AIR verification failed: {reason}")
            }
        }
    }
}

impl std::error::Error for ActionBindingError {}

/// Verify a `PortableActionBinding` against the executor's expected typed
/// parameters.
///
/// The executor passes its own view of `(nullifier, recipient,
/// destination_federation, amount)` — the parameters it is about to apply.
/// This function deserializes the embedded STARK proof and checks that the
/// AIR's boundary constraints all hold against those parameters. Any
/// mismatch on ANY limb of any field causes rejection.
///
/// # Why the executor passes the parameters
///
/// We do NOT trust the parameters embedded in the `PortableActionBinding`
/// itself for the verify step — those are dispatch hints. The cryptographic
/// binding is the AIR boundary check, which compares the executor's typed
/// values against the prover's committed trace. This pattern matches
/// `verify_note_spend_dsl_with_destination`.
pub fn verify_action_binding(
    binding: &PortableActionBinding,
    expected_nullifier: &[u8; 32],
    expected_recipient: &[u8; 32],
    expected_destination_federation: &[u8; 32],
    expected_amount: u64,
) -> Result<(), ActionBindingError> {
    let proof: StarkProof =
        proof_from_bytes(&binding.proof_bytes).map_err(|reason| ActionBindingError::DeserializationFailed { reason })?;
    verify_bridge_action(
        expected_nullifier,
        expected_recipient,
        expected_destination_federation,
        expected_amount,
        &proof,
    )
    .map_err(|e| ActionBindingError::AirVerificationFailed { reason: e })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_binding() -> PortableActionBinding {
        create_action_binding(
            [0x10; 32],
            [0x20; 32],
            [0x30; 32],
            (1u64 << 40) | 0xDEAD_BEEF,
        )
    }

    #[test]
    fn happy_path() {
        let b = sample_binding();
        let r = verify_action_binding(&b, &b.nullifier, &b.recipient, &b.destination_federation, b.amount);
        assert!(r.is_ok(), "honest binding must verify: {r:?}");
    }

    #[test]
    fn wrong_nullifier_rejected() {
        let b = sample_binding();
        let mut wrong = b.nullifier;
        wrong[5] ^= 0x01;
        let r = verify_action_binding(&b, &wrong, &b.recipient, &b.destination_federation, b.amount);
        assert!(matches!(r, Err(ActionBindingError::AirVerificationFailed { .. })));
    }

    #[test]
    fn wrong_recipient_rejected() {
        let b = sample_binding();
        let mut wrong = b.recipient;
        wrong[10] ^= 0x02;
        let r = verify_action_binding(&b, &b.nullifier, &wrong, &b.destination_federation, b.amount);
        assert!(matches!(r, Err(ActionBindingError::AirVerificationFailed { .. })));
    }

    #[test]
    fn wrong_destination_federation_rejected() {
        let b = sample_binding();
        let mut wrong = b.destination_federation;
        wrong[0] ^= 0xFF;
        let r = verify_action_binding(&b, &b.nullifier, &b.recipient, &wrong, b.amount);
        assert!(matches!(r, Err(ActionBindingError::AirVerificationFailed { .. })));
    }

    #[test]
    fn wrong_amount_30bit_truncation_rejected() {
        let b = sample_binding();
        let truncated = b.amount & ((1u64 << 30) - 1);
        let r = verify_action_binding(
            &b,
            &b.nullifier,
            &b.recipient,
            &b.destination_federation,
            truncated,
        );
        assert!(matches!(r, Err(ActionBindingError::AirVerificationFailed { .. })));
    }

    #[test]
    fn tampered_proof_bytes_rejected() {
        let mut b = sample_binding();
        b.proof_bytes[10] ^= 0xAA;
        let r = verify_action_binding(&b, &b.nullifier, &b.recipient, &b.destination_federation, b.amount);
        // Either deserialization fails or AIR verification fails — both are
        // acceptable rejection paths.
        assert!(r.is_err(), "tampered proof must be rejected: got {r:?}");
    }
}
