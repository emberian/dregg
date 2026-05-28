//! Real STARK-backed `MerkleMembership` predicate verifier (SenderAuthorized
//! AIR teeth).
//!
//! `StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { .. } }`
//! dispatches through the witnessed-predicate registry to a verifier of kind
//! [`WitnessedPredicateKind::MerkleMembership`]. The default registry registers
//! `NotYetWiredVerifier::merkle_membership()` — a fail-closed stub that rejects
//! everything (honest, but means SenderAuthorized can never *pass*, and the
//! membership relation is never algebraically enforced).
//!
//! This module provides [`MerkleMembershipStarkVerifier`]: a real verifier that
//! checks an in-circuit Poseidon2 Merkle-membership STARK
//! (`dregg_circuit::dsl::membership`). A turn whose sender is genuinely a leaf
//! under the authorized-set root carries a proof that verifies; a turn whose
//! sender is NOT in the set cannot produce a proof that verifies against the
//! root (Poseidon2 collision resistance), so it is rejected **at the circuit /
//! STARK level**, not merely by an executor-side comparison.
//!
//! # Encoding convention
//!
//! The verifier receives `commitment` (the 32-byte authorized-set Merkle root,
//! as projected from the cell's slot field) and `input = Sender(pk)` (the
//! 32-byte sender public key). It maps both into BabyBear via the canonical
//! Poseidon2 compression used elsewhere in the bridge / SDK layer
//! (`hash_many(encode_hash(bytes))`), then verifies the membership STARK whose
//! public inputs are `[leaf, root]`.
//!
//! A prover constructs the matching proof with [`prove_sender_membership`].

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier,
};
use dregg_circuit::BabyBear;
use dregg_circuit::dsl::membership::{
    generate_merkle_poseidon2_trace, prove_membership_dsl, verify_membership_dsl,
};
use dregg_circuit::poseidon2;
use dregg_circuit::stark::{StarkProof, proof_from_bytes};

const KIND_NAME: &str = "MerkleMembership";

/// Compress a 32-byte value to a single BabyBear via Poseidon2 of its 8 limbs.
///
/// This is the same compression the bridge-mint path uses (`apply.rs::compress`)
/// and the SDK's `bytes_to_babybear`. A sender public key (the Merkle leaf
/// pre-image) is mapped to a field element this way, so prover and verifier
/// agree on the leaf the membership circuit commits to.
fn compress(bytes: &[u8; 32]) -> BabyBear {
    let limbs = BabyBear::encode_hash(bytes);
    poseidon2::hash_many(&limbs)
}

/// Read an authorized-set root felt from a 32-byte slot value.
///
/// The cell program publishes the Poseidon2 Merkle root (a BabyBear felt) in
/// its slot as the felt's canonical 4-byte little-endian form in the low 4
/// bytes (the rest zero). The root is ALREADY a field element (the membership
/// circuit's `root` public input), so — unlike the leaf, which is a raw 32-byte
/// pk that must be compressed — the verifier reads it directly rather than
/// compressing it again. [`authorized_set_root_bytes`] emits the matching form.
fn root_felt_from_slot(bytes: &[u8; 32]) -> BabyBear {
    let v = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    BabyBear::new(v)
}

/// Real STARK-backed MerkleMembership verifier for `SenderAuthorized`.
#[derive(Clone, Copy, Debug, Default)]
pub struct MerkleMembershipStarkVerifier;

impl WitnessedPredicateVerifier for MerkleMembershipStarkVerifier {
    fn name(&self) -> &'static str {
        "merkle-membership-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::MerkleMembership
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // Resolve the candidate sender bytes.
        let candidate: [u8; 32] = match input {
            PredicateInput::Sender(s) => **s,
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) => {
                if b.len() != 32 {
                    return Err(WitnessedPredicateError::InputShapeMismatch {
                        kind_name: KIND_NAME,
                        expected: "32-byte candidate",
                        actual: "non-32-byte Bytes",
                    });
                }
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "SigningMessage",
                });
            }
        };

        let leaf = compress(&candidate);
        let root = root_felt_from_slot(commitment);

        let proof: StarkProof =
            proof_from_bytes(proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: KIND_NAME,
                reason: format!("membership STARK deserialization failed: {e}"),
            })?;

        // SECURITY: the membership circuit binds public inputs [leaf, root] via
        // row-0 / last-row boundary constraints over a Poseidon2 Merkle path.
        // A proof verifies iff the prover knew a Merkle path from `leaf` to
        // `root`. If the sender is not a leaf under the authorized-set root, no
        // such path exists (Poseidon2 collision resistance), so verification
        // fails and SenderAuthorized rejects.
        verify_membership_dsl(&proof, leaf, root).map_err(|e| {
            WitnessedPredicateError::Rejected {
                kind_name: KIND_NAME,
                reason: format!("sender is not a member of the authorized set: {e}"),
            }
        })
    }
}

/// Build a witnessed-predicate registry that wires the real STARK-backed
/// MerkleMembership verifier on top of the fail-closed defaults.
///
/// Every other kind remains its `default_builtins` fail-closed verifier; this
/// only replaces the MerkleMembership slot with the real gadget so
/// `SenderAuthorized { PublicRoot }` is algebraically enforced.
pub fn registry_with_real_sender_membership() -> WitnessedPredicateRegistry {
    let mut r = WitnessedPredicateRegistry::default_builtins();
    r.register_builtin(Arc::new(MerkleMembershipStarkVerifier));
    r
}

/// Produce a SenderAuthorized membership proof for a sender that is a leaf at
/// `(siblings, positions)` under the authorized-set root.
///
/// `sender_pk` is the 32-byte sender public key (the candidate); the returned
/// serialized STARK proof verifies under [`MerkleMembershipStarkVerifier`]
/// against the set root computed from the same path. The `siblings`/`positions`
/// are BabyBear-domain Merkle witness data (leaf-to-root), matching
/// [`dregg_circuit::dsl::membership::prove_membership_dsl`].
pub fn prove_sender_membership(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<Vec<u8>, String> {
    let leaf = compress(sender_pk);
    let proof = prove_membership_dsl(leaf, siblings, positions)?;
    Ok(dregg_circuit::stark::proof_to_bytes(&proof))
}

/// The authorized-set Merkle root as a BabyBear felt (the value the membership
/// circuit commits to as `root`), for a sender leaf at `(siblings, positions)`.
///
/// Delegates to the circuit's own trace generator so the root matches exactly
/// what the membership STARK commits to (Poseidon2 `hash_4_to_1` of children
/// arranged by position), rather than re-deriving it here.
pub fn authorized_set_root_felt(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> BabyBear {
    let leaf = compress(sender_pk);
    let (_trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, siblings, positions);
    // PI layout is [leaf, root].
    public_inputs[1]
}

/// The 32-byte slot value the cell program publishes for the authorized-set
/// root: the root felt's canonical 4-byte little-endian form in the low bytes
/// (matching [`root_felt_from_slot`]).
pub fn authorized_set_root_bytes(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> [u8; 32] {
    let root = authorized_set_root_felt(sender_pk, siblings, positions);
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&root.0.to_le_bytes());
    out
}
