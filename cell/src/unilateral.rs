//! Stage 7-γ.2 unilateral binding — plain data type.
//!
//! The 1-arity sibling of γ.2's bilateral (Transfer/Grant) and trilateral
//! (Introduce) binding family. A unilateral attestation is a cell binding
//! a property over its *own* transitions — without a counterparty.
//!
//! This module owns the plain data type so [`crate::peer_exchange`] can
//! carry it on a [`crate::peer_exchange::PeerStateTransition`]. The
//! accumulator-side logic (PI projection, kind→salt mapping, Poseidon2
//! absorb) lives in `pyana_turn::bilateral_schedule` because it depends on
//! the circuit's PI layout.
//!
//! See `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.5 for the categorical lens.

use serde::{Deserialize, Serialize};

use crate::CellId;

/// A unilateral attestation: a cell binding a property over its *own*
/// transitions without a counterparty. Composes with
/// [`crate::peer_exchange::PeerStateTransition`] — a sovereign cell using
/// the federation-bypass primitive can ship one attestation per transition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnilateralAttestation {
    pub kind: UnilateralAttestationKind,
    /// 32-byte canonical hash of the attestation's witness. The exact
    /// preimage is kind-specific (see [`Self::self_state_transition`] etc.).
    /// The receiver re-derives this from the sender's cell-id-derived view
    /// — including `cell_id` in the preimage means a forged sender cannot
    /// reuse another cell's attestation data.
    pub attestation_data: [u8; 32],
}

/// Discriminant of [`UnilateralAttestation`]. Each variant has a distinct
/// PI tag and a distinct accumulator salt so two attestations with
/// colliding `attestation_data` but different kinds remain distinguishable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnilateralAttestationKind {
    /// "My cell state went from X to Y." Used by hosted-cell sovereign-style
    /// receipts where the cell self-publishes the transition.
    SelfStateTransition,
    /// "My nonce was N, now N+1." Useful for clients that want to publish
    /// monotonic activity without leaking effect content.
    SelfNonceBump,
    /// "I signed this transition as a sovereign witness." Composes with
    /// the SOVEREIGN_WITNESS_* PI slots — but distinct from those: those
    /// bind the AIR's row-0 owner-pubkey hash, while this binds the
    /// post-hoc auditable trail.
    SovereignWitness,
    /// Caller-provided 30-bit `kind_tag`. The PI projection masks the tag
    /// to 30 bits and OR's with the custom discriminant so it remains in
    /// canonical BabyBear space and can never collide with a well-known kind.
    Custom { kind_tag: u32 },
}

impl UnilateralAttestation {
    /// Canonical helper: build a SelfStateTransition attestation. The
    /// preimage layout mirrors `peer_exchange::canonical_message` so the
    /// receiver can rebuild without coordination.
    pub fn self_state_transition(
        cell_id: &CellId,
        old_commit: &[u8; 32],
        new_commit: &[u8; 32],
        effects_hash: &[u8; 32],
    ) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-unilateral-self-state-transition-v1");
        hasher.update(cell_id.as_bytes());
        hasher.update(old_commit);
        hasher.update(new_commit);
        hasher.update(effects_hash);
        Self {
            kind: UnilateralAttestationKind::SelfStateTransition,
            attestation_data: *hasher.finalize().as_bytes(),
        }
    }

    /// Canonical helper: a SelfNonceBump attestation over (prev_nonce, new_nonce).
    pub fn self_nonce_bump(cell_id: &CellId, prev_nonce: u64, new_nonce: u64) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-unilateral-self-nonce-bump-v1");
        hasher.update(cell_id.as_bytes());
        hasher.update(&prev_nonce.to_be_bytes());
        hasher.update(&new_nonce.to_be_bytes());
        Self {
            kind: UnilateralAttestationKind::SelfNonceBump,
            attestation_data: *hasher.finalize().as_bytes(),
        }
    }

    /// Canonical helper: a SovereignWitness attestation over (pubkey,
    /// sequence, signature). Used by sovereign cells that publish their
    /// signed transitions as auditable artifacts.
    pub fn sovereign_witness(
        cell_id: &CellId,
        pubkey: &[u8; 32],
        sequence: u64,
        signature: &[u8; 64],
    ) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-unilateral-sovereign-witness-v1");
        hasher.update(cell_id.as_bytes());
        hasher.update(pubkey);
        hasher.update(&sequence.to_be_bytes());
        hasher.update(signature);
        Self {
            kind: UnilateralAttestationKind::SovereignWitness,
            attestation_data: *hasher.finalize().as_bytes(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn canonical_preimages_include_cell_id() {
        // Same logical (old, new, effects) attested by two different cells
        // must produce different attestation_data — this is what blocks a
        // forged sender from reusing another cell's attestation.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let old = [0x01; 32];
        let new = [0x02; 32];
        let eff = [0x03; 32];
        let alice_att = UnilateralAttestation::self_state_transition(&alice, &old, &new, &eff);
        let bob_att = UnilateralAttestation::self_state_transition(&bob, &old, &new, &eff);
        assert_ne!(alice_att.attestation_data, bob_att.attestation_data);
        assert_eq!(alice_att.kind, bob_att.kind);
    }

    #[test]
    fn self_state_transition_is_deterministic() {
        let id = cid(1);
        let a = UnilateralAttestation::self_state_transition(&id, &[1; 32], &[2; 32], &[3; 32]);
        let b = UnilateralAttestation::self_state_transition(&id, &[1; 32], &[2; 32], &[3; 32]);
        assert_eq!(a, b);
    }

    #[test]
    fn nonce_bump_differs_per_nonce() {
        let id = cid(1);
        let a = UnilateralAttestation::self_nonce_bump(&id, 1, 2);
        let b = UnilateralAttestation::self_nonce_bump(&id, 2, 3);
        assert_ne!(a.attestation_data, b.attestation_data);
    }

    #[test]
    fn sovereign_witness_differs_per_signature() {
        let id = cid(1);
        let pk = [0x42; 32];
        let mut sig_a = [0u8; 64];
        sig_a[0] = 1;
        let mut sig_b = [0u8; 64];
        sig_b[0] = 2;
        let a = UnilateralAttestation::sovereign_witness(&id, &pk, 7, &sig_a);
        let b = UnilateralAttestation::sovereign_witness(&id, &pk, 7, &sig_b);
        assert_ne!(a.attestation_data, b.attestation_data);
    }
}
