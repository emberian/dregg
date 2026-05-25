//! Bridge-lock action binding AIR (sibling to `bridge_action_air`).
//!
//! Where `bridge_action_air` is the canonical full-fidelity binding for
//! `Effect::BridgeMint` (the *credit* side of a cross-federation bridge),
//! this module is the symmetric binding for `Effect::BridgeLock` (the
//! *debit* side — actor locks value in a pending bridge, awaiting
//! finalization or cancellation).
//!
//! # What this AIR binds
//!
//! Public inputs (all bytes / amounts carried at full fidelity):
//!
//! ```text
//! pi[ 0.. 8)  nullifier_limbs[8]                  (8 × 4-byte BabyBear limbs)
//! pi[ 8..16)  destination_federation_limbs[8]     (8 × 4-byte BabyBear limbs)
//! pi[16..24)  asset_type_commitment_limbs[8]      (8 × 4-byte BabyBear limbs)
//! pi[24..32)  value_commitment_limbs[8]           (8 × 4-byte BabyBear limbs;
//!                                                  ZERO sentinel when None)
//! pi[32]      value_lo            (low  32 bits of u64 value)
//! pi[33]      value_hi            (high 32 bits of u64 value)
//! pi[34]      asset_type_lo
//! pi[35]      asset_type_hi
//! pi[36]      timeout_height_lo
//! pi[37]      timeout_height_hi
//! ```
//!
//! Total = 38 PI slots. Per-32-byte field: ~248 bits of binding. Per-u64
//! amount: full 64 bits.
//!
//! # Closure of the gap
//!
//! Prior to this AIR, `Effect::BridgeLock` projected to
//! `VmEffect::BridgeLock { value_lo, lock_hash, value_full }` where
//! `lock_hash = BLAKE3(nullifier ‖ destination ‖ asset_type)[..4]` — a
//! 4-byte digest. `timeout_height` and the optional Pedersen value
//! commitment were dropped entirely. A malicious prover could swap the
//! destination, the asset_type, or the timeout height for any other
//! values whose digest happened to collide on 4 bytes (~2^32 collision
//! workspace).
//!
//! With this sibling AIR, every parameter the runtime variant carries is
//! pinned at full fidelity. The sidecar binding proof is consumed by
//! `turn::executor::verify_proof_carrying_turn_bundle` alongside the
//! Effect VM proof: the VM proof retains its 4-byte truncations for
//! backwards compatibility of the existing trace shape; the binding
//! proof is what a verifier consults for algebraic, full-fidelity
//! parameter binding.
//!
//! # Why both a standalone AIR and a schema entry?
//!
//! `circuit/src/effect_action_air.rs::SCHEMA_BRIDGE_LOCK` is the
//! schema-based generalized binding. This module re-exposes the same
//! binding through a dedicated AIR struct + `prove_bridge_lock_action`
//! / `verify_bridge_lock_action` API to mirror the
//! `bridge_action_air::BridgeActionAir` shape for the bridge mint side.
//! Wire callers that work with the mint side can migrate to the lock
//! side using the same pattern.

use crate::effect_action_air::{
    EffectActionAir, EffectActionSchema, EffectActionWitness, SCHEMA_BRIDGE_LOCK,
    prove_effect_action, verify_effect_action,
};
use crate::field::BabyBear;
use crate::stark::StarkProof;

/// The bridge-lock action binding schema (re-export from `effect_action_air`).
pub const SCHEMA: EffectActionSchema = SCHEMA_BRIDGE_LOCK;

/// Total PI count: 4 × 8 = 32 from fields, 3 × 2 = 6 from amounts, total 38.
pub const BRIDGE_LOCK_PI_COUNT: usize = 38;

/// A typed witness for the bridge-lock binding.
#[derive(Clone, Debug)]
pub struct BridgeLockActionWitness {
    /// 32-byte nullifier of the note being locked.
    pub nullifier: [u8; 32],
    /// 32-byte destination federation identity.
    pub destination_federation: [u8; 32],
    /// 32-byte asset-type commitment (BLAKE3 over `asset_type.to_le_bytes()` or
    /// a domain-tagged asset identifier; the schema treats this as a 32-byte
    /// opaque field bound at full fidelity).
    pub asset_type_commitment: [u8; 32],
    /// 32-byte Pedersen value commitment; all-zero when the runtime variant
    /// does not carry a commitment (cleartext-value path).
    pub value_commitment: [u8; 32],
    /// Full u64 value being locked.
    pub value: u64,
    /// Full u64 asset_type discriminator.
    pub asset_type: u64,
    /// Block-height timeout after which the lock can be cancelled.
    pub timeout_height: u64,
}

impl BridgeLockActionWitness {
    /// Convert into the generalized `EffectActionWitness` shape.
    pub fn to_effect_witness(&self) -> EffectActionWitness {
        EffectActionWitness {
            schema: SCHEMA,
            fields: vec![
                self.nullifier,
                self.destination_federation,
                self.asset_type_commitment,
                self.value_commitment,
            ],
            amounts: vec![self.value, self.asset_type, self.timeout_height],
        }
    }

    /// Compute the canonical public-input vector this witness commits to.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        self.to_effect_witness().public_inputs()
    }
}

/// The bridge-lock action binding AIR. Thin wrapper over `EffectActionAir`
/// with the bridge-lock schema baked in.
pub struct BridgeLockActionAir {
    pub inner: EffectActionAir,
}

impl Default for BridgeLockActionAir {
    fn default() -> Self {
        Self {
            inner: EffectActionAir { schema: SCHEMA },
        }
    }
}

/// Prove a bridge-lock action binding.
pub fn prove_bridge_lock_action(witness: &BridgeLockActionWitness) -> StarkProof {
    prove_effect_action(&witness.to_effect_witness())
}

/// Verify a bridge-lock action binding proof against expected typed parameters.
pub fn verify_bridge_lock_action(
    nullifier: &[u8; 32],
    destination_federation: &[u8; 32],
    asset_type_commitment: &[u8; 32],
    value_commitment: &[u8; 32],
    value: u64,
    asset_type: u64,
    timeout_height: u64,
    proof: &StarkProof,
) -> Result<(), String> {
    verify_effect_action(
        SCHEMA,
        &[
            *nullifier,
            *destination_federation,
            *asset_type_commitment,
            *value_commitment,
        ],
        &[value, asset_type, timeout_height],
        proof,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_witness() -> BridgeLockActionWitness {
        BridgeLockActionWitness {
            nullifier: [0x10u8; 32],
            destination_federation: [0x20u8; 32],
            asset_type_commitment: [0x30u8; 32],
            value_commitment: [0x40u8; 32],
            value: (1u64 << 45) | 0xCAFE_BABE,
            asset_type: 99,
            timeout_height: 1_000_000,
        }
    }

    #[test]
    fn pi_count_matches() {
        let w = make_witness();
        let pi = w.public_inputs();
        assert_eq!(pi.len(), BRIDGE_LOCK_PI_COUNT);
    }

    #[test]
    fn prove_and_verify_roundtrip() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_ok(), "honest bridge_lock binding must verify: {r:?}");
    }

    #[test]
    fn tamper_nullifier_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let mut wrong = w.nullifier;
        wrong[0] ^= 0xFF;
        let r = verify_bridge_lock_action(
            &wrong,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_destination_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let mut wrong = w.destination_federation;
        wrong[15] ^= 0x10;
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &wrong,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_asset_type_commit_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let mut wrong = w.asset_type_commitment;
        wrong[20] ^= 0x80;
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &wrong,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_value_commitment_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let mut wrong = w.value_commitment;
        wrong[31] ^= 0x01;
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &wrong,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_value_above_2_pow_30_rejected() {
        let mut w = make_witness();
        w.value = (1u64 << 50) | 0xBEEF;
        let proof = prove_bridge_lock_action(&w);
        // 30-bit truncation must not collide.
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value & ((1u64 << 30) - 1),
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_asset_type_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type + 1,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn tamper_timeout_height_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height + 1,
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn swap_nullifier_and_destination_rejected() {
        let w = make_witness();
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.destination_federation,
            &w.nullifier,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_err(), "positional binding must reject swap");
    }

    #[test]
    fn max_amounts_roundtrip() {
        let mut w = make_witness();
        w.value = u64::MAX;
        w.asset_type = u64::MAX;
        w.timeout_height = u64::MAX;
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_ok(), "u64::MAX amounts must verify: {r:?}");
    }

    #[test]
    fn none_value_commitment_zero_sentinel_roundtrip() {
        let mut w = make_witness();
        w.value_commitment = [0u8; 32]; // None sentinel
        let proof = prove_bridge_lock_action(&w);
        let r = verify_bridge_lock_action(
            &w.nullifier,
            &w.destination_federation,
            &w.asset_type_commitment,
            &w.value_commitment,
            w.value,
            w.asset_type,
            w.timeout_height,
            &proof,
        );
        assert!(r.is_ok());
    }
}
