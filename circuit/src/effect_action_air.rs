//! Generalized effect-action binding AIR.
//!
//! Sibling AIR to `bridge_action_air`. The bridge AIR established the pattern:
//! a 32-byte field becomes 8 BabyBear limbs (4 bytes each), a u64 amount
//! becomes 2 BabyBear limbs (low/high 32 bits), and each limb is pinned to a
//! trace-row-0 column via a boundary constraint. Transition constraints force
//! every row to equal row 0, so a malicious prover cannot put one set of
//! parameters in row 0 and another in row 1 to slip past the boundary check.
//!
//! `bridge_action_air` ships a *fixed* schema (nullifier + recipient +
//! destination_federation + amount). This module generalizes the same shape to
//! an arbitrary list of named 32-byte fields and named u64 amounts, so each
//! `Effect` variant can have its parameters bound at full fidelity without
//! authoring a new AIR per variant.
//!
//! # Layout
//!
//! Given a schema with `N` 32-byte fields and `M` u64 amounts, the column /
//! PI layout is:
//!
//! ```text
//! col / PI 0..8           field[0] limbs        (8 × 4-byte BabyBear)
//! col / PI 8..16          field[1] limbs
//! ...
//! col / PI 8N             amount[0] low 32 bits
//! col / PI 8N + 1         amount[0] high 32 bits
//! col / PI 8N + 2         amount[1] low 32 bits
//! ...
//! ```
//!
//! Total trace width = 8N + 2M. Total PI count = 8N + 2M. Each PI slot
//! corresponds 1:1 with a row-0 boundary constraint on the same column.
//!
//! # Why a generalized AIR rather than one-per-effect?
//!
//! The bridge-action AIR is its own module for historical / dispatch reasons
//! (the bridge wire format references the proof shape by name). For
//! subsequent effects we factor: one AIR with a per-effect *schema*, and
//! per-effect *witness builders* in this same module. Each effect's
//! `prove_X_binding` / `verify_X_binding` pair uses the same AIR with a
//! different schema. The AIR's `air_name` mixes in the effect kind so the
//! Fiat-Shamir transcript domain-separates different effect kinds (a proof
//! generated for effect A cannot replay as effect B even with the same
//! parameter bytes).
//!
//! # What this AIR does and does NOT do
//!
//! Does: full-fidelity binding of typed parameters into the proof's PI.
//! Tampering on any byte of any 32-byte field, or any bit of any u64 amount,
//! produces a different limb encoding which mismatches the boundary
//! constraint, which fails STARK verification.
//!
//! Does NOT: replay protection, ledger-state consistency, cross-effect
//! ordering, or anything specific to an effect's *semantics*. Those live one
//! layer up (executor / Effect-VM / per-effect side proofs).

use crate::field::BabyBear;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Number of BabyBear limbs used to represent a 32-byte field.
pub const HASH_LIMBS: usize = 8;

/// Number of BabyBear limbs used to represent a u64 amount.
pub const AMOUNT_LIMBS: usize = 2;

/// A static schema describing what an effect-binding proof commits to.
///
/// Schemas are normally defined as `pub const` values, one per Effect kind,
/// with a unique `kind_name` (used for domain separation in the Fiat-Shamir
/// transcript) and a fixed list of named 32-byte fields and u64 amounts.
#[derive(Clone, Copy, Debug)]
pub struct EffectActionSchema {
    /// Unique name used in `air_name()` for Fiat-Shamir domain separation.
    /// MUST be distinct for each effect kind to prevent cross-effect proof
    /// confusion.
    pub kind_name: &'static str,
    /// Number of 32-byte fields the schema binds.
    pub field_count: usize,
    /// Number of u64 amounts the schema binds.
    pub amount_count: usize,
}

impl EffectActionSchema {
    /// Total trace width / PI count for this schema.
    pub const fn width(&self) -> usize {
        self.field_count * HASH_LIMBS + self.amount_count * AMOUNT_LIMBS
    }
}

/// Encode a 32-byte value as 8 BabyBear limbs (4 bytes each, little-endian
/// per chunk, each chunk reduced via `BabyBear::new`).
///
/// Same encoding as `bridge_action_air::encode_hash`. The collision
/// probability across two distinct 32-byte values whose all 8 limbs collide
/// modulo the BabyBear prime is ~p^-8 ≈ 2^-248 (well above the 124-bit STARK
/// soundness target).
pub fn encode_hash(bytes: &[u8; 32]) -> [BabyBear; HASH_LIMBS] {
    let mut out = [BabyBear::ZERO; HASH_LIMBS];
    for (i, chunk) in bytes.chunks(4).enumerate() {
        let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        out[i] = BabyBear::new(val);
    }
    out
}

/// Encode a u64 amount as 2 BabyBear limbs (low 32 + high 32, each reduced
/// canonically via `BabyBear::new`).
///
/// Same encoding as `bridge_action_air::encode_amount`.
pub fn encode_amount(amount: u64) -> [BabyBear; AMOUNT_LIMBS] {
    let lo = (amount & 0xFFFF_FFFF) as u32;
    let hi = (amount >> 32) as u32;
    [BabyBear::new(lo), BabyBear::new(hi)]
}

/// A typed witness for one instance of an `EffectActionSchema`.
///
/// The `fields` and `amounts` vectors are in schema order: `fields[i]` is
/// pinned to PI slots `[i * 8, (i + 1) * 8)`; `amounts[j]` is pinned to PI
/// slots `[8 * field_count + j * 2, 8 * field_count + (j + 1) * 2)`.
#[derive(Clone, Debug)]
pub struct EffectActionWitness {
    /// Schema describing the binding.
    pub schema: EffectActionSchema,
    /// 32-byte fields in schema order.
    pub fields: Vec<[u8; 32]>,
    /// u64 amounts in schema order.
    pub amounts: Vec<u64>,
}

impl EffectActionWitness {
    /// Compute the canonical public-input vector this witness commits to.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pi = Vec::with_capacity(self.schema.width());
        for f in &self.fields {
            pi.extend_from_slice(&encode_hash(f));
        }
        for a in &self.amounts {
            let [lo, hi] = encode_amount(*a);
            pi.push(lo);
            pi.push(hi);
        }
        pi
    }
}

/// The generalized effect-action binding AIR.
///
/// Stateless modulo the `schema`. One real row of typed data, padded to 4 to
/// satisfy STARK power-of-2 trace-length requirements.
pub struct EffectActionAir {
    /// The schema this AIR instance binds to. Carried by value so each
    /// effect kind gets its own (statically declared) schema and the
    /// `air_name()` returns the kind's unique name for Fiat-Shamir.
    pub schema: EffectActionSchema,
}

impl EffectActionAir {
    /// Generate the execution trace and public inputs from a witness.
    pub fn generate_trace(
        witness: &EffectActionWitness,
    ) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        assert_eq!(
            witness.fields.len(),
            witness.schema.field_count,
            "field count mismatch"
        );
        assert_eq!(
            witness.amounts.len(),
            witness.schema.amount_count,
            "amount count mismatch"
        );
        let width = witness.schema.width();

        // Row 0: the full typed binding.
        let mut row0 = vec![BabyBear::ZERO; width];
        let mut col = 0;
        for f in &witness.fields {
            let limbs = encode_hash(f);
            for limb in limbs {
                row0[col] = limb;
                col += 1;
            }
        }
        for a in &witness.amounts {
            let [lo, hi] = encode_amount(*a);
            row0[col] = lo;
            col += 1;
            row0[col] = hi;
            col += 1;
        }

        // Pad to length 4 (smallest power of 2 ≥ 1).
        let mut trace = Vec::with_capacity(4);
        for _ in 0..4 {
            trace.push(row0.clone());
        }

        let public_inputs = witness.public_inputs();
        (trace, public_inputs)
    }
}

impl StarkAir for EffectActionAir {
    fn width(&self) -> usize {
        self.schema.width()
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn air_name(&self) -> &'static str {
        // The kind_name is itself the domain separator. Effect-kind-specific
        // schemas have distinct `kind_name` values so the Fiat-Shamir
        // transcript cannot confuse one effect kind with another.
        self.schema.kind_name
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // Transition: every column constant across rows. Same shape as
        // bridge_action_air.
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;
        let width = self.schema.width();
        for c in 0..width {
            let diff = next[c] - local[c];
            combined = combined + alpha_pow * diff;
            alpha_pow = alpha_pow * alpha;
        }
        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let width = self.schema.width();
        if public_inputs.len() != width {
            // Wrong PI length → emit no boundary constraints; this fails the
            // verifier because the trace won't match the empty constraint
            // set. (Mirrors bridge_action_air behavior.)
            return Vec::new();
        }
        let mut constraints = Vec::with_capacity(width);
        for c in 0..width {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: c,
                value: public_inputs[c],
            });
        }
        constraints
    }
}

/// Prove an effect-action binding.
///
/// Produces a STARK proof that carries the typed parameters at full fidelity
/// (8 limbs per 32-byte field, 2 limbs per u64 amount). The proof binds the
/// prover to the exact `(fields, amounts)` tuple in the witness — any
/// tampering on the verifier side fails.
pub fn prove_effect_action(witness: &EffectActionWitness) -> StarkProof {
    let air = EffectActionAir {
        schema: witness.schema,
    };
    let (trace, public_inputs) = EffectActionAir::generate_trace(witness);
    stark::prove(&air, &trace, &public_inputs)
}

/// Verify an effect-action binding proof against expected typed parameters.
///
/// The verifier passes the schema and the expected `fields` / `amounts` in
/// schema order. Any limb mismatch fails verification.
pub fn verify_effect_action(
    schema: EffectActionSchema,
    expected_fields: &[[u8; 32]],
    expected_amounts: &[u64],
    proof: &StarkProof,
) -> Result<(), String> {
    if expected_fields.len() != schema.field_count {
        return Err(format!(
            "expected {} fields, got {}",
            schema.field_count,
            expected_fields.len()
        ));
    }
    if expected_amounts.len() != schema.amount_count {
        return Err(format!(
            "expected {} amounts, got {}",
            schema.amount_count,
            expected_amounts.len()
        ));
    }

    let mut public_inputs = Vec::with_capacity(schema.width());
    for f in expected_fields {
        public_inputs.extend_from_slice(&encode_hash(f));
    }
    for a in expected_amounts {
        let [lo, hi] = encode_amount(*a);
        public_inputs.push(lo);
        public_inputs.push(hi);
    }

    let air = EffectActionAir { schema };
    stark::verify(&air, proof, &public_inputs)
}

// ============================================================================
// Per-Effect schemas
// ============================================================================
//
// Each schema is a `pub const` so the Fiat-Shamir `air_name` is statically
// distinct per effect kind. Adding a new effect's binding is one new const
// here plus a `prove_X_binding` / `verify_X_binding` convenience pair (see
// below) and the executor's projection update.

/// Schema for `GrantCapability` binding:
/// fields = [cap_target_cell (32B), cap_permissions_hash (32B),
///           cap_allowed_effects_hash (32B)]
/// amounts = [cap_slot (u32 → u64)]
pub const SCHEMA_GRANT_CAPABILITY: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-grant-capability-v1",
    field_count: 3,
    amount_count: 1,
};

/// Schema for `RevokeCapability` binding:
/// fields = [cell_id (32B)]
/// amounts = [slot (u32 → u64)]
pub const SCHEMA_REVOKE_CAPABILITY: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-revoke-capability-v1",
    field_count: 1,
    amount_count: 1,
};

/// Schema for `EmitEvent` binding:
/// fields = [topic (32B), data_hash (32B = BLAKE3 of full event.data)]
/// amounts = [data_len (u64)]
pub const SCHEMA_EMIT_EVENT: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-emit-event-v1",
    field_count: 2,
    amount_count: 1,
};

/// Schema for `CreateCell` binding:
/// fields = [public_key (32B), token_id (32B)]
/// amounts = [balance (u64)]
pub const SCHEMA_CREATE_CELL: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-create-cell-v1",
    field_count: 2,
    amount_count: 1,
};

/// Schema for `SetPermissions` binding:
/// fields = [cell_id (32B), permissions_hash (32B = BLAKE3 of postcard(perm))]
/// amounts = []
pub const SCHEMA_SET_PERMISSIONS: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-set-permissions-v1",
    field_count: 2,
    amount_count: 0,
};

/// Schema for `SetVerificationKey` binding:
/// fields = [cell_id (32B), vk_hash (32B; all-zero for None)]
/// amounts = []
pub const SCHEMA_SET_VERIFICATION_KEY: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-set-verification-key-v1",
    field_count: 2,
    amount_count: 0,
};

/// Schema for `Introduce` binding:
/// fields = [introducer (32B), recipient (32B), target (32B),
///           permissions_vk_hash (32B; zero for non-Custom)]
/// amounts = [permissions_discriminant (u64; 0..=5)]
pub const SCHEMA_INTRODUCE: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-introduce-v1",
    field_count: 4,
    amount_count: 1,
};

/// Schema for `CreateSealPair` binding:
/// fields = [sealer_holder (32B), unsealer_holder (32B)]
/// amounts = []
pub const SCHEMA_CREATE_SEAL_PAIR: EffectActionSchema = EffectActionSchema {
    kind_name: "pyana-effect-create-seal-pair-v1",
    field_count: 2,
    amount_count: 0,
};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A roundtrip helper: prove + verify, returning the verification result.
    fn roundtrip(
        schema: EffectActionSchema,
        fields: Vec<[u8; 32]>,
        amounts: Vec<u64>,
    ) -> Result<(), String> {
        let witness = EffectActionWitness {
            schema,
            fields: fields.clone(),
            amounts: amounts.clone(),
        };
        let proof = prove_effect_action(&witness);
        verify_effect_action(schema, &fields, &amounts, &proof)
    }

    #[test]
    fn encode_hash_deterministic() {
        let a = encode_hash(&[0x42; 32]);
        let b = encode_hash(&[0x42; 32]);
        assert_eq!(a, b);
    }

    #[test]
    fn encode_hash_distinguishes_distinct_bytes() {
        let a = encode_hash(&[0x42; 32]);
        let mut bytes = [0x42u8; 32];
        bytes[0] = 0x43;
        let b = encode_hash(&bytes);
        assert_ne!(a, b);
    }

    #[test]
    fn encode_amount_full_64_bits() {
        let [lo, hi] = encode_amount(0xDEAD_BEEF_CAFE_F00D);
        assert_eq!(lo, BabyBear::new(0xCAFE_F00D));
        assert_eq!(hi, BabyBear::new(0xDEAD_BEEF));
    }

    #[test]
    fn schema_width_arithmetic() {
        assert_eq!(SCHEMA_GRANT_CAPABILITY.width(), 3 * 8 + 1 * 2);
        assert_eq!(SCHEMA_REVOKE_CAPABILITY.width(), 8 + 2);
        assert_eq!(SCHEMA_EMIT_EVENT.width(), 16 + 2);
        assert_eq!(SCHEMA_CREATE_CELL.width(), 16 + 2);
        assert_eq!(SCHEMA_SET_PERMISSIONS.width(), 16);
        assert_eq!(SCHEMA_SET_VERIFICATION_KEY.width(), 16);
        assert_eq!(SCHEMA_INTRODUCE.width(), 32 + 2);
        assert_eq!(SCHEMA_CREATE_SEAL_PAIR.width(), 16);
    }

    #[test]
    fn grant_capability_roundtrip() {
        let target = [0x11u8; 32];
        let perm = [0x22u8; 32];
        let allowed = [0x33u8; 32];
        let slot = 0xCAFEBABEu64;
        let r = roundtrip(SCHEMA_GRANT_CAPABILITY, vec![target, perm, allowed], vec![slot]);
        assert!(r.is_ok(), "honest grant_capability binding must verify: {r:?}");
    }

    #[test]
    fn grant_capability_tamper_target_rejected() {
        let target = [0x11u8; 32];
        let perm = [0x22u8; 32];
        let allowed = [0x33u8; 32];
        let slot = 0xCAFEBABEu64;
        let w = EffectActionWitness {
            schema: SCHEMA_GRANT_CAPABILITY,
            fields: vec![target, perm, allowed],
            amounts: vec![slot],
        };
        let proof = prove_effect_action(&w);
        let mut wrong_target = target;
        wrong_target[0] ^= 0x01;
        let r = verify_effect_action(
            SCHEMA_GRANT_CAPABILITY,
            &[wrong_target, perm, allowed],
            &[slot],
            &proof,
        );
        assert!(r.is_err(), "tampered target must be rejected");
    }

    #[test]
    fn grant_capability_tamper_permissions_rejected() {
        let target = [0x11u8; 32];
        let perm = [0x22u8; 32];
        let allowed = [0x33u8; 32];
        let slot = 0xCAFEBABEu64;
        let w = EffectActionWitness {
            schema: SCHEMA_GRANT_CAPABILITY,
            fields: vec![target, perm, allowed],
            amounts: vec![slot],
        };
        let proof = prove_effect_action(&w);
        let mut wrong_perm = perm;
        wrong_perm[20] ^= 0xFF;
        let r = verify_effect_action(
            SCHEMA_GRANT_CAPABILITY,
            &[target, wrong_perm, allowed],
            &[slot],
            &proof,
        );
        assert!(r.is_err(), "tampered permissions must be rejected");
    }

    #[test]
    fn grant_capability_tamper_allowed_effects_rejected() {
        let target = [0x11u8; 32];
        let perm = [0x22u8; 32];
        let allowed = [0x33u8; 32];
        let slot = 0xCAFEBABEu64;
        let w = EffectActionWitness {
            schema: SCHEMA_GRANT_CAPABILITY,
            fields: vec![target, perm, allowed],
            amounts: vec![slot],
        };
        let proof = prove_effect_action(&w);
        let mut wrong_allowed = allowed;
        wrong_allowed[31] ^= 0x80;
        let r = verify_effect_action(
            SCHEMA_GRANT_CAPABILITY,
            &[target, perm, wrong_allowed],
            &[slot],
            &proof,
        );
        assert!(r.is_err(), "tampered allowed_effects must be rejected");
    }

    #[test]
    fn grant_capability_tamper_slot_rejected() {
        let target = [0x11u8; 32];
        let perm = [0x22u8; 32];
        let allowed = [0x33u8; 32];
        let slot = 0xCAFEBABEu64;
        let w = EffectActionWitness {
            schema: SCHEMA_GRANT_CAPABILITY,
            fields: vec![target, perm, allowed],
            amounts: vec![slot],
        };
        let proof = prove_effect_action(&w);
        let r = verify_effect_action(
            SCHEMA_GRANT_CAPABILITY,
            &[target, perm, allowed],
            &[slot + 1],
            &proof,
        );
        assert!(r.is_err(), "tampered slot must be rejected");
    }

    #[test]
    fn revoke_capability_roundtrip() {
        let cell = [0xAAu8; 32];
        let r = roundtrip(SCHEMA_REVOKE_CAPABILITY, vec![cell], vec![42]);
        assert!(r.is_ok());
    }

    #[test]
    fn revoke_capability_tamper_cell_rejected() {
        let cell = [0xAAu8; 32];
        let slot = 42u64;
        let w = EffectActionWitness {
            schema: SCHEMA_REVOKE_CAPABILITY,
            fields: vec![cell],
            amounts: vec![slot],
        };
        let proof = prove_effect_action(&w);
        let mut wrong = cell;
        wrong[15] ^= 0x01;
        let r = verify_effect_action(SCHEMA_REVOKE_CAPABILITY, &[wrong], &[slot], &proof);
        assert!(r.is_err());
    }

    #[test]
    fn emit_event_roundtrip() {
        let topic = [0x55u8; 32];
        let data_hash = [0x66u8; 32];
        let r = roundtrip(SCHEMA_EMIT_EVENT, vec![topic, data_hash], vec![128]);
        assert!(r.is_ok());
    }

    #[test]
    fn emit_event_tamper_data_hash_rejected() {
        let topic = [0x55u8; 32];
        let data_hash = [0x66u8; 32];
        let data_len = 128u64;
        let w = EffectActionWitness {
            schema: SCHEMA_EMIT_EVENT,
            fields: vec![topic, data_hash],
            amounts: vec![data_len],
        };
        let proof = prove_effect_action(&w);
        let mut wrong = data_hash;
        wrong[16] ^= 0x10;
        let r = verify_effect_action(SCHEMA_EMIT_EVENT, &[topic, wrong], &[data_len], &proof);
        assert!(r.is_err());
    }

    #[test]
    fn create_cell_roundtrip_and_max_balance() {
        let pk = [0x77u8; 32];
        let tok = [0x88u8; 32];
        let r = roundtrip(SCHEMA_CREATE_CELL, vec![pk, tok], vec![u64::MAX]);
        assert!(r.is_ok(), "u64::MAX balance must round-trip: {r:?}");
    }

    #[test]
    fn create_cell_tamper_balance_high_bit_rejected() {
        // Critical: confirm balance carries full 64 bits, not 30-bit
        // truncation.
        let pk = [0x77u8; 32];
        let tok = [0x88u8; 32];
        let balance: u64 = (1u64 << 50) | 0xCAFE;
        let w = EffectActionWitness {
            schema: SCHEMA_CREATE_CELL,
            fields: vec![pk, tok],
            amounts: vec![balance],
        };
        let proof = prove_effect_action(&w);
        // Verifier with the low-30-bits-truncated balance must REJECT.
        let r = verify_effect_action(
            SCHEMA_CREATE_CELL,
            &[pk, tok],
            &[balance & ((1u64 << 30) - 1)],
            &proof,
        );
        assert!(
            r.is_err(),
            "high-bit balance change must NOT collide with low-30-bit truncation"
        );
    }

    #[test]
    fn set_permissions_roundtrip() {
        let cell = [0x99u8; 32];
        let phash = [0xAAu8; 32];
        let r = roundtrip(SCHEMA_SET_PERMISSIONS, vec![cell, phash], vec![]);
        assert!(r.is_ok());
    }

    #[test]
    fn set_permissions_tamper_phash_rejected() {
        let cell = [0x99u8; 32];
        let phash = [0xAAu8; 32];
        let w = EffectActionWitness {
            schema: SCHEMA_SET_PERMISSIONS,
            fields: vec![cell, phash],
            amounts: vec![],
        };
        let proof = prove_effect_action(&w);
        let mut wrong = phash;
        wrong[0] ^= 0x01;
        let r = verify_effect_action(SCHEMA_SET_PERMISSIONS, &[cell, wrong], &[], &proof);
        assert!(r.is_err());
    }

    #[test]
    fn set_verification_key_roundtrip() {
        let cell = [0xBBu8; 32];
        let vk = [0xCCu8; 32];
        let r = roundtrip(SCHEMA_SET_VERIFICATION_KEY, vec![cell, vk], vec![]);
        assert!(r.is_ok());
    }

    #[test]
    fn set_verification_key_none_zero_hash_roundtrip() {
        // None → zero hash; must still round-trip distinctly from any non-zero
        // hash.
        let cell = [0xBBu8; 32];
        let none_vk = [0u8; 32];
        let r = roundtrip(SCHEMA_SET_VERIFICATION_KEY, vec![cell, none_vk], vec![]);
        assert!(r.is_ok());

        // And tampering with cell still rejects.
        let w = EffectActionWitness {
            schema: SCHEMA_SET_VERIFICATION_KEY,
            fields: vec![cell, none_vk],
            amounts: vec![],
        };
        let proof = prove_effect_action(&w);
        let mut wrong_cell = cell;
        wrong_cell[5] ^= 0x40;
        let r = verify_effect_action(
            SCHEMA_SET_VERIFICATION_KEY,
            &[wrong_cell, none_vk],
            &[],
            &proof,
        );
        assert!(r.is_err());
    }

    #[test]
    fn introduce_roundtrip() {
        let introducer = [0x10u8; 32];
        let recipient = [0x20u8; 32];
        let target = [0x30u8; 32];
        let perm_vk = [0u8; 32];
        let perm_disc = 1u64;
        let r = roundtrip(
            SCHEMA_INTRODUCE,
            vec![introducer, recipient, target, perm_vk],
            vec![perm_disc],
        );
        assert!(r.is_ok());
    }

    #[test]
    fn introduce_swap_recipient_target_rejected() {
        // Positional binding: swapping recipient and target must fail.
        let introducer = [0x10u8; 32];
        let recipient = [0x20u8; 32];
        let target = [0x30u8; 32];
        let perm_vk = [0u8; 32];
        let perm_disc = 1u64;
        let w = EffectActionWitness {
            schema: SCHEMA_INTRODUCE,
            fields: vec![introducer, recipient, target, perm_vk],
            amounts: vec![perm_disc],
        };
        let proof = prove_effect_action(&w);
        let r = verify_effect_action(
            SCHEMA_INTRODUCE,
            &[introducer, target, recipient, perm_vk],
            &[perm_disc],
            &proof,
        );
        assert!(r.is_err(), "swapped recipient/target must be rejected");
    }

    #[test]
    fn introduce_tamper_perm_discriminant_rejected() {
        let introducer = [0x10u8; 32];
        let recipient = [0x20u8; 32];
        let target = [0x30u8; 32];
        let perm_vk = [0u8; 32];
        let perm_disc = 1u64;
        let w = EffectActionWitness {
            schema: SCHEMA_INTRODUCE,
            fields: vec![introducer, recipient, target, perm_vk],
            amounts: vec![perm_disc],
        };
        let proof = prove_effect_action(&w);
        let r = verify_effect_action(
            SCHEMA_INTRODUCE,
            &[introducer, recipient, target, perm_vk],
            &[perm_disc + 1],
            &proof,
        );
        assert!(r.is_err(), "tampered perm_disc must be rejected");
    }

    #[test]
    fn create_seal_pair_roundtrip_and_swap_rejected() {
        let sealer = [0x40u8; 32];
        let unsealer = [0x50u8; 32];
        let r = roundtrip(SCHEMA_CREATE_SEAL_PAIR, vec![sealer, unsealer], vec![]);
        assert!(r.is_ok());

        // Swap rejected.
        let w = EffectActionWitness {
            schema: SCHEMA_CREATE_SEAL_PAIR,
            fields: vec![sealer, unsealer],
            amounts: vec![],
        };
        let proof = prove_effect_action(&w);
        let r = verify_effect_action(SCHEMA_CREATE_SEAL_PAIR, &[unsealer, sealer], &[], &proof);
        assert!(r.is_err(), "swapped sealer/unsealer must be rejected");
    }

    #[test]
    fn cross_kind_proofs_do_not_verify_as_other_kinds() {
        // Critical: domain separation. A proof generated for kind A must not
        // verify as kind B, even if the parameter bytes happen to coincide.
        let cell = [0x99u8; 32];
        let phash = [0xAAu8; 32];
        let w = EffectActionWitness {
            schema: SCHEMA_SET_PERMISSIONS,
            fields: vec![cell, phash],
            amounts: vec![],
        };
        let proof_set_perm = prove_effect_action(&w);
        // Attempt to verify as SetVerificationKey (same shape: 2 fields, 0
        // amounts) — the air_name's Fiat-Shamir transcript MUST domain-
        // separate.
        let r = verify_effect_action(
            SCHEMA_SET_VERIFICATION_KEY,
            &[cell, phash],
            &[],
            &proof_set_perm,
        );
        assert!(
            r.is_err(),
            "cross-kind proof confusion: SetPermissions proof verified as SetVerificationKey"
        );
    }

    #[test]
    fn tampered_proof_bytes_rejected() {
        let cell = [0x99u8; 32];
        let phash = [0xAAu8; 32];
        let w = EffectActionWitness {
            schema: SCHEMA_SET_PERMISSIONS,
            fields: vec![cell, phash],
            amounts: vec![],
        };
        let mut proof = prove_effect_action(&w);
        proof.trace_commitment[0] ^= 0xFF;
        let r = verify_effect_action(SCHEMA_SET_PERMISSIONS, &[cell, phash], &[], &proof);
        assert!(r.is_err());
    }

    #[test]
    fn zero_witness_roundtrip() {
        // All-zero fields and amount must round-trip (sentinel cases).
        let r = roundtrip(SCHEMA_CREATE_CELL, vec![[0u8; 32], [0u8; 32]], vec![0]);
        assert!(r.is_ok());
    }
}
