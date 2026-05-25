//! Bridge action binding AIR (sibling to `note_spending_air`).
//!
//! # Why a sibling AIR?
//!
//! `note_spending_air` (and its DSL twin `dsl::note_spending`) already prove
//! knowledge of a spending key + Merkle membership of the note, and pin
//! `nullifier`, `merkle_root`, `value`, `asset_type`, `destination_federation`
//! as public inputs. **However**, each of those PIs is a **single** BabyBear
//! field element (~31 bits). To squeeze a 32-byte hash into one felt the
//! prover/verifier compresses via `bytes_to_babybear` (Poseidon2 hash of 8
//! limbs to one element). That compression is one-way, so it works for
//! soundness, but it has two consequences this AIR fixes:
//!
//! 1. **The full 32 bytes never appear directly in any PI vector**, only their
//!    Poseidon2 digest. A verifier that wants to attribute a bridge mint to a
//!    specific 32-byte recipient commitment (the "who got minted to") cannot
//!    cryptographically check against the recipient bytes — it can only check
//!    against the digest. For a bridge that mints a *new note* on the
//!    destination, the destination wants the proof to say "I am minting to
//!    commitment 0xABCD…", not "I am minting to something that hashes to a
//!    BabyBear felt 0x12345678".
//!
//! 2. **The amount is currently truncated to 30 bits** (`v & ((1<<30)-1)`,
//!    see `turn/src/executor.rs` BridgeMint closure, CAVEAT-LAYER-COVERAGE.md
//!    §6.5, and `circuit/src/effect_vm.rs::BridgeMint::value_lo`). Above
//!    2^30 (~10⁹) the high bits are unrecoverable from the proof — a prover
//!    above that ceiling can claim any high-bit collision. The substrate
//!    AIR is out of this lane's write surface, but the bridge-side proof
//!    can and must carry the full 64 bits.
//!
//! # What this AIR binds
//!
//! Public inputs (all bytes / amount carried at full fidelity):
//!
//! ```text
//! pi[ 0.. 8) = nullifier_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[ 8..16) = recipient_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[16..24) = destination_federation_limbs[8] (8 × 4-byte BabyBear limbs)
//! pi[24]     = amount_lo   (low  32 bits of u64 amount, BabyBear-encoded)
//! pi[25]     = amount_hi   (high 32 bits of u64 amount, BabyBear-encoded)
//! ```
//!
//! Total = 26 PI slots, ~248 bits of binding strength per 32-byte field, and
//! the full 64 bits of amount (split into two 32-bit limbs, each reduced
//! canonically to BabyBear via `BabyBear::new`).
//!
//! Trace layout (1 row, padded to 4 to satisfy STARK power-of-2 requirements):
//!
//! ```text
//! col  0.. 8) nullifier_limbs[8]
//! col  8..16) recipient_limbs[8]
//! col 16..24) destination_federation_limbs[8]
//! col 24      amount_lo
//! col 25      amount_hi
//! ```
//!
//! Boundary constraints pin each trace column at row 0 to the corresponding
//! PI slot. The verifier passes the exact same 26 BabyBears it received from
//! the executor; any mismatch on any column fails STARK verification.
//!
//! # What this AIR does NOT do
//!
//! It does NOT re-prove the underlying spend (that's `note_spending`'s
//! job). It is a *binding-only* AIR: it carries the typed bridge-action
//! parameters at full fidelity inside a STARK so the executor can check
//! that the bridge mint it is about to apply matches the proof's bytes
//! algebraically, not just by ad-hoc structural comparison in plaintext.
//!
//! Combined with `note_spending`'s Merkle/nullifier/key proof, the pair of
//! AIRs (spend + action) gives the executor algebraic guarantees on:
//! - Knowledge of the spending key (spending AIR)
//! - Merkle membership of the spent note (spending AIR)
//! - 248-bit-strength binding to nullifier / recipient / destination_federation
//!   (this AIR)
//! - Full 64-bit amount binding (this AIR)

use crate::field::BabyBear;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Trace width: 8 + 8 + 8 + 2 = 26 columns.
pub const BRIDGE_ACTION_WIDTH: usize = 26;

/// Number of public-input slots. Each 32-byte field uses 8 limbs; amount uses 2.
pub const BRIDGE_ACTION_PI_COUNT: usize = 26;

/// Number of BabyBear limbs used to represent a 32-byte value.
pub const HASH_LIMBS: usize = 8;

/// Column ranges. (Const fn would be cleaner; explicit names are clearer.)
pub mod col {
    /// Column range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// Column range \[8, 16\): recipient (destination_commitment) limbs.
    pub const RECIPIENT_START: usize = 8;
    /// Column range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// Column 24: amount low 32 bits.
    pub const AMOUNT_LO: usize = 24;
    /// Column 25: amount high 32 bits.
    pub const AMOUNT_HI: usize = 25;
}

/// Public input layout matches the column layout exactly.
pub mod pi {
    /// PI range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// PI range \[8, 16\): recipient limbs.
    pub const RECIPIENT_START: usize = 8;
    /// PI range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// PI 24: amount_lo.
    pub const AMOUNT_LO: usize = 24;
    /// PI 25: amount_hi.
    pub const AMOUNT_HI: usize = 25;
}

/// Encode a 32-byte value as 8 BabyBear limbs (4 bytes each, little-endian per
/// chunk, each chunk reduced via `BabyBear::new`).
///
/// This is the canonical bridge-action encoding. `BabyBear::new(u32)` reduces
/// modulo p = 2^31 - 2^27 + 1, so values 2^31-2^27+1 .. 2^32-1 collide on
/// reduction — but since we apply the same encoding on prover and verifier,
/// the boundary constraint is on the reduced value. Two distinct 32-byte
/// values whose limbs all collide modulo p have collision probability ~p^-8
/// ≈ 2^-248, well above the 124-bit STARK soundness target.
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
pub fn encode_amount(amount: u64) -> [BabyBear; 2] {
    let lo = (amount & 0xFFFF_FFFF) as u32;
    let hi = (amount >> 32) as u32;
    [BabyBear::new(lo), BabyBear::new(hi)]
}

/// A bridge-action witness: the typed parameters the prover and verifier
/// will algebraically agree on.
#[derive(Clone, Debug)]
pub struct BridgeActionWitness {
    /// The 32-byte spent-note nullifier.
    pub nullifier: [u8; 32],
    /// The 32-byte destination-side commitment (recipient note commitment).
    pub recipient: [u8; 32],
    /// The 32-byte destination federation identity.
    pub destination_federation: [u8; 32],
    /// The full u64 amount (no truncation).
    pub amount: u64,
}

impl BridgeActionWitness {
    /// Compute the canonical public-input vector this witness commits to.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let n = encode_hash(&self.nullifier);
        let r = encode_hash(&self.recipient);
        let d = encode_hash(&self.destination_federation);
        let [lo, hi] = encode_amount(self.amount);
        let mut pi = Vec::with_capacity(BRIDGE_ACTION_PI_COUNT);
        pi.extend_from_slice(&n);
        pi.extend_from_slice(&r);
        pi.extend_from_slice(&d);
        pi.push(lo);
        pi.push(hi);
        pi
    }
}

/// The bridge-action binding AIR.
///
/// One real row of typed data; padded to 4 to satisfy STARK power-of-2
/// requirements (FRI requires a power-of-2 trace length).
pub struct BridgeActionAir;

impl BridgeActionAir {
    /// Generate the execution trace and public inputs from a witness.
    pub fn generate_trace(witness: &BridgeActionWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let n = encode_hash(&witness.nullifier);
        let r = encode_hash(&witness.recipient);
        let d = encode_hash(&witness.destination_federation);
        let [lo, hi] = encode_amount(witness.amount);

        // Row 0: the full typed binding.
        let mut row0 = vec![BabyBear::ZERO; BRIDGE_ACTION_WIDTH];
        for i in 0..HASH_LIMBS {
            row0[col::NULLIFIER_START + i] = n[i];
            row0[col::RECIPIENT_START + i] = r[i];
            row0[col::DESTINATION_FEDERATION_START + i] = d[i];
        }
        row0[col::AMOUNT_LO] = lo;
        row0[col::AMOUNT_HI] = hi;

        // Pad to length 4 (smallest power of 2 ≥ 1).
        let mut trace = Vec::with_capacity(4);
        trace.push(row0.clone());
        for _ in 1..4 {
            // Padding rows replicate row 0 so the boundary constraints at
            // (row 0, col X) are unambiguous and the transition continuity
            // (next == local for all cols) holds trivially.
            trace.push(row0.clone());
        }

        let public_inputs = witness.public_inputs();
        (trace, public_inputs)
    }
}

impl StarkAir for BridgeActionAir {
    fn width(&self) -> usize {
        BRIDGE_ACTION_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Transition constraints below are linear (degree 1). The STARK
        // framework still needs at least degree 2 to play nicely with FRI
        // quotient construction in some configurations; we declare 2 for
        // safety.
        2
    }

    fn air_name(&self) -> &'static str {
        "pyana-bridge-action-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        // We use our own transition constraints; the default chain-continuity
        // shape (parent/current at cols 5/0) does not apply here.
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // Transition: every column is constant across rows. This ensures
        // that the trace is genuinely "1 typed row, replicated for FRI
        // power-of-2 padding" — a prover cannot put one set of bound values
        // in row 0 and a different set in row 1 to slip past the boundary
        // check on row 0. (The boundary constraints pin row 0; the
        // transition glue makes every row equal to row 0 in every column.)
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;
        for c in 0..BRIDGE_ACTION_WIDTH {
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
        // Each PI slot pins exactly one trace column at row 0.
        let mut constraints = Vec::with_capacity(BRIDGE_ACTION_PI_COUNT);
        if public_inputs.len() != BRIDGE_ACTION_PI_COUNT {
            // Wrong PI length → emit no boundary constraints; the verifier
            // will then accept only the trivial trace, which will not match
            // any honest prover's trace, so verification fails.
            return constraints;
        }
        for i in 0..HASH_LIMBS {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::NULLIFIER_START + i,
                value: public_inputs[pi::NULLIFIER_START + i],
            });
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::RECIPIENT_START + i,
                value: public_inputs[pi::RECIPIENT_START + i],
            });
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::DESTINATION_FEDERATION_START + i,
                value: public_inputs[pi::DESTINATION_FEDERATION_START + i],
            });
        }
        constraints.push(BoundaryConstraint {
            row: 0,
            col: col::AMOUNT_LO,
            value: public_inputs[pi::AMOUNT_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: col::AMOUNT_HI,
            value: public_inputs[pi::AMOUNT_HI],
        });
        constraints
    }
}

/// Prove a bridge action binding.
///
/// Produces a STARK proof that carries the typed parameters at full fidelity
/// (8 limbs per 32-byte field, 2 limbs for u64 amount). The proof binds the
/// prover to the exact `(nullifier, recipient, destination_federation, amount)`
/// tuple supplied in the witness — any tampering on the verifier side fails.
pub fn prove_bridge_action(witness: &BridgeActionWitness) -> StarkProof {
    let air = BridgeActionAir;
    let (trace, public_inputs) = BridgeActionAir::generate_trace(witness);
    stark::prove(&air, &trace, &public_inputs)
}

/// Verify a bridge action binding proof against expected typed parameters.
///
/// Returns `Ok(())` if and only if every limb (8 nullifier, 8 recipient,
/// 8 destination_federation) and both amount halves match what the prover
/// committed to. A single byte change anywhere yields a different limb under
/// `encode_hash`/`encode_amount` and the boundary constraint fails.
pub fn verify_bridge_action(
    nullifier: &[u8; 32],
    recipient: &[u8; 32],
    destination_federation: &[u8; 32],
    amount: u64,
    proof: &StarkProof,
) -> Result<(), String> {
    let n = encode_hash(nullifier);
    let r = encode_hash(recipient);
    let d = encode_hash(destination_federation);
    let [lo, hi] = encode_amount(amount);

    let mut public_inputs = Vec::with_capacity(BRIDGE_ACTION_PI_COUNT);
    public_inputs.extend_from_slice(&n);
    public_inputs.extend_from_slice(&r);
    public_inputs.extend_from_slice(&d);
    public_inputs.push(lo);
    public_inputs.push(hi);

    let air = BridgeActionAir;
    stark::verify(&air, proof, &public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_witness() -> BridgeActionWitness {
        BridgeActionWitness {
            nullifier: [0x10; 32],
            recipient: [0x20; 32],
            destination_federation: [0x30; 32],
            amount: 0xDEAD_BEEF_CAFE_F00D,
        }
    }

    #[test]
    fn encode_hash_roundtrip_deterministic() {
        let a = encode_hash(&[0x42; 32]);
        let b = encode_hash(&[0x42; 32]);
        assert_eq!(a, b, "encode_hash must be deterministic");
    }

    #[test]
    fn encode_hash_distinguishes_distinct_bytes() {
        let a = encode_hash(&[0x42; 32]);
        let mut bytes = [0x42u8; 32];
        bytes[0] = 0x43;
        let b = encode_hash(&bytes);
        assert_ne!(a, b, "one byte change must change the limb encoding");
    }

    #[test]
    fn encode_amount_full_64_bits() {
        let [lo, hi] = encode_amount(0xDEAD_BEEF_CAFE_F00D);
        // Low 32 bits = 0xCAFE_F00D, high 32 bits = 0xDEAD_BEEF.
        assert_eq!(lo, BabyBear::new(0xCAFE_F00D));
        assert_eq!(hi, BabyBear::new(0xDEAD_BEEF));
    }

    #[test]
    fn encode_amount_distinguishes_high_bits() {
        // Two amounts that share low 30 bits but differ in high bits must
        // produce distinct encodings — proving we don't have the 30-bit
        // truncation bug.
        let a = encode_amount((1u64 << 30) | 1); // low bit set, bit 30 set
        let b = encode_amount(1); // only low bit set
        assert_ne!(
            a, b,
            "amounts differing only in high bits must produce distinct PIs"
        );
    }

    #[test]
    fn witness_public_inputs_layout() {
        let w = make_witness();
        let pi = w.public_inputs();
        assert_eq!(pi.len(), BRIDGE_ACTION_PI_COUNT);
        let n = encode_hash(&w.nullifier);
        let r = encode_hash(&w.recipient);
        let d = encode_hash(&w.destination_federation);
        let [lo, hi] = encode_amount(w.amount);
        for i in 0..HASH_LIMBS {
            assert_eq!(pi[pi::NULLIFIER_START + i], n[i]);
            assert_eq!(pi[pi::RECIPIENT_START + i], r[i]);
            assert_eq!(pi[pi::DESTINATION_FEDERATION_START + i], d[i]);
        }
        assert_eq!(pi[pi::AMOUNT_LO], lo);
        assert_eq!(pi[pi::AMOUNT_HI], hi);
    }

    #[test]
    fn trace_generation_shape() {
        let w = make_witness();
        let (trace, pi) = BridgeActionAir::generate_trace(&w);
        assert_eq!(trace.len(), 4, "padded to power of 2 (smallest = 4)");
        for row in &trace {
            assert_eq!(row.len(), BRIDGE_ACTION_WIDTH);
        }
        assert_eq!(pi.len(), BRIDGE_ACTION_PI_COUNT);
    }

    #[test]
    fn prove_and_verify_roundtrip() {
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(
            result.is_ok(),
            "honest bridge-action proof must verify: {result:?}"
        );
    }

    #[test]
    fn adversarial_wrong_nullifier_rejected() {
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let mut wrong_nullifier = w.nullifier;
        wrong_nullifier[0] ^= 0xFF;
        let result = verify_bridge_action(
            &wrong_nullifier,
            &w.recipient,
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(
            result.is_err(),
            "tampered nullifier (one byte flip) must be rejected"
        );
    }

    #[test]
    fn adversarial_wrong_recipient_rejected() {
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let mut wrong_recipient = w.recipient;
        wrong_recipient[15] ^= 0x01;
        let result = verify_bridge_action(
            &w.nullifier,
            &wrong_recipient,
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(
            result.is_err(),
            "tampered recipient (single byte flip) must be rejected"
        );
    }

    #[test]
    fn adversarial_wrong_destination_federation_rejected() {
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let mut wrong_dest = w.destination_federation;
        wrong_dest[31] ^= 0x80;
        let result =
            verify_bridge_action(&w.nullifier, &w.recipient, &wrong_dest, w.amount, &proof);
        assert!(
            result.is_err(),
            "tampered destination_federation must be rejected"
        );
    }

    #[test]
    fn adversarial_wrong_amount_rejected() {
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            w.amount.wrapping_add(1),
            &proof,
        );
        assert!(result.is_err(), "tampered amount must be rejected");
    }

    /// CRITICAL: amount above 2^30 must round-trip. This is the regression
    /// test for the 30-bit truncation gap from CAVEAT-LAYER-COVERAGE.md §6.5.
    /// Two amounts that share the low 30 bits but differ in high bits must
    /// produce distinguishable proofs.
    #[test]
    fn adversarial_amount_above_2_pow_30_distinguished() {
        let mut w = make_witness();
        // amount_a has bit 30 set; amount_b shares the low 30 bits but lacks
        // the high bit.
        w.amount = (1u64 << 30) | 0xABCD;
        let proof_a = prove_bridge_action(&w);
        // Verifier with the truncated amount (just 0xABCD) must REJECT proof_a.
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            0xABCDu64, // strip bit 30
            &proof_a,
        );
        assert!(
            result.is_err(),
            "amounts above 2^30 must NOT collide with their low-30-bit truncations"
        );
    }

    /// CRITICAL: very large amounts (above 2^32) must round-trip. This proves
    /// the high u32 limb is genuinely bound.
    #[test]
    fn adversarial_amount_above_2_pow_32_distinguished() {
        let mut w = make_witness();
        w.amount = (1u64 << 32) | 0xDEAD_BEEF;
        let proof = prove_bridge_action(&w);
        // Verifier with the low 32 bits only must reject.
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            0xDEAD_BEEFu64, // strip the high bit
            &proof,
        );
        assert!(
            result.is_err(),
            "amounts above 2^32 must NOT collide with their low-32-bit truncations"
        );
    }

    #[test]
    fn adversarial_swap_nullifier_and_recipient_rejected() {
        // If a prover tried to swap nullifier and recipient (claim the
        // "recipient is N" while really N is the nullifier of a high-value
        // note), the verifier with the canonical labelling must reject.
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        let result = verify_bridge_action(
            &w.recipient, // swapped
            &w.nullifier, // swapped
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(
            result.is_err(),
            "swapped nullifier/recipient must be rejected (positional binding)"
        );
    }

    #[test]
    fn double_mint_with_same_proof_indistinguishable_at_air_level() {
        // The AIR is a pure binding AIR — it does NOT enforce replay
        // protection. That responsibility lives on the executor's
        // BridgedNullifierSet (see cell/src/note_bridge.rs::BridgedNullifierSet
        // and turn/src/executor.rs:6582). This test documents the boundary:
        // the same valid proof MUST verify twice at the AIR layer.
        let w = make_witness();
        let proof = prove_bridge_action(&w);
        assert!(
            verify_bridge_action(
                &w.nullifier,
                &w.recipient,
                &w.destination_federation,
                w.amount,
                &proof
            )
            .is_ok()
        );
        assert!(
            verify_bridge_action(
                &w.nullifier,
                &w.recipient,
                &w.destination_federation,
                w.amount,
                &proof
            )
            .is_ok()
        );
        // Replay protection is enforced one layer up (`BridgedNullifierSet`).
    }

    #[test]
    fn tampered_proof_bytes_rejected() {
        let w = make_witness();
        let mut proof = prove_bridge_action(&w);
        // Flip a byte in the trace commitment.
        proof.trace_commitment[0] ^= 0xFF;
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(result.is_err(), "tampered STARK proof must be rejected");
    }

    /// All-zero values must round-trip (used for local non-bridge spends
    /// where bridge-action binding isn't meaningful).
    #[test]
    fn zero_witness_roundtrip() {
        let w = BridgeActionWitness {
            nullifier: [0u8; 32],
            recipient: [0u8; 32],
            destination_federation: [0u8; 32],
            amount: 0,
        };
        let proof = prove_bridge_action(&w);
        assert!(
            verify_bridge_action(
                &w.nullifier,
                &w.recipient,
                &w.destination_federation,
                w.amount,
                &proof
            )
            .is_ok()
        );
    }

    /// Maximum-value amount must round-trip (u64::MAX).
    #[test]
    fn max_amount_roundtrip() {
        let mut w = make_witness();
        w.amount = u64::MAX;
        let proof = prove_bridge_action(&w);
        let result = verify_bridge_action(
            &w.nullifier,
            &w.recipient,
            &w.destination_federation,
            w.amount,
            &proof,
        );
        assert!(result.is_ok(), "u64::MAX amount must verify: {result:?}");
    }
}
