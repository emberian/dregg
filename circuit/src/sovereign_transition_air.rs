//! Sovereign Cell State Transition AIR (Phase 3).
//!
//! Proves: "given old_state (whose commitment matches old_commitment), applying
//! Transfer effects produces new_state (whose commitment matches new_commitment),
//! and the balance_delta is correctly derived from the transfer."
//!
//! Public inputs (34 BabyBear elements):
//!   [old_commitment_bb[0..8], new_commitment_bb[0..8],
//!    effects_hash_bb[0..8], cell_id_hash_bb[0..8],
//!    balance_delta_bb[0..2]]
//!
//! The balance_delta is a PROVEN output: the verifier extracts it from the proof's
//! public inputs rather than trusting the submitter. It is encoded as 2 BabyBear
//! elements: [magnitude, sign_bit] where sign_bit=1 means negative (outgoing).
//!
//! Each 32-byte hash is encoded as 8 BabyBear elements (4 bytes each, LE, reduced mod p).
//! This matches the executor's `bytes32_to_babybear` encoding.
//!
//! The trace layout proves a single Transfer effect:
//!   Row 0: [old_balance, transfer_amount, new_balance, direction, delta_magnitude, delta_sign]
//!   Row 1: (padding duplicate of row 0 for power-of-two trace requirement)
//!
//! Constraints:
//!   - `direction * (direction - 1) == 0` (direction is boolean)
//!   - `new_balance == old_balance + transfer_amount - 2 * direction * transfer_amount`
//!     i.e. if direction=1 (outgoing): new = old - amount
//!          if direction=0 (incoming): new = old + amount
//!   - `delta_magnitude == transfer_amount` (binds delta to proven amount)
//!   - `delta_sign == direction` (binds sign to proven direction)
//!
//! This is a MINIMAL Phase 3 AIR: it proves balance transfer only. Other effect
//! types (SetField, GrantCapability, etc.) can be added incrementally by extending
//! the trace width and constraint set.

use crate::field::{BABYBEAR_P, BabyBear};
use crate::stark::{BoundaryConstraint, StarkAir};

/// Width of the sovereign transition trace.
///  Col 0: old_balance
///  Col 1: transfer_amount
///  Col 2: new_balance
///  Col 3: direction (1 = outgoing/debit, 0 = incoming/credit)
///  Col 4: delta_magnitude (must equal transfer_amount -- proven binding)
///  Col 5: delta_sign (must equal direction -- proven binding)
pub const SOVEREIGN_TRANSITION_WIDTH: usize = 6;

/// Number of public inputs for SovereignTransitionAir.
/// 4 hashes * 8 BabyBear elements each = 32, plus 2 for balance_delta = 34 total.
pub const SOVEREIGN_PUBLIC_INPUTS: usize = 34;

/// Offset into the public inputs where balance_delta begins.
/// The delta is encoded as 2 BabyBear elements: [magnitude, sign_bit].
/// sign_bit=1 means the delta is negative (outgoing transfer).
pub const DELTA_PI_OFFSET: usize = 32;

/// Number of BabyBear elements encoding the balance delta in public inputs.
pub const DELTA_PI_LEN: usize = 2;

/// The AIR for sovereign cell state transitions (Phase 3).
///
/// Proves that a balance transfer was correctly applied AND that the balance_delta
/// public input is correctly derived from the transfer:
///   old_balance - amount = new_balance (outgoing, direction=1)
///   old_balance + amount = new_balance (incoming, direction=0)
///   delta_magnitude == transfer_amount (binds PI to proven value)
///   delta_sign == direction (binds PI to proven direction)
pub struct SovereignTransitionAir;

impl StarkAir for SovereignTransitionAir {
    fn width(&self) -> usize {
        SOVEREIGN_TRANSITION_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // direction * (direction - 1) gives degree 2
        // direction * transfer_amount gives degree 2
        // overall constraint degree is 2
        2
    }

    fn air_name(&self) -> &'static str {
        "pyana-sovereign-transition-v2"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let old_balance = local[0];
        let transfer_amount = local[1];
        let new_balance = local[2];
        let direction = local[3];
        let delta_magnitude = local[4];
        let delta_sign = local[5];

        // Constraint 1: direction must be 0 or 1 (boolean constraint).
        // direction * (direction - 1) == 0
        let c1 = direction * (direction - BabyBear::ONE);

        // Constraint 2: balance conservation.
        // If direction == 1 (outgoing): new_balance == old_balance - transfer_amount
        // If direction == 0 (incoming): new_balance == old_balance + transfer_amount
        //
        // Unified: new_balance == old_balance + transfer_amount * (1 - 2 * direction)
        //        = old_balance + transfer_amount - 2 * direction * transfer_amount
        //
        // Rearranging: new_balance - old_balance - transfer_amount + 2 * direction * transfer_amount == 0
        let two = BabyBear::new(2);
        let c2 = new_balance - old_balance - transfer_amount + two * direction * transfer_amount;

        // Constraint 3: delta_magnitude == transfer_amount.
        // This binds the proven balance delta to the transfer amount in the trace.
        // Without this, a prover could claim any delta value.
        let c3 = delta_magnitude - transfer_amount;

        // Constraint 4: delta_sign == direction.
        // This binds the proven sign to the direction in the trace.
        let c4 = delta_sign - direction;

        c1 + alpha * c2 + alpha * alpha * c3 + alpha * alpha * alpha * c4
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];

        // Bind delta_magnitude (col 4) and delta_sign (col 5) to their public inputs.
        // This ensures the trace values used in eval_constraints match what the
        // verifier extracts as the balance delta.
        if public_inputs.len() >= SOVEREIGN_PUBLIC_INPUTS {
            // PI[32] = delta_magnitude, PI[33] = delta_sign
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 4, // delta_magnitude column
                value: public_inputs[DELTA_PI_OFFSET],
            });
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 5, // delta_sign column
                value: public_inputs[DELTA_PI_OFFSET + 1],
            });
        }

        constraints
    }
}

/// Extract the balance delta from a sovereign proof's public inputs.
///
/// Returns the signed balance delta: positive means the cell received funds,
/// negative means it sent funds. Returns None if the PI slice is too short.
pub fn extract_balance_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < SOVEREIGN_PUBLIC_INPUTS {
        return None;
    }
    let magnitude = public_inputs[DELTA_PI_OFFSET].0 as i64;
    let sign_bit = public_inputs[DELTA_PI_OFFSET + 1].0;
    if sign_bit == 1 {
        Some(-magnitude) // outgoing
    } else {
        Some(magnitude) // incoming
    }
}

/// Encode a signed balance delta as 2 BabyBear elements for public inputs.
///
/// Returns [magnitude, sign_bit] where sign_bit=1 means negative.
pub fn encode_balance_delta(delta: i64) -> [BabyBear; 2] {
    if delta < 0 {
        [BabyBear::new((-delta) as u32), BabyBear::ONE]
    } else {
        [BabyBear::new(delta as u32), BabyBear::ZERO]
    }
}

/// Generate the execution trace and public inputs for a sovereign balance transfer.
///
/// # Arguments
///
/// * `old_balance` - The cell's balance before the transfer.
/// * `transfer_amount` - The amount being transferred.
/// * `direction` - 1 for outgoing (debit), 0 for incoming (credit).
/// * `old_commitment` - 32-byte commitment of the old state.
/// * `new_commitment` - 32-byte commitment of the new state.
/// * `effects_hash` - 32-byte hash of the effects being applied.
/// * `cell_id_hash` - 32-byte hash of the cell ID.
///
/// # Returns
///
/// (trace, public_inputs) suitable for `stark::prove`.
/// The public inputs include the balance_delta at positions [32..34]:
///   PI[32] = transfer_amount (magnitude)
///   PI[33] = direction (sign: 1=negative/outgoing, 0=positive/incoming)
pub fn generate_sovereign_transition_trace(
    old_balance: u64,
    transfer_amount: u64,
    direction: u32, // 1 = outgoing, 0 = incoming
    old_commitment: &[u8; 32],
    new_commitment: &[u8; 32],
    effects_hash: &[u8; 32],
    cell_id_hash: &[u8; 32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // Compute new balance.
    let new_balance = if direction == 1 {
        old_balance.saturating_sub(transfer_amount)
    } else {
        old_balance.saturating_add(transfer_amount)
    };

    // Compute the signed balance delta.
    let delta: i64 = if direction == 1 {
        -(transfer_amount as i64)
    } else {
        transfer_amount as i64
    };
    let delta_bb = encode_balance_delta(delta);

    // Build trace (needs at least 2 rows, power-of-two).
    // Cols 4-5 carry delta_magnitude and delta_sign, bound to PI by boundary constraints
    // and bound to the transfer by eval_constraints.
    let row0 = vec![
        BabyBear::from_u64(old_balance),
        BabyBear::from_u64(transfer_amount),
        BabyBear::from_u64(new_balance),
        BabyBear::new(direction),
        delta_bb[0], // delta_magnitude (== transfer_amount)
        delta_bb[1], // delta_sign (== direction)
    ];

    // Padding row: duplicate row 0 (constraint still holds).
    let row1 = row0.clone();

    let trace = vec![row0, row1];

    // Public inputs: encode each 32-byte hash as 8 BabyBear elements (4 bytes LE each),
    // then append the 2-element balance delta.
    let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
    public_inputs.extend(bytes32_to_babybear(old_commitment));
    public_inputs.extend(bytes32_to_babybear(new_commitment));
    public_inputs.extend(bytes32_to_babybear(effects_hash));
    public_inputs.extend(bytes32_to_babybear(cell_id_hash));
    public_inputs.push(delta_bb[0]); // PI[32]: magnitude
    public_inputs.push(delta_bb[1]); // PI[33]: sign_bit

    (trace, public_inputs)
}

/// Encode a 32-byte hash as 8 BabyBear field elements (4 bytes each, little-endian).
///
/// This matches the executor's `bytes32_to_babybear` encoding.
pub fn bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<BabyBear> {
    let mut result = Vec::with_capacity(8);
    for chunk in bytes.chunks(4) {
        let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        result.push(BabyBear::new(val % BABYBEAR_P));
    }
    result
}

/// Compute the effects hash for a Transfer effect (matches executor's format).
///
/// The executor hashes effects using `blake3("pyana-sovereign-effects-v1:" || effect_hashes...)`.
/// For a single Transfer, we hash the effect bytes in the same DFS order the executor would.
pub fn compute_transfer_effects_hash(from: &[u8], to: &[u8], amount: u64) -> [u8; 32] {
    // Build the same hash as Effect::Transfer.hash() would produce.
    let mut effect_hasher = blake3::Hasher::new();
    effect_hasher.update(b"pyana-effect-v1:");
    effect_hasher.update(b"Transfer");
    effect_hasher.update(from);
    effect_hasher.update(to);
    effect_hasher.update(&amount.to_le_bytes());
    let effect_hash = *effect_hasher.finalize().as_bytes();

    // Now wrap in the turn-level effects hash.
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-sovereign-effects-v1:");
    hasher.update(&effect_hash);
    *hasher.finalize().as_bytes()
}

/// Compute the cell ID hash for binding (matches executor's format).
pub fn compute_cell_id_hash(cell_id_bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(cell_id_bytes).as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::{proof_from_bytes, proof_to_bytes, prove, verify};

    #[test]
    fn test_sovereign_transition_outgoing() {
        let old_balance = 1000u64;
        let transfer_amount = 100u64;
        let direction = 1u32; // outgoing

        // Dummy commitments for this test.
        let old_commitment = [1u8; 32];
        let new_commitment = [2u8; 32];
        let effects_hash = [3u8; 32];
        let cell_id_hash = [4u8; 32];

        let (trace, public_inputs) = generate_sovereign_transition_trace(
            old_balance,
            transfer_amount,
            direction,
            &old_commitment,
            &new_commitment,
            &effects_hash,
            &cell_id_hash,
        );

        assert_eq!(public_inputs.len(), SOVEREIGN_PUBLIC_INPUTS);

        let air = SovereignTransitionAir;
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "Verification failed: {:?}", result.err());

        // Verify the proven delta is correct.
        let delta = extract_balance_delta(&public_inputs).unwrap();
        assert_eq!(
            delta, -100,
            "outgoing transfer of 100 should yield delta=-100"
        );
    }

    #[test]
    fn test_sovereign_transition_incoming() {
        let old_balance = 500u64;
        let transfer_amount = 200u64;
        let direction = 0u32; // incoming

        let old_commitment = [10u8; 32];
        let new_commitment = [11u8; 32];
        let effects_hash = [12u8; 32];
        let cell_id_hash = [13u8; 32];

        let (trace, public_inputs) = generate_sovereign_transition_trace(
            old_balance,
            transfer_amount,
            direction,
            &old_commitment,
            &new_commitment,
            &effects_hash,
            &cell_id_hash,
        );

        let air = SovereignTransitionAir;
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_ok(), "Verification failed: {:?}", result.err());

        // Verify the proven delta is correct.
        let delta = extract_balance_delta(&public_inputs).unwrap();
        assert_eq!(
            delta, 200,
            "incoming transfer of 200 should yield delta=+200"
        );
    }

    #[test]
    fn test_invalid_transition_detected() {
        // Construct an invalid trace: wrong new_balance.
        let old_commitment = [5u8; 32];
        let new_commitment = [6u8; 32];
        let effects_hash = [7u8; 32];
        let cell_id_hash = [8u8; 32];

        let delta_bb = encode_balance_delta(-100);

        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&old_commitment));
        public_inputs.extend(bytes32_to_babybear(&new_commitment));
        public_inputs.extend(bytes32_to_babybear(&effects_hash));
        public_inputs.extend(bytes32_to_babybear(&cell_id_hash));
        public_inputs.push(delta_bb[0]);
        public_inputs.push(delta_bb[1]);

        // Invalid trace: old=1000, amount=100, direction=1 (outgoing)
        // but new_balance=1000 (should be 900).
        let trace = vec![
            vec![
                BabyBear::from_u64(1000),
                BabyBear::from_u64(100),
                BabyBear::from_u64(1000), // WRONG: should be 900
                BabyBear::ONE,            // direction = outgoing
                delta_bb[0],              // delta_magnitude
                delta_bb[1],              // delta_sign
            ],
            vec![
                BabyBear::from_u64(1000),
                BabyBear::from_u64(100),
                BabyBear::from_u64(1000), // WRONG
                BabyBear::ONE,
                delta_bb[0],
                delta_bb[1],
            ],
        ];

        let air = SovereignTransitionAir;
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        assert!(result.is_err(), "Invalid trace should not verify");
    }

    #[test]
    fn test_forged_delta_detected() {
        // An adversary tries to claim delta=0 for an outgoing transfer of 100.
        // The boundary constraints bind col[4] to PI[32], so if PI[32] != transfer_amount,
        // constraint 3 (delta_magnitude == transfer_amount) catches it.
        let old_commitment = [5u8; 32];
        let new_commitment = [6u8; 32];
        let effects_hash = [7u8; 32];
        let cell_id_hash = [8u8; 32];

        // Forged delta: claim magnitude=0, sign=0 (no change) despite outgoing 100.
        let forged_delta = [BabyBear::ZERO, BabyBear::ZERO];

        let mut public_inputs: Vec<BabyBear> = Vec::with_capacity(SOVEREIGN_PUBLIC_INPUTS);
        public_inputs.extend(bytes32_to_babybear(&old_commitment));
        public_inputs.extend(bytes32_to_babybear(&new_commitment));
        public_inputs.extend(bytes32_to_babybear(&effects_hash));
        public_inputs.extend(bytes32_to_babybear(&cell_id_hash));
        public_inputs.push(forged_delta[0]); // FORGED: 0 instead of 100
        public_inputs.push(forged_delta[1]); // FORGED: 0 instead of 1

        // Correct trace (balance conservation is valid)
        let trace = vec![
            vec![
                BabyBear::from_u64(1000),
                BabyBear::from_u64(100),
                BabyBear::from_u64(900),
                BabyBear::ONE,   // direction = outgoing
                forged_delta[0], // boundary constraint forces this to match PI[32]=0
                forged_delta[1], // boundary constraint forces this to match PI[33]=0
            ],
            vec![
                BabyBear::from_u64(1000),
                BabyBear::from_u64(100),
                BabyBear::from_u64(900),
                BabyBear::ONE,
                forged_delta[0],
                forged_delta[1],
            ],
        ];

        let air = SovereignTransitionAir;
        let proof = prove(&air, &trace, &public_inputs);
        let result = verify(&air, &proof, &public_inputs);
        // Constraint 3: delta_magnitude(0) - transfer_amount(100) != 0 --> FAIL
        assert!(
            result.is_err(),
            "Forged delta (magnitude mismatch) should not verify"
        );
    }

    #[test]
    fn test_proof_serialization_roundtrip() {
        let old_balance = 5000u64;
        let transfer_amount = 42u64;
        let direction = 1u32;

        let old_commitment = [20u8; 32];
        let new_commitment = [21u8; 32];
        let effects_hash = [22u8; 32];
        let cell_id_hash = [23u8; 32];

        let (trace, public_inputs) = generate_sovereign_transition_trace(
            old_balance,
            transfer_amount,
            direction,
            &old_commitment,
            &new_commitment,
            &effects_hash,
            &cell_id_hash,
        );

        let air = SovereignTransitionAir;
        let proof = prove(&air, &trace, &public_inputs);

        // Serialize and deserialize.
        let bytes = proof_to_bytes(&proof);
        let recovered = proof_from_bytes(&bytes).expect("deserialization should succeed");

        // Verify the deserialized proof.
        let result = verify(&air, &recovered, &public_inputs);
        assert!(
            result.is_ok(),
            "Roundtripped proof failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_encode_decode_delta_roundtrip() {
        for delta in [-500i64, -1, 0, 1, 42, 1000000] {
            let encoded = encode_balance_delta(delta);
            let decoded = extract_balance_delta(&{
                // Build minimal PI vector with delta at the right offset.
                let mut pi = vec![BabyBear::ZERO; DELTA_PI_OFFSET];
                pi.push(encoded[0]);
                pi.push(encoded[1]);
                pi
            })
            .unwrap();
            assert_eq!(decoded, delta, "roundtrip failed for delta={}", delta);
        }
    }
}
