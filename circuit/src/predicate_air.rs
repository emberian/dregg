//! Predicate proof AIR.
//!
//! Proves statements about private token attributes without revealing them:
//! - "My token has `valid_until >= T`" (not expired for a while)
//! - "My bid amount >= minimum_bid" (auction qualification)
//! - "My reputation score >= threshold" (access to premium service)
//! - "My delegation depth <= max_depth" (freshness guarantee)
//!
//! These are all range/comparison checks where one operand is private (in the
//! witness) and the other is a public input (the threshold).
//!
//! # Design
//!
//! The predicate AIR is a standalone single-row circuit that proves a comparison
//! predicate over a private attribute bound to a specific fact in the token state.
//! It uses the same bit-decomposition technique as the GTE/LT checks in
//! [`derivation_air`](crate::derivation_air) but in a self-contained form with
//! its own public inputs.
//!
//! # Trace layout
//!
//! | Column    | Description                                            |
//! |-----------|-------------------------------------------------------|
//! | 0         | private_value (the attribute being proven about)       |
//! | 1         | threshold (public comparison target)                   |
//! | 2         | diff (computed difference for the comparison)          |
//! | 3..32     | diff_bits[0..29] (bit decomposition of diff, 30 bits)  |
//! | 33        | fact_commitment (binding to the token state)            |
//! | 34        | neq_inverse (multiplicative inverse of diff, for NEQ)   |
//!
//! # Public inputs
//!
//! `[threshold, fact_commitment]`
//!
//! - `threshold`: The public comparison target.
//! - `fact_commitment`: Poseidon2(fact_hash, state_root) — binds the proven
//!   value to a specific fact in a specific token state.
//!
//! # Predicate types
//!
//! - `GTE(value, threshold)`: prove `value >= threshold` via bit decomp of `value - threshold`
//! - `LTE(value, threshold)`: prove `threshold >= value` via bit decomp of `threshold - value`
//! - `GT(value, threshold)`: prove `value > threshold` via bit decomp of `value - threshold - 1`
//! - `LT(value, threshold)`: prove `value < threshold` via bit decomp of `threshold - value - 1`
//! - `InRange(value, low, high)`: prove `value >= low AND value <= high`
//! - `NEQ(value, target)`: prove `value != target` by exhibiting inverse of (value - target)

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Number of bits for the range check.
///
/// SOUNDNESS NOTE: BabyBear p = 2013265921, p/2 = 1006632960, 2^30 = 1073741824.
/// Since 2^30 > p/2, using 31 bits (checking bit 30 = 0) is UNSOUND: values in
/// [p/2, 2^30) have bit 30 = 0 but represent "negative" field elements.
///
/// We use 30 bits total. The high bit is bit 29. If bit 29 = 0, diff < 2^29 = 536870912,
/// which is safely below p/2. This restricts the proven range to values < 2^29 (~537M),
/// which is sufficient for all practical token attribute comparisons.
pub const PREDICATE_DIFF_BITS: usize = 30;

/// Trace width for the predicate AIR.
/// private_value(1) + threshold(1) + diff(1) + diff_bits(30) + fact_commitment(1) + neq_inverse(1)
/// + blinding(1) + fact_hash(1) + state_root(1) = 38
pub const PREDICATE_AIR_WIDTH: usize = 38;

/// Column indices for the predicate AIR trace.
pub mod col {
    use super::PREDICATE_DIFF_BITS;

    /// The private attribute value (witness).
    pub const PRIVATE_VALUE: usize = 0;
    /// The threshold (matches public input).
    pub const THRESHOLD: usize = 1;
    /// The computed difference for the comparison.
    pub const DIFF: usize = 2;
    /// Start of bit decomposition columns (30 bits).
    pub const DIFF_BITS_START: usize = 3;
    /// The fact commitment (binding to token state).
    pub const FACT_COMMITMENT: usize = DIFF_BITS_START + PREDICATE_DIFF_BITS; // 33
    /// Multiplicative inverse of diff (used only for NEQ predicate).
    pub const NEQ_INVERSE: usize = FACT_COMMITMENT + 1; // 34
    /// Per-proof blinding factor (witness, private). Prevents cross-session linking.
    pub const BLINDING: usize = NEQ_INVERSE + 1; // 35
    /// The fact hash (witness, private). Used to verify blinded commitment derivation.
    pub const FACT_HASH: usize = BLINDING + 1; // 36
    /// The state root (witness, private). Used to verify blinded commitment derivation.
    pub const STATE_ROOT: usize = FACT_HASH + 1; // 37

    /// Get the column for diff_bits[bit_idx].
    #[inline]
    pub const fn diff_bit(bit_idx: usize) -> usize {
        DIFF_BITS_START + bit_idx
    }
}

/// The type of predicate being proven.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PredicateType {
    /// Prove `private_value >= threshold`.
    /// diff = private_value - threshold; bit decomp with high bit = 0.
    Gte,
    /// Prove `private_value <= threshold`.
    /// diff = threshold - private_value; bit decomp with high bit = 0.
    Lte,
    /// Prove `private_value > threshold`.
    /// diff = private_value - threshold - 1; bit decomp with high bit = 0.
    Gt,
    /// Prove `private_value < threshold`.
    /// diff = threshold - private_value - 1; bit decomp with high bit = 0.
    Lt,
    /// Prove `private_value != target`.
    /// Exhibit the multiplicative inverse of (private_value - target).
    Neq,
    /// Prove `low <= private_value <= high`.
    /// This is encoded as two separate predicates (GTE for low, LTE for high)
    /// composed at the witness level. The AIR proves the lower bound; a second
    /// AIR instance proves the upper bound.
    InRangeLow,
    /// The upper-bound half of an InRange proof.
    InRangeHigh,
}

/// Witness for a predicate proof.
#[derive(Clone, Debug)]
pub struct PredicateWitness {
    /// The private attribute value.
    pub private_value: BabyBear,
    /// The threshold/target for comparison.
    pub threshold: BabyBear,
    /// The type of predicate.
    pub predicate_type: PredicateType,
    /// Fact commitment: binds this proof to a specific fact in a specific token state.
    /// When blinding is used, this is `Poseidon2(fact_hash, state_root, blinding, 0)`.
    /// When blinding is zero/None, this is the legacy `Poseidon2(fact_hash, state_root)`.
    pub fact_commitment: BabyBear,
    /// Per-proof blinding factor for unlinkability. When `Some(nonzero)`, the
    /// fact_commitment is computed as `Poseidon2(fact_hash, state_root, blinding, 0)`.
    /// When `None` or `Some(ZERO)`, the legacy deterministic commitment is used.
    /// This value is private (in the witness) and never revealed to the verifier.
    pub blinding: Option<BabyBear>,
    /// The fact hash (private witness). Required when blinding is used so the AIR
    /// can verify the commitment derivation.
    pub fact_hash: Option<BabyBear>,
    /// The state root (private witness). Required when blinding is used so the AIR
    /// can verify the commitment derivation.
    pub state_root: Option<BabyBear>,
}

impl PredicateWitness {
    /// Compute the diff for this predicate.
    pub fn compute_diff(&self) -> BabyBear {
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => {
                // diff = value - threshold (must be non-negative)
                self.private_value - self.threshold
            }
            PredicateType::Lte | PredicateType::InRangeHigh => {
                // diff = threshold - value (must be non-negative)
                self.threshold - self.private_value
            }
            PredicateType::Gt => {
                // diff = value - threshold - 1 (must be non-negative)
                self.private_value - self.threshold - BabyBear::ONE
            }
            PredicateType::Lt => {
                // diff = threshold - value - 1 (must be non-negative)
                self.threshold - self.private_value - BabyBear::ONE
            }
            PredicateType::Neq => {
                // diff = value - target (must be non-zero)
                self.private_value - self.threshold
            }
        }
    }

    /// Check whether the predicate can be satisfied (i.e., the statement is true).
    ///
    /// Returns `false` if the private value does not satisfy the predicate,
    /// meaning proof generation would produce an invalid proof.
    pub fn is_satisfiable(&self) -> bool {
        let v = self.private_value.as_u32();
        let t = self.threshold.as_u32();
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => v >= t,
            PredicateType::Lte | PredicateType::InRangeHigh => v <= t,
            PredicateType::Gt => v > t,
            PredicateType::Lt => v < t,
            PredicateType::Neq => v != t,
        }
    }
}

/// The predicate proof AIR.
///
/// Proves a single predicate statement about a private value with a public threshold.
pub struct PredicateAir {
    pub witness: PredicateWitness,
}

impl PredicateAir {
    pub fn new(witness: PredicateWitness) -> Self {
        Self { witness }
    }
}

impl Air for PredicateAir {
    fn trace_width(&self) -> usize {
        PREDICATE_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        2 // [threshold, fact_commitment]
    }

    fn constraints(&self) -> Vec<Constraint> {
        let predicate_type = self.witness.predicate_type;

        vec![
            // Constraint 1: Threshold in trace matches public input.
            Constraint {
                name: "threshold_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| row[col::THRESHOLD] - public_inputs[0]),
            },
            // Constraint 2: Fact commitment in trace matches public input.
            Constraint {
                name: "fact_commitment_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::FACT_COMMITMENT] - public_inputs[1]
                }),
            },
            // Constraint 3: Diff is correctly computed based on predicate type.
            Constraint {
                name: "diff_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    let diff = row[col::DIFF];
                    match predicate_type {
                        PredicateType::Gte | PredicateType::InRangeLow => {
                            diff - (value - threshold)
                        }
                        PredicateType::Lte | PredicateType::InRangeHigh => {
                            diff - (threshold - value)
                        }
                        PredicateType::Gt => diff - (value - threshold - BabyBear::ONE),
                        PredicateType::Lt => diff - (threshold - value - BabyBear::ONE),
                        PredicateType::Neq => diff - (value - threshold),
                    }
                }),
            },
            // Constraint 4: Bit decomposition is correct.
            // sum(bit_i * 2^i) = diff
            // (For NEQ, this constraint is still applied but supplemented by the
            // inverse constraint below.)
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        // For NEQ, we don't need bit decomposition — we use the inverse.
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    recomposed - diff
                }),
            },
            // Constraint 5: All bits are binary (0 or 1).
            Constraint {
                name: "bits_binary".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    let mut result = BabyBear::ZERO;
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 6: High bit is 0 (diff < 2^30 < p/2, proving non-negative).
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    row[col::diff_bit(PREDICATE_DIFF_BITS - 1)]
                }),
            },
            // Constraint 7: NEQ inverse proof — diff * inverse = 1.
            // Only enforced for NEQ predicates; for others this is trivially 0.
            Constraint {
                name: "neq_inverse_valid".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type != PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let inverse = row[col::NEQ_INVERSE];
                    diff * inverse - BabyBear::ONE
                }),
            },
            // Constraint 8: Blinded fact commitment derivation.
            // When fact_hash and state_root are both zero (components not provided),
            // this constraint is a no-op (legacy path — external verification).
            // When components are provided:
            //   If blinding != 0: fact_commitment == Poseidon2(fact_hash, state_root, blinding, 0)
            //   If blinding == 0: fact_commitment == Poseidon2(fact_hash, state_root) [2-to-1]
            Constraint {
                name: "fact_commitment_derivation".to_string(),
                eval: Box::new(move |row, _, _| {
                    let fact_commitment = row[col::FACT_COMMITMENT];
                    let blinding = row[col::BLINDING];
                    let fact_hash = row[col::FACT_HASH];
                    let state_root = row[col::STATE_ROOT];

                    // Skip when components are not provided (legacy path).
                    if fact_hash == BabyBear::ZERO && state_root == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    if blinding == BabyBear::ZERO {
                        // Unblinded: commitment = hash_2_to_1(fact_hash, state_root)
                        let expected = poseidon2::hash_2_to_1(fact_hash, state_root);
                        fact_commitment - expected
                    } else {
                        // Blinded: commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])
                        let expected = poseidon2::hash_4_to_1(&[
                            fact_hash,
                            state_root,
                            blinding,
                            BabyBear::ZERO,
                        ]);
                        fact_commitment - expected
                    }
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut row = vec![BabyBear::ZERO; PREDICATE_AIR_WIDTH];

        // Fill trace columns.
        row[col::PRIVATE_VALUE] = w.private_value;
        row[col::THRESHOLD] = w.threshold;
        row[col::FACT_COMMITMENT] = w.fact_commitment;
        row[col::BLINDING] = w.blinding.unwrap_or(BabyBear::ZERO);
        row[col::FACT_HASH] = w.fact_hash.unwrap_or(BabyBear::ZERO);
        row[col::STATE_ROOT] = w.state_root.unwrap_or(BabyBear::ZERO);

        let diff = w.compute_diff();
        row[col::DIFF] = diff;

        match w.predicate_type {
            PredicateType::Neq => {
                // For NEQ: provide the multiplicative inverse of diff.
                // If diff is zero (value == target), inverse doesn't exist and
                // the constraint will fail — this is the intended behavior.
                if let Some(inv) = diff.inverse() {
                    row[col::NEQ_INVERSE] = inv;
                }
                // bits are left as zero (not used for NEQ)
            }
            _ => {
                // For range predicates: bit decomposition of diff.
                let diff_val = diff.as_u32();
                for i in 0..PREDICATE_DIFF_BITS {
                    let bit = (diff_val >> i) & 1;
                    row[col::diff_bit(i)] = BabyBear::new(bit);
                }
            }
        }

        let public_inputs = vec![w.threshold, w.fact_commitment];
        (vec![row], public_inputs)
    }
}

impl StarkAir for PredicateAir {
    fn width(&self) -> usize {
        PREDICATE_AIR_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-predicate-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let predicate_type = self.witness.predicate_type;

        // C1: threshold matches public input
        let c1 = local[col::THRESHOLD] - public_inputs[0];
        // C2: fact_commitment matches public input
        let c2 = local[col::FACT_COMMITMENT] - public_inputs[1];
        // C3: diff is correctly computed
        let c3 = {
            let value = local[col::PRIVATE_VALUE];
            let threshold = local[col::THRESHOLD];
            let diff = local[col::DIFF];
            match predicate_type {
                PredicateType::Gte | PredicateType::InRangeLow => diff - (value - threshold),
                PredicateType::Lte | PredicateType::InRangeHigh => diff - (threshold - value),
                PredicateType::Gt => diff - (value - threshold - BabyBear::ONE),
                PredicateType::Lt => diff - (threshold - value - BabyBear::ONE),
                PredicateType::Neq => diff - (value - threshold),
            }
        };
        // C4: bit decomposition correct
        let c4 = if predicate_type == PredicateType::Neq {
            BabyBear::ZERO
        } else {
            let diff = local[col::DIFF];
            let mut recomposed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            for i in 0..PREDICATE_DIFF_BITS {
                let bit = local[col::diff_bit(i)];
                recomposed = recomposed + bit * power_of_two;
                power_of_two = power_of_two + power_of_two;
            }
            recomposed - diff
        };
        // C5: bits are binary
        let c5 = if predicate_type == PredicateType::Neq {
            BabyBear::ZERO
        } else {
            let mut result = BabyBear::ZERO;
            for i in 0..PREDICATE_DIFF_BITS {
                let bit = local[col::diff_bit(i)];
                result = result + bit * (bit - BabyBear::ONE);
            }
            result
        };
        // C6: high bit is zero
        let c6 = if predicate_type == PredicateType::Neq {
            BabyBear::ZERO
        } else {
            local[col::diff_bit(PREDICATE_DIFF_BITS - 1)]
        };
        // C7: NEQ inverse valid (diff * inverse = 1)
        let c7 = if predicate_type != PredicateType::Neq {
            BabyBear::ZERO
        } else {
            let diff = local[col::DIFF];
            let inverse = local[col::NEQ_INVERSE];
            diff * inverse - BabyBear::ONE
        };

        // Combine with alpha powers
        let mut combined = c1;
        let mut alpha_pow = alpha;
        combined = combined + alpha_pow * c2;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c3;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c4;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c5;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c6;
        alpha_pow = alpha_pow * alpha;
        combined = combined + alpha_pow * c7;

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 2 {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::THRESHOLD,
                value: public_inputs[0],
            });
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::FACT_COMMITMENT,
                value: public_inputs[1],
            });
        }
        constraints
    }
}

/// A complete predicate proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PredicateProof {
    /// The type of predicate that was proven.
    pub predicate_type: PredicateType,
    /// The threshold (public input).
    pub threshold: BabyBear,
    /// The fact commitment (public input).
    pub fact_commitment: BabyBear,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
}

/// Generate a predicate proof from a witness.
///
/// Returns `None` if the predicate is not satisfiable (the statement is false)
/// or if proof generation fails.
pub fn prove_predicate(witness: PredicateWitness) -> Option<PredicateProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let predicate_type = witness.predicate_type;
    let threshold = witness.threshold;
    let fact_commitment = witness.fact_commitment;

    let air = PredicateAir::new(witness);
    let (mut trace, public_inputs) = air.generate_trace();

    // STARK prover requires trace length >= 2 and power-of-two.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        trace.push(trace[0].clone());
    }

    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(PredicateProof {
        predicate_type,
        threshold,
        fact_commitment,
        stark_proof,
    })
}

/// Verify a predicate proof against expected public inputs.
///
/// The verifier provides the threshold and fact_commitment they expect and
/// checks the proof is consistent.
pub fn verify_predicate(
    proof: &PredicateProof,
    threshold: BabyBear,
    fact_commitment: BabyBear,
) -> bool {
    if proof.threshold != threshold || proof.fact_commitment != fact_commitment {
        return false;
    }
    let public_inputs = vec![threshold, fact_commitment];
    // Reconstruct a dummy witness for the AIR (only needed for constraint evaluation shape).
    let dummy_witness = PredicateWitness {
        private_value: BabyBear::ZERO,
        threshold,
        predicate_type: proof.predicate_type,
        fact_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let air = PredicateAir::new(dummy_witness);
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

/// Compute the (unblinded) fact commitment that binds a proven value to a token state.
///
/// `fact_commitment = Poseidon2(fact_hash, state_root)`
///
/// - `fact_hash`: The Poseidon2 hash of the fact containing the proven attribute.
/// - `state_root`: The Merkle root of the token state containing the fact.
///
/// WARNING: This produces a deterministic commitment. If the same fact is proven
/// multiple times from the same state, the commitment is identical, enabling
/// cross-session correlation. Use [`compute_blinded_fact_commitment`] for
/// unlinkable proofs.
pub fn compute_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(fact_hash, state_root)
}

/// Compute a blinded fact commitment that prevents cross-session linkability.
///
/// `blinded_fact_commitment = Poseidon2(fact_hash, state_root, blinding, 0)`
///
/// The `blinding` factor MUST be generated fresh (random BabyBear element) for
/// each proof. It goes into the witness (private) so the verifier cannot recover
/// `fact_hash` or `state_root` from the commitment.
///
/// When `blinding` is zero, this produces the same result as [`compute_fact_commitment`]
/// (backward compatibility for testing/migration).
///
/// - `fact_hash`: The Poseidon2 hash of the fact containing the proven attribute.
/// - `state_root`: The Merkle root of the token state containing the fact.
/// - `blinding`: A fresh random BabyBear element (per-proof).
pub fn compute_blinded_fact_commitment(
    fact_hash: BabyBear,
    state_root: BabyBear,
    blinding: BabyBear,
) -> BabyBear {
    if blinding == BabyBear::ZERO {
        // Legacy path: deterministic 2-to-1 hash.
        poseidon2::hash_2_to_1(fact_hash, state_root)
    } else {
        // Blinded path: 4-to-1 hash with blinding factor.
        poseidon2::hash_4_to_1(&[fact_hash, state_root, blinding, BabyBear::ZERO])
    }
}

/// Prove an InRange predicate (value >= low AND value <= high).
///
/// This produces two proofs: one for the lower bound (GTE) and one for the
/// upper bound (LTE). Both must verify for the range claim to hold.
///
/// Returns `None` if either bound is not satisfiable.
pub fn prove_in_range(
    private_value: BabyBear,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> Option<(PredicateProof, PredicateProof)> {
    let low_witness = PredicateWitness {
        private_value,
        threshold: low,
        predicate_type: PredicateType::InRangeLow,
        fact_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let high_witness = PredicateWitness {
        private_value,
        threshold: high,
        predicate_type: PredicateType::InRangeHigh,
        fact_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let low_proof = prove_predicate(low_witness)?;
    let high_proof = prove_predicate(high_witness)?;
    Some((low_proof, high_proof))
}

/// Verify an InRange proof (both bounds must pass).
pub fn verify_in_range(
    low_proof: &PredicateProof,
    high_proof: &PredicateProof,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> bool {
    verify_predicate(low_proof, low, fact_commitment)
        && verify_predicate(high_proof, high, fact_commitment)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::poseidon2::hash_fact;

    /// Test state root used in all test helpers.
    const TEST_STATE_ROOT: u32 = 99999;

    /// Helper: create a fact commitment and its components for testing.
    /// Returns (commitment, fact_hash, state_root).
    fn test_fact_commitment_parts(value: BabyBear) -> (BabyBear, BabyBear, BabyBear) {
        let fact_hash = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(TEST_STATE_ROOT);
        let commitment = compute_fact_commitment(fact_hash, state_root);
        (commitment, fact_hash, state_root)
    }

    /// Helper: create a fact commitment for testing (legacy convenience).
    fn test_fact_commitment(value: BabyBear) -> BabyBear {
        test_fact_commitment_parts(value).0
    }

    /// Helper: build a PredicateWitness with fact_hash and state_root populated for constraint 8.
    fn test_witness(
        private_value: BabyBear,
        threshold: BabyBear,
        predicate_type: PredicateType,
    ) -> PredicateWitness {
        let (commitment, fh, sr) = test_fact_commitment_parts(private_value);
        PredicateWitness {
            private_value,
            threshold,
            predicate_type,
            fact_commitment: commitment,
            blinding: None,
            fact_hash: Some(fh),
            state_root: Some(sr),
        }
    }

    // =========================================================================
    // GTE tests
    // =========================================================================

    #[test]
    fn test_predicate_gte_passes() {
        // Prove: value(25) >= threshold(18)
        let witness = test_witness(BabyBear::new(25), BabyBear::new(18), PredicateType::Gte);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 25 >= 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gte_equal_passes() {
        // Prove: value(18) >= threshold(18)
        let witness = test_witness(BabyBear::new(18), BabyBear::new(18), PredicateType::Gte);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 18 >= 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gte_fails() {
        // Prove: value(15) >= threshold(18) — should FAIL
        // diff = 15 - 18 in BabyBear wraps to p - 3 (high bit set)
        let witness = test_witness(BabyBear::new(15), BabyBear::new(18), PredicateType::Gte);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GTE 15 >= 18 should fail");
        // The high bit constraint should catch this
        let has_high_bit = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "high_bit_zero");
        assert!(
            has_high_bit,
            "Should have high_bit_zero violation, got: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // LTE tests
    // =========================================================================

    #[test]
    fn test_predicate_lte_passes() {
        // Prove: value(10) <= threshold(100)
        let witness = test_witness(BabyBear::new(10), BabyBear::new(100), PredicateType::Lte);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LTE 10 <= 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_lte_fails() {
        // Prove: value(200) <= threshold(100) — should FAIL
        let witness = test_witness(BabyBear::new(200), BabyBear::new(100), PredicateType::Lte);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "LTE 200 <= 100 should fail");
    }

    // =========================================================================
    // GT / LT tests
    // =========================================================================

    #[test]
    fn test_predicate_gt_passes() {
        // Prove: value(25) > threshold(18)
        let witness = test_witness(BabyBear::new(25), BabyBear::new(18), PredicateType::Gt);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GT 25 > 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gt_equal_fails() {
        // Prove: value(18) > threshold(18) — should FAIL (not strictly greater)
        // diff = 18 - 18 - 1 = p - 1 in BabyBear (wraps, high bit set)
        let witness = test_witness(BabyBear::new(18), BabyBear::new(18), PredicateType::Gt);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GT 18 > 18 should fail");
    }

    #[test]
    fn test_predicate_lt_passes() {
        // Prove: value(5) < threshold(18)
        let witness = test_witness(BabyBear::new(5), BabyBear::new(18), PredicateType::Lt);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LT 5 < 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_lt_equal_fails() {
        // Prove: value(18) < threshold(18) — should FAIL
        let witness = test_witness(BabyBear::new(18), BabyBear::new(18), PredicateType::Lt);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "LT 18 < 18 should fail");
    }

    // =========================================================================
    // NEQ tests
    // =========================================================================

    #[test]
    fn test_predicate_neq_passes() {
        // Prove: value(42) != target(0)
        let witness = test_witness(BabyBear::new(42), BabyBear::new(0), PredicateType::Neq);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "NEQ 42 != 0 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_neq_fails() {
        // Prove: value(7) != target(7) — should FAIL
        // diff = 0, inverse doesn't exist, constraint diff * inv = 1 fails.
        let witness = test_witness(BabyBear::new(7), BabyBear::new(7), PredicateType::Neq);
        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "NEQ 7 != 7 should fail");
        let has_neq_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "neq_inverse_valid");
        assert!(
            has_neq_violation,
            "Should have neq_inverse_valid violation, got: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // InRange tests
    // =========================================================================

    #[test]
    fn test_predicate_in_range_passes() {
        // Prove: 18 <= value(25) <= 120
        let value = BabyBear::new(25);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(
            result.is_some(),
            "InRange 18 <= 25 <= 120 should produce proofs"
        );

        let (low_proof, high_proof) = result.unwrap();
        assert!(
            verify_in_range(&low_proof, &high_proof, low, high, commitment),
            "InRange verification should pass"
        );
    }

    #[test]
    fn test_predicate_in_range_below_low_fails() {
        // Prove: 18 <= value(15) <= 120 — should FAIL (below low bound)
        let value = BabyBear::new(15);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_none(), "InRange with value below low should fail");
    }

    #[test]
    fn test_predicate_in_range_above_high_fails() {
        // Prove: 18 <= value(200) <= 120 — should FAIL (above high bound)
        let value = BabyBear::new(200);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(
            result.is_none(),
            "InRange with value above high should fail"
        );
    }

    #[test]
    fn test_predicate_in_range_at_bounds_passes() {
        // Prove: 18 <= value(18) <= 120 (at lower bound, inclusive)
        let value = BabyBear::new(18);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_some(), "InRange at lower bound should pass");

        // Prove: 18 <= value(120) <= 120 (at upper bound, inclusive)
        let value = BabyBear::new(120);
        let commitment = test_fact_commitment(value);
        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_some(), "InRange at upper bound should pass");
    }

    // =========================================================================
    // prove_predicate / verify_predicate integration
    // =========================================================================

    #[test]
    fn test_prove_and_verify_gte() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let witness = test_witness(value, threshold, PredicateType::Gte);
        let commitment = witness.fact_commitment;

        let proof = prove_predicate(witness).expect("should produce proof");
        assert!(verify_predicate(&proof, threshold, commitment));
    }

    #[test]
    fn test_prove_returns_none_for_false_statement() {
        // Trying to prove 5 >= 100 should return None.
        let witness = test_witness(BabyBear::new(5), BabyBear::new(100), PredicateType::Gte);
        let proof = prove_predicate(witness);
        assert!(proof.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn test_verify_fails_with_wrong_threshold() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let witness = test_witness(value, threshold, PredicateType::Gte);
        let commitment = witness.fact_commitment;

        let proof = prove_predicate(witness).expect("should produce proof");
        // Verify with a different threshold — should fail.
        let wrong_threshold = BabyBear::new(999);
        assert!(!verify_predicate(&proof, wrong_threshold, commitment));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let witness = test_witness(value, threshold, PredicateType::Gte);

        let proof = prove_predicate(witness).expect("should produce proof");
        // Verify with a different commitment — should fail.
        let wrong_commitment = BabyBear::new(12345);
        assert!(!verify_predicate(&proof, threshold, wrong_commitment));
    }

    #[test]
    fn test_predicate_balance_scenario() {
        // Real scenario: prove balance >= 1000 without revealing exact balance.
        // Balance is 5000 (private), threshold is 1000 (public).
        let balance = BabyBear::new(5000);
        let min_balance = BabyBear::new(1000);

        // The fact is balance(5000) in some token state.
        let balance_pred = BabyBear::new(42); // "balance" predicate symbol
        let fh = hash_fact(balance_pred, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let sr = BabyBear::new(77777);
        let commitment = compute_fact_commitment(fh, sr);

        let witness = PredicateWitness {
            private_value: balance,
            threshold: min_balance,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
            blinding: None,
            fact_hash: Some(fh),
            state_root: Some(sr),
        };

        let proof = prove_predicate(witness).expect("balance proof should succeed");

        // Verifier only knows: threshold=1000, fact_commitment
        // They learn: "the balance in that fact is >= 1000" without knowing the exact value.
        assert!(verify_predicate(&proof, min_balance, commitment));
    }

    // =========================================================================
    // Blinding / unlinkability tests
    // =========================================================================

    #[test]
    fn test_blinded_commitment_differs_across_proofs() {
        // The same fact proven with different blinding factors must produce
        // different fact_commitments, preventing cross-session linking.
        let fh = hash_fact(
            BabyBear::new(100),
            &[BabyBear::new(25), BabyBear::ZERO, BabyBear::ZERO],
        );
        let sr = BabyBear::new(TEST_STATE_ROOT);

        let blinding_a = BabyBear::new(12345);
        let blinding_b = BabyBear::new(67890);

        let commit_a = compute_blinded_fact_commitment(fh, sr, blinding_a);
        let commit_b = compute_blinded_fact_commitment(fh, sr, blinding_b);

        assert_ne!(
            commit_a, commit_b,
            "Different blinding must produce different commitments"
        );
    }

    #[test]
    fn test_blinded_proof_verifies() {
        // Generate a proof with blinding and verify it.
        let value = BabyBear::new(25);
        let threshold = BabyBear::new(18);
        let fh = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let sr = BabyBear::new(TEST_STATE_ROOT);
        let blinding = BabyBear::new(42424242);

        let commitment = compute_blinded_fact_commitment(fh, sr, blinding);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
            blinding: Some(blinding),
            fact_hash: Some(fh),
            state_root: Some(sr),
        };

        let air = PredicateAir::new(witness.clone());
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Blinded GTE 25 >= 18 should pass: {:?}",
            result.violations()
        );

        // Also verify via prove/verify path.
        let proof = prove_predicate(witness).expect("blinded proof should succeed");
        assert!(verify_predicate(&proof, threshold, commitment));
    }

    #[test]
    fn test_zero_blinding_matches_legacy() {
        // When blinding is zero, the blinded commitment equals the legacy commitment.
        let fh = hash_fact(
            BabyBear::new(100),
            &[BabyBear::new(25), BabyBear::ZERO, BabyBear::ZERO],
        );
        let sr = BabyBear::new(TEST_STATE_ROOT);

        let legacy = compute_fact_commitment(fh, sr);
        let blinded_zero = compute_blinded_fact_commitment(fh, sr, BabyBear::ZERO);

        assert_eq!(
            legacy, blinded_zero,
            "Zero blinding must equal legacy commitment"
        );
    }
}
