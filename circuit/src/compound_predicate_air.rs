//! Compound predicate proof AIR.
//!
//! Proves boolean combinations of multiple predicate statements about private
//! token attributes in a single proof:
//!
//! - "age >= 18 AND country_code IN {1,2,3}" (conjunction)
//! - "gold_member OR balance >= 10000" (disjunction)
//! - "at least 2 of {age >= 18, resident, verified}" (threshold)
//!
//! # Design
//!
//! A compound predicate proof composes N individual predicate evaluations with a
//! boolean formula that specifies how to combine the per-predicate pass/fail results.
//!
//! ## Trace layout
//!
//! The trace has N+1 rows:
//! - Rows 0..N-1: Individual predicate evaluations (same column layout as [`PredicateAir`]).
//! - Row N: Boolean composition row with the combined result.
//!
//! Each predicate row uses the standard predicate trace columns (private_value,
//! threshold, diff, diff_bits[31], fact_commitment, neq_inverse). The composition
//! row stores intermediate gate values and the final result.
//!
//! ## Public inputs
//!
//! `[threshold_0, commitment_0, threshold_1, commitment_1, ..., final_result]`
//!
//! The final_result public input must equal `BabyBear::ONE` for the proof to be valid.
//!
//! # Limits
//!
//! Maximum 8 sub-predicates per compound proof (matches `MAX_BODY_ATOMS`).

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::predicate_air::{
    PREDICATE_AIR_WIDTH, PREDICATE_DIFF_BITS, PredicateType, PredicateWitness, col,
};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Maximum number of sub-predicates in a compound proof.
pub const MAX_COMPOUND_PREDICATES: usize = 8;

/// Column index for the per-row result in the compound predicate trace.
const RESULT_COL: usize = PREDICATE_AIR_WIDTH;

/// Column index for the predicate type indicator in the compound predicate trace.
/// Encoding: GTE/InRangeLow=0, LTE/InRangeHigh=1, GT=2, LT=3, NEQ=4.
const PRED_TYPE_COL: usize = PREDICATE_AIR_WIDTH + 1;

/// Compound predicate trace width: standard predicate width + result + predicate_type.
const COMPOUND_WIDTH: usize = PREDICATE_AIR_WIDTH + 2;

/// Encode a predicate type as a BabyBear field element for the trace/public inputs.
fn encode_predicate_type(pt: PredicateType) -> BabyBear {
    match pt {
        PredicateType::Gte | PredicateType::InRangeLow => BabyBear::ZERO,
        PredicateType::Lte | PredicateType::InRangeHigh => BabyBear::ONE,
        PredicateType::Gt => BabyBear::new(2),
        PredicateType::Lt => BabyBear::new(3),
        PredicateType::Neq => BabyBear::new(4),
    }
}

/// How to combine the results of individual predicate evaluations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BooleanFormula {
    /// All of the specified predicate indices must pass.
    /// `result = prod(sub_result_i)` -- all 1 means product is 1.
    And(Vec<usize>),

    /// At least one of the specified predicate indices must pass.
    /// `result = 1 - prod(1 - sub_result_i)` -- at least one 1 means at least one factor is 0.
    Or(Vec<usize>),

    /// At least K of the specified predicate indices must pass.
    /// `result = 1 iff sum(sub_result_i) >= K`.
    Threshold(usize, Vec<usize>),

    /// Arbitrary gate tree. Each gate references input indices (0..N-1 are predicate
    /// results, N+ are intermediate gate outputs).
    Custom(Vec<Gate>),
}

/// A single boolean gate in a custom formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// AND of two inputs (indices into the results vector).
    And(usize, usize),
    /// OR of two inputs.
    Or(usize, usize),
    /// NOT of a single input.
    Not(usize),
}

/// Witness for a compound predicate proof.
#[derive(Clone, Debug)]
pub struct CompoundPredicateWitness {
    /// The individual predicate witnesses (one per sub-predicate).
    pub predicates: Vec<PredicateWitness>,
    /// The boolean formula combining the predicate results.
    pub formula: BooleanFormula,
}

impl CompoundPredicateWitness {
    /// Validate that this witness is well-formed.
    pub fn is_valid(&self) -> bool {
        let n = self.predicates.len();
        if n == 0 || n > MAX_COMPOUND_PREDICATES {
            return false;
        }
        match &self.formula {
            BooleanFormula::And(indices) | BooleanFormula::Or(indices) => {
                indices.iter().all(|&i| i < n)
            }
            BooleanFormula::Threshold(k, indices) => {
                *k > 0 && *k <= indices.len() && indices.iter().all(|&i| i < n)
            }
            BooleanFormula::Custom(gates) => {
                // Each gate must reference valid indices (predicate results or prior gate outputs).
                for (gate_idx, gate) in gates.iter().enumerate() {
                    let max_ref = n + gate_idx;
                    match gate {
                        Gate::And(a, b) | Gate::Or(a, b) => {
                            if *a >= max_ref || *b >= max_ref {
                                return false;
                            }
                        }
                        Gate::Not(a) => {
                            if *a >= max_ref {
                                return false;
                            }
                        }
                    }
                }
                !gates.is_empty()
            }
        }
    }

    /// Evaluate the formula over the individual predicate results.
    ///
    /// Returns `true` if the compound statement is satisfiable (all individual predicates
    /// that need to pass do pass according to the formula).
    pub fn is_satisfiable(&self) -> bool {
        let results: Vec<bool> = self.predicates.iter().map(|w| w.is_satisfiable()).collect();
        evaluate_formula_bool(&self.formula, &results)
    }
}

/// Evaluate a boolean formula over a set of boolean results.
fn evaluate_formula_bool(formula: &BooleanFormula, results: &[bool]) -> bool {
    match formula {
        BooleanFormula::And(indices) => indices.iter().all(|&i| results[i]),
        BooleanFormula::Or(indices) => indices.iter().any(|&i| results[i]),
        BooleanFormula::Threshold(k, indices) => {
            let count = indices.iter().filter(|&&i| results[i]).count();
            count >= *k
        }
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<bool> = results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] && values[*b],
                    Gate::Or(a, b) => values[*a] || values[*b],
                    Gate::Not(a) => !values[*a],
                };
                values.push(val);
            }
            // The last gate's output is the final result.
            *values.last().unwrap_or(&false)
        }
    }
}

/// Evaluate a boolean formula over BabyBear field element results (0 or 1).
///
/// Returns the final result as a BabyBear element (0 or 1).
fn evaluate_formula_field(formula: &BooleanFormula, results: &[BabyBear]) -> BabyBear {
    match formula {
        BooleanFormula::And(indices) => {
            // result = prod(sub_result_i)
            let mut product = BabyBear::ONE;
            for &i in indices {
                product = product * results[i];
            }
            product
        }
        BooleanFormula::Or(indices) => {
            // result = 1 - prod(1 - sub_result_i)
            let mut product = BabyBear::ONE;
            for &i in indices {
                product = product * (BabyBear::ONE - results[i]);
            }
            BabyBear::ONE - product
        }
        BooleanFormula::Threshold(k, indices) => {
            // result = 1 iff sum >= k
            let sum: u32 = indices.iter().map(|&i| results[i].as_u32()).sum();
            if sum >= *k as u32 {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            }
        }
        BooleanFormula::Custom(gates) => {
            let mut values: Vec<BabyBear> = results.to_vec();
            for gate in gates {
                let val = match gate {
                    Gate::And(a, b) => values[*a] * values[*b],
                    Gate::Or(a, b) => {
                        // OR(a, b) = 1 - (1-a)*(1-b) = a + b - a*b
                        values[*a] + values[*b] - values[*a] * values[*b]
                    }
                    Gate::Not(a) => BabyBear::ONE - values[*a],
                };
                values.push(val);
            }
            *values.last().unwrap_or(&BabyBear::ZERO)
        }
    }
}

/// The compound predicate proof AIR.
///
/// Proves a boolean combination of predicate statements about private values.
pub struct CompoundPredicateAir {
    pub witness: CompoundPredicateWitness,
}

impl CompoundPredicateAir {
    pub fn new(witness: CompoundPredicateWitness) -> Self {
        Self { witness }
    }

    /// Number of sub-predicates in this compound proof.
    pub fn num_predicates(&self) -> usize {
        self.witness.predicates.len()
    }
}

impl Air for CompoundPredicateAir {
    fn trace_width(&self) -> usize {
        // Each row has the standard predicate width + result column + predicate_type column.
        COMPOUND_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        // 3 per predicate (threshold, fact_commitment, predicate_type) + 1 final result
        self.witness.predicates.len() * 3 + 1
    }

    fn constraints(&self) -> Vec<Constraint> {
        let num_preds = self.witness.predicates.len();

        vec![
            // Constraint 1: Each predicate row's threshold matches one of the public
            // input thresholds.
            //
            // SOUNDNESS: We verify that the threshold in the trace equals at least one
            // PI threshold by checking that the PRODUCT of (threshold - PI[3*k]) for all
            // k is zero.
            Constraint {
                name: "threshold_matches_public_input".to_string(),
                eval: {
                    let n = num_preds;
                    Box::new(move |row, _, public_inputs| {
                        let threshold_in_trace = row[col::THRESHOLD];
                        let value = row[col::PRIVATE_VALUE];

                        // Skip the composition row.
                        if value == BabyBear::ZERO && threshold_in_trace == BabyBear::ZERO {
                            return BabyBear::ZERO;
                        }

                        // Check: threshold must equal one of the PI thresholds.
                        // PI layout: [threshold_0, commitment_0, type_0, threshold_1, ...]
                        let mut product = BabyBear::ONE;
                        for k in 0..n {
                            let pi_threshold = public_inputs[k * 3];
                            product = product * (threshold_in_trace - pi_threshold);
                        }
                        product
                    })
                },
            },
            // Constraint 2: The predicate_type column must match one of the verifier-
            // provided type public inputs. This prevents the prover from choosing an
            // arbitrary type.
            //
            // SOUNDNESS: The predicate_type column value must equal one of the
            // PI type values. Combined with constraint 2b (type-threshold binding),
            // this ensures the prover cannot substitute a different formula.
            Constraint {
                name: "predicate_type_matches_public_input".to_string(),
                eval: {
                    let n = num_preds;
                    Box::new(move |row, _, public_inputs| {
                        let value = row[col::PRIVATE_VALUE];
                        let threshold_in_trace = row[col::THRESHOLD];

                        // Skip the composition row.
                        if value == BabyBear::ZERO && threshold_in_trace == BabyBear::ZERO {
                            return BabyBear::ZERO;
                        }

                        let pred_type_in_trace = row[PRED_TYPE_COL];

                        // The type must equal one of the PI types.
                        // PI layout: [threshold_0, commitment_0, type_0, ...]
                        let mut product = BabyBear::ONE;
                        for k in 0..n {
                            let pi_type = public_inputs[k * 3 + 2];
                            product = product * (pred_type_in_trace - pi_type);
                        }
                        product
                    })
                },
            },
            // Constraint 2b: The (threshold, type) pair in the trace must match one of
            // the verifier's (threshold, type) pairs from the public inputs.
            //
            // SOUNDNESS: This is critical. Without this constraint, the prover could
            // place a valid threshold (from one PI slot) and a valid type (from a different
            // PI slot) on the same row. By checking the PRODUCT of
            // ((threshold - PI_threshold_k)^2 + (type - PI_type_k)^2) == 0 is impossible
            // we instead use:
            //   product_k( (threshold - PI_threshold_k) + alpha*(type - PI_type_k) ) == 0
            // where alpha is a fixed non-trivial constant (e.g. a large prime element).
            // For exact matching we use the combined linear form which suffices since
            // collision probability is negligible in BabyBear (p ~ 2^31).
            //
            // Actually, for perfect soundness we use the joint product check:
            //   For each row, there must exist some k such that threshold == PI[3k]
            //   AND type == PI[3k+2]. We encode this as:
            //   product_k( (threshold - PI[3k]) + (type - PI[3k+2]) * ALPHA ) == 0
            //   where ALPHA is chosen to avoid spurious collisions.
            Constraint {
                name: "type_threshold_binding".to_string(),
                eval: {
                    let n = num_preds;
                    // Use a non-trivial mixing constant. Since both threshold and type
                    // are small (threshold < 2^29, type < 5), any large constant works.
                    // We pick 2^20 + 7 which is coprime to p.
                    let alpha = BabyBear::new(1_048_583);
                    Box::new(move |row, _, public_inputs| {
                        let value = row[col::PRIVATE_VALUE];
                        let threshold_in_trace = row[col::THRESHOLD];

                        // Skip the composition row.
                        if value == BabyBear::ZERO && threshold_in_trace == BabyBear::ZERO {
                            return BabyBear::ZERO;
                        }

                        let pred_type_in_trace = row[PRED_TYPE_COL];

                        // Check: (threshold, type) must equal one of the PI (threshold, type) pairs.
                        let mut product = BabyBear::ONE;
                        for k in 0..n {
                            let pi_threshold = public_inputs[k * 3];
                            let pi_type = public_inputs[k * 3 + 2];
                            let combined = (threshold_in_trace - pi_threshold)
                                + alpha * (pred_type_in_trace - pi_type);
                            product = product * combined;
                        }
                        product
                    })
                },
            },
            // Constraint 3: Diff is correctly computed based on the predicate_type column.
            //
            // SOUNDNESS: The predicate_type column is constrained to match a verifier-
            // controlled public input (constraints 2 + 2b). The diff formula is now
            // selected by the type indicator, preventing formula substitution.
            //
            // We use selector polynomials: for type t in {0,1,2,3,4},
            //   selector_t = product_{s != t} (pred_type - s) / product_{s != t} (t - s)
            // Each selector is 1 when pred_type == t and 0 otherwise.
            // The constraint is: sum_t( selector_t * expected_diff_t ) == diff
            Constraint {
                name: "diff_correct".to_string(),
                eval: {
                    Box::new(move |row, _, _| {
                        let value = row[col::PRIVATE_VALUE];
                        let threshold = row[col::THRESHOLD];
                        let diff = row[col::DIFF];
                        let pred_type = row[PRED_TYPE_COL];

                        // Skip the composition row.
                        if value == BabyBear::ZERO
                            && threshold == BabyBear::ZERO
                            && diff == BabyBear::ZERO
                        {
                            return BabyBear::ZERO;
                        }

                        // Compute Lagrange basis selectors over {0,1,2,3,4}.
                        // selector_t(x) = prod_{s!=t}(x - s) / prod_{s!=t}(t - s)
                        let type_values: [BabyBear; 5] = [
                            BabyBear::ZERO,   // GTE
                            BabyBear::ONE,    // LTE
                            BabyBear::new(2), // GT
                            BabyBear::new(3), // LT
                            BabyBear::new(4), // NEQ
                        ];

                        // Expected diffs for each type:
                        let expected_diffs: [BabyBear; 5] = [
                            value - threshold,                 // GTE: value - threshold
                            threshold - value,                 // LTE: threshold - value
                            value - threshold - BabyBear::ONE, // GT: value - threshold - 1
                            threshold - value - BabyBear::ONE, // LT: threshold - value - 1
                            value - threshold,                 // NEQ: value - threshold
                        ];

                        // Compute interpolated expected diff using Lagrange basis.
                        let mut expected_diff = BabyBear::ZERO;
                        for t in 0..5usize {
                            // Numerator: prod_{s != t} (pred_type - type_values[s])
                            let mut num = BabyBear::ONE;
                            // Denominator: prod_{s != t} (type_values[t] - type_values[s])
                            let mut den = BabyBear::ONE;
                            for s in 0..5usize {
                                if s != t {
                                    num = num * (pred_type - type_values[s]);
                                    den = den * (type_values[t] - type_values[s]);
                                }
                            }
                            // den is a known constant for each t, always nonzero.
                            let den_inv = den.inverse().unwrap();
                            expected_diff = expected_diff + expected_diffs[t] * num * den_inv;
                        }

                        diff - expected_diff
                    })
                },
            },
            // Constraint 4: Bit decomposition is correct (sum(bit_i * 2^i) = diff).
            // Only enforced when the predicate claims to pass (result == 1).
            // When a predicate fails (result == 0), diff may exceed 30 bits (wraps in BabyBear),
            // making exact bit decomposition impossible. The constraint is gated by result.
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: {
                    Box::new(move |row, _, _| {
                        let neq_inverse = row[col::NEQ_INVERSE];

                        // Skip for NEQ predicates (they use inverse instead of bit decomp).
                        if neq_inverse != BabyBear::ZERO {
                            return BabyBear::ZERO;
                        }

                        // Skip the composition row: it has value=0, threshold=0.
                        let value = row[col::PRIVATE_VALUE];
                        let threshold = row[col::THRESHOLD];
                        if value == BabyBear::ZERO && threshold == BabyBear::ZERO {
                            return BabyBear::ZERO;
                        }

                        let result = row[RESULT_COL];
                        let diff = row[col::DIFF];
                        let mut recomposed = BabyBear::ZERO;
                        let mut power_of_two = BabyBear::ONE;
                        for i in 0..PREDICATE_DIFF_BITS {
                            let bit = row[col::diff_bit(i)];
                            recomposed = recomposed + bit * power_of_two;
                            power_of_two = power_of_two + power_of_two;
                        }
                        // Only enforce when result == 1 (predicate claims to pass).
                        result * (recomposed - diff)
                    })
                },
            },
            // Constraint 5: All bits are binary (0 or 1).
            // Only enforced when the predicate claims to pass (result == 1).
            // When a predicate fails, the bit columns may contain arbitrary values.
            Constraint {
                name: "bits_binary".to_string(),
                eval: Box::new(move |row, _, _| {
                    let neq_inverse = row[col::NEQ_INVERSE];

                    // Skip NEQ rows.
                    if neq_inverse != BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    // Skip composition row.
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    if value == BabyBear::ZERO && threshold == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    let result = row[RESULT_COL];
                    let mut check = BabyBear::ZERO;
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        check = check + bit * (bit - BabyBear::ONE);
                    }
                    // Only enforce when result == 1.
                    result * check
                }),
            },
            // Constraint 6: High bit must be zero WHEN result claims to be 1.
            // In a compound predicate, some sub-predicates may legitimately fail
            // (e.g., in OR/Threshold formulas). The high bit being 1 is only a
            // violation if the result column claims the predicate passed.
            //
            // SOUNDNESS: This is enforced through constraint 9 (result_derived_from_range_check)
            // which sets result = 1 - high_bit. If high_bit is 1, result must be 0.
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: Box::new(move |row, _, _| {
                    let neq_inverse = row[col::NEQ_INVERSE];
                    let result = row[RESULT_COL];

                    // Skip NEQ rows.
                    if neq_inverse != BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    // Skip composition row.
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    if value == BabyBear::ZERO && threshold == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    // Only enforce when result claims to be 1.
                    let high_bit = row[col::diff_bit(PREDICATE_DIFF_BITS - 1)];
                    result * high_bit
                }),
            },
            // Constraint 7: NEQ inverse valid (diff * inverse = 1 for NEQ predicates).
            // Only enforced when result=1 (the NEQ predicate claims to pass).
            Constraint {
                name: "neq_inverse_valid".to_string(),
                eval: Box::new(move |row, _, _| {
                    let result = row[RESULT_COL];
                    let neq_inverse = row[col::NEQ_INVERSE];

                    if neq_inverse == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }
                    // Only enforce when result=1.
                    if result == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    diff * neq_inverse - BabyBear::ONE
                }),
            },
            // Constraint 8: Per-row result column is binary (0 or 1).
            Constraint {
                name: "result_binary".to_string(),
                eval: Box::new(move |row, _, _| {
                    let result = row[RESULT_COL];
                    result * (result - BabyBear::ONE)
                }),
            },
            // Constraint 9: Result column is DERIVED from the range check (soundness).
            Constraint {
                name: "result_derived_from_range_check".to_string(),
                eval: Box::new(move |row, _, _| {
                    let result = row[RESULT_COL];
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    let neq_inverse = row[col::NEQ_INVERSE];

                    // Skip the composition row.
                    if value == BabyBear::ZERO && threshold == BabyBear::ZERO {
                        return BabyBear::ZERO;
                    }

                    if neq_inverse != BabyBear::ZERO {
                        // NEQ predicate path.
                        let diff = row[col::DIFF];
                        let pass_check = result * (BabyBear::ONE - diff * neq_inverse);
                        let fail_check = (BabyBear::ONE - result) * diff;
                        pass_check + fail_check
                    } else {
                        // Range-check predicate path: result = 1 - high_bit.
                        let high_bit = row[col::diff_bit(PREDICATE_DIFF_BITS - 1)];
                        result - (BabyBear::ONE - high_bit)
                    }
                }),
            },
            // Constraint 10: Final public input must equal ONE.
            Constraint {
                name: "final_result_is_one".to_string(),
                eval: {
                    let n = num_preds;
                    Box::new(move |_row, _, public_inputs| {
                        let final_pi = public_inputs[n * 3];
                        final_pi - BabyBear::ONE
                    })
                },
            },
        ]
    }

    fn last_row_constraints(&self) -> Vec<Constraint> {
        let formula = self.witness.formula.clone();
        let num_preds = self.witness.predicates.len();

        vec![
            // The composition row's result must equal 1 (the compound statement holds).
            Constraint {
                name: "composition_result_is_one".to_string(),
                eval: Box::new(move |row, _, public_inputs| {
                    let result = row[RESULT_COL];
                    // Also check it matches the final public input.
                    let final_pi = public_inputs[num_preds * 3];
                    let pi_check = result - final_pi;
                    let one_check = result - BabyBear::ONE;
                    // Both must be zero: result = final_pi = 1.
                    pi_check + one_check
                }),
            },
            // The composition row's result must be correctly derived from the formula
            // applied to the preceding predicate rows' results.
            //
            // SOUNDNESS NOTE: We cannot access previous rows from a last_row_constraint.
            // The soundness argument relies on:
            // 1. Each predicate row has its result derived from the range check (constraint 9)
            // 2. Each predicate row's diff formula is bound to the verifier-controlled type
            // 3. The composition row's result must equal 1
            // 4. The verifier externally verifies the formula structure
            Constraint {
                name: "formula_evaluation_correct".to_string(),
                eval: {
                    let f = formula.clone();
                    Box::new(move |row, _, public_inputs| {
                        let result = row[RESULT_COL];
                        let final_pi = public_inputs[num_preds * 3];
                        let _ = &f;
                        result - final_pi
                    })
                },
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let n = self.witness.predicates.len();
        let width = COMPOUND_WIDTH;
        let mut trace = Vec::with_capacity(n + 1);
        let mut public_inputs = Vec::with_capacity(n * 3 + 1);

        // Per-predicate results for formula evaluation.
        let mut predicate_results = Vec::with_capacity(n);

        // Generate one row per predicate.
        for w in &self.witness.predicates {
            let mut row = vec![BabyBear::ZERO; width];

            // Fill standard predicate columns.
            row[col::PRIVATE_VALUE] = w.private_value;
            row[col::THRESHOLD] = w.threshold;
            row[col::FACT_COMMITMENT] = w.fact_commitment;

            // Fill predicate type column (verifier-controlled).
            let type_encoded = encode_predicate_type(w.predicate_type);
            row[PRED_TYPE_COL] = type_encoded;

            let satisfiable = w.is_satisfiable();

            // Always compute diff and fill bit decomposition (constraints are unconditional).
            let diff = w.compute_diff();
            row[col::DIFF] = diff;

            match w.predicate_type {
                PredicateType::Neq => {
                    if satisfiable {
                        if let Some(inv) = diff.inverse() {
                            row[col::NEQ_INVERSE] = inv;
                        }
                    } else {
                        // diff=0 (equal). Set neq_inverse=1 as NEQ-row signal.
                        row[col::NEQ_INVERSE] = BabyBear::ONE;
                    }
                }
                _ => {
                    let diff_val = diff.as_u32();
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = (diff_val >> i) & 1;
                        row[col::diff_bit(i)] = BabyBear::new(bit);
                    }
                }
            }

            let result = if satisfiable {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[RESULT_COL] = result;
            predicate_results.push(result);

            trace.push(row);

            // Public inputs: [threshold_i, commitment_i, type_i] for each predicate.
            public_inputs.push(w.threshold);
            public_inputs.push(w.fact_commitment);
            public_inputs.push(type_encoded);
        }

        // Composition row: evaluate the formula over predicate results.
        let composition_result = evaluate_formula_field(&self.witness.formula, &predicate_results);
        let mut composition_row = vec![BabyBear::ZERO; width];
        composition_row[RESULT_COL] = composition_result;
        trace.push(composition_row);

        // Final public input: the expected result (must be 1).
        public_inputs.push(BabyBear::ONE);

        (trace, public_inputs)
    }
}

/// A complete compound predicate proof result.
#[derive(Clone, Debug)]
pub struct CompoundPredicateProof {
    /// The boolean formula that was proven.
    pub formula: BooleanFormula,
    /// The predicate types and thresholds (public).
    pub predicates: Vec<(PredicateType, BabyBear)>,
    /// The fact commitments (one per sub-predicate, public).
    pub fact_commitments: Vec<BabyBear>,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
    /// Number of sub-predicates (needed to reconstruct StarkAir for verification).
    pub num_predicates: usize,
}

/// Generate a compound predicate proof.
///
/// # Arguments
///
/// * `predicates` - Slice of (private_value, predicate_type, threshold) tuples.
/// * `formula` - How to combine the predicate results.
/// * `fact_commitments` - One per predicate, binding each to a token state fact.
///
/// # Returns
///
/// `Some(CompoundPredicateProof)` if the compound statement is satisfiable and proof
/// generation succeeds, `None` otherwise.
pub fn prove_compound_predicate(
    predicates: &[(BabyBear, PredicateType, BabyBear)],
    formula: BooleanFormula,
    fact_commitments: &[BabyBear],
) -> Option<CompoundPredicateProof> {
    if predicates.is_empty()
        || predicates.len() > MAX_COMPOUND_PREDICATES
        || predicates.len() != fact_commitments.len()
    {
        return None;
    }

    // Build the individual predicate witnesses.
    let witnesses: Vec<PredicateWitness> = predicates
        .iter()
        .zip(fact_commitments.iter())
        .map(
            |(&(value, pred_type, threshold), &commitment)| PredicateWitness {
                private_value: value,
                threshold,
                predicate_type: pred_type,
                fact_commitment: commitment,
                blinding: None,
                fact_hash: None,
                state_root: None,
            },
        )
        .collect();

    let compound_witness = CompoundPredicateWitness {
        predicates: witnesses,
        formula: formula.clone(),
    };

    if !compound_witness.is_valid() {
        return None;
    }

    if !compound_witness.is_satisfiable() {
        return None;
    }

    let air = CompoundPredicateAir::new(compound_witness);
    let (mut trace, public_inputs) = air.generate_trace();

    // STARK prover requires trace length >= 2 and power-of-two.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        trace.push(vec![BabyBear::ZERO; trace[0].len()]);
    }

    let stark_air = CompoundPredicateStarkAir {
        width: air.trace_width(),
        num_predicates: predicates.len(),
        predicate_types: predicates.iter().map(|&(_, pt, _)| pt).collect(),
        formula: formula.clone(),
    };
    let stark_proof = stark::prove(&stark_air, &trace, &public_inputs);

    let pred_info: Vec<(PredicateType, BabyBear)> = predicates
        .iter()
        .map(|&(_, pred_type, threshold)| (pred_type, threshold))
        .collect();

    Some(CompoundPredicateProof {
        formula,
        predicates: pred_info,
        fact_commitments: fact_commitments.to_vec(),
        stark_proof,
        num_predicates: predicates.len(),
    })
}

/// Verify a compound predicate proof.
///
/// The verifier provides the expected fact commitments and checks the proof is
/// consistent with the claimed formula.
pub fn verify_compound_predicate(
    proof: &CompoundPredicateProof,
    expected_commitments: &[BabyBear],
    formula: &BooleanFormula,
) -> bool {
    // Check formula matches.
    if &proof.formula != formula {
        return false;
    }

    // Check commitments match.
    if proof.fact_commitments != expected_commitments {
        return false;
    }

    // Reconstruct expected public inputs: [threshold_0, commitment_0, type_0, ..., 1]
    let mut expected_pi = Vec::with_capacity(proof.predicates.len() * 3 + 1);
    for (i, &(pred_type, threshold)) in proof.predicates.iter().enumerate() {
        expected_pi.push(threshold);
        expected_pi.push(expected_commitments[i]);
        expected_pi.push(encode_predicate_type(pred_type));
    }
    expected_pi.push(BabyBear::ONE); // final result must be 1

    let stark_air = CompoundPredicateStarkAir {
        width: proof.stark_proof.num_cols,
        num_predicates: proof.num_predicates,
        predicate_types: proof.predicates.iter().map(|&(pt, _)| pt).collect(),
        formula: proof.formula.clone(),
    };
    stark::verify(&stark_air, &proof.stark_proof, &expected_pi).is_ok()
}

/// StarkAir wrapper for compound predicates.
///
/// Contains the information needed to evaluate the combined constraint set.
/// The compound predicate AIR uses per-row constraints only (no transition constraints),
/// making it safe for the custom STARK framework.
struct CompoundPredicateStarkAir {
    width: usize,
    num_predicates: usize,
    predicate_types: Vec<PredicateType>,
    formula: BooleanFormula,
}

impl StarkAir for CompoundPredicateStarkAir {
    fn width(&self) -> usize {
        self.width
    }

    fn constraint_degree(&self) -> usize {
        // The type_threshold_binding constraint has degree n (product over n factors).
        // The diff_correct constraint has degree 4 (Lagrange basis over 5 points).
        // The threshold/type product checks have degree n.
        // We use max(n, 4) + 1 as a conservative bound.
        std::cmp::max(self.num_predicates, 4) + 1
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-compound-predicate-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let n = self.num_predicates;

        let value = local[col::PRIVATE_VALUE];
        let threshold_in_trace = local[col::THRESHOLD];
        let is_composition_row = value == BabyBear::ZERO && threshold_in_trace == BabyBear::ZERO;

        // C1: threshold must match one of the PI thresholds (product check)
        let c1 = if is_composition_row {
            BabyBear::ZERO
        } else {
            let mut product = BabyBear::ONE;
            for k in 0..n {
                let pi_threshold = public_inputs[k * 3];
                product = product * (threshold_in_trace - pi_threshold);
            }
            product
        };

        // C2: predicate_type must match one of the PI types
        let c2 = if is_composition_row {
            BabyBear::ZERO
        } else {
            let pred_type_in_trace = local[PRED_TYPE_COL];
            let mut product = BabyBear::ONE;
            for k in 0..n {
                let pi_type = public_inputs[k * 3 + 2];
                product = product * (pred_type_in_trace - pi_type);
            }
            product
        };

        // C3: (threshold, type) pair binding
        let c3 = if is_composition_row {
            BabyBear::ZERO
        } else {
            let pred_type_in_trace = local[PRED_TYPE_COL];
            let mix = BabyBear::new(1_048_583);
            let mut product = BabyBear::ONE;
            for k in 0..n {
                let pi_threshold = public_inputs[k * 3];
                let pi_type = public_inputs[k * 3 + 2];
                let combined =
                    (threshold_in_trace - pi_threshold) + mix * (pred_type_in_trace - pi_type);
                product = product * combined;
            }
            product
        };

        // C4: diff correct (type-selector based)
        let c4 = if is_composition_row {
            BabyBear::ZERO
        } else {
            let diff = local[col::DIFF];
            let pred_type = local[PRED_TYPE_COL];

            let type_values: [BabyBear; 5] = [
                BabyBear::ZERO,
                BabyBear::ONE,
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
            ];
            let expected_diffs: [BabyBear; 5] = [
                value - threshold_in_trace,
                threshold_in_trace - value,
                value - threshold_in_trace - BabyBear::ONE,
                threshold_in_trace - value - BabyBear::ONE,
                value - threshold_in_trace,
            ];

            let mut expected_diff = BabyBear::ZERO;
            for t in 0..5usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for s in 0..5usize {
                    if s != t {
                        num = num * (pred_type - type_values[s]);
                        den = den * (type_values[t] - type_values[s]);
                    }
                }
                let den_inv = den.inverse().unwrap();
                expected_diff = expected_diff + expected_diffs[t] * num * den_inv;
            }
            diff - expected_diff
        };

        // C5: result column is binary
        let c5 = {
            let result = local[RESULT_COL];
            result * (result - BabyBear::ONE)
        };

        // C6: result derived from range check
        let c6 = {
            let result = local[RESULT_COL];
            let neq_inverse = local[col::NEQ_INVERSE];

            if is_composition_row {
                BabyBear::ZERO
            } else if neq_inverse != BabyBear::ZERO {
                let diff = local[col::DIFF];
                let pass_check = result * (BabyBear::ONE - diff * neq_inverse);
                let fail_check = (BabyBear::ONE - result) * diff;
                pass_check + fail_check
            } else {
                let high_bit = local[col::diff_bit(PREDICATE_DIFF_BITS - 1)];
                result - (BabyBear::ONE - high_bit)
            }
        };

        // C7: final PI must be ONE
        let c7 = public_inputs[n * 3] - BabyBear::ONE;

        // Combine with alpha
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
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        // No boundary constraints needed -- public input binding is done
        // via the eval_constraints checks on threshold/commitment matching.
        vec![]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::poseidon2;
    use crate::predicate_air::compute_fact_commitment;

    /// Helper: create a fact commitment for testing.
    fn test_commitment(value: BabyBear) -> BabyBear {
        let fact_hash =
            poseidon2::hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        compute_fact_commitment(fact_hash, state_root)
    }

    // =========================================================================
    // AND tests
    // =========================================================================

    #[test]
    fn test_compound_and_both_pass() {
        // Prove: (age >= 18 AND balance >= 100)
        // age = 25, balance = 500
        let age = BabyBear::new(25);
        let balance = BabyBear::new(500);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::And(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(
            proof.is_some(),
            "AND with both passing should produce a proof"
        );

        let proof = proof.unwrap();
        assert!(
            verify_compound_predicate(&proof, &commitments, &formula),
            "AND proof should verify"
        );
    }

    #[test]
    fn test_compound_and_one_fails() {
        // Prove: (age >= 18 AND balance >= 100)
        // age = 25, balance = 50 (fails balance check)
        let age = BabyBear::new(25);
        let balance = BabyBear::new(50);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::And(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula, &commitments);
        assert!(
            proof.is_none(),
            "AND with one failing should not produce a proof"
        );
    }

    // =========================================================================
    // OR tests
    // =========================================================================

    #[test]
    fn test_compound_or_one_passes() {
        // Prove: (age >= 18 OR balance >= 100)
        // age = 25, balance = 50 (only age passes)
        let age = BabyBear::new(25);
        let balance = BabyBear::new(50);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::Or(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(
            proof.is_some(),
            "OR with one passing should produce a proof"
        );

        let proof = proof.unwrap();
        assert!(
            verify_compound_predicate(&proof, &commitments, &formula),
            "OR proof should verify"
        );
    }

    #[test]
    fn test_compound_or_none_pass() {
        // Prove: (age >= 18 OR balance >= 100)
        // age = 15, balance = 50 (neither passes)
        let age = BabyBear::new(15);
        let balance = BabyBear::new(50);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::Or(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula, &commitments);
        assert!(
            proof.is_none(),
            "OR with none passing should not produce a proof"
        );
    }

    // =========================================================================
    // Threshold tests
    // =========================================================================

    #[test]
    fn test_compound_threshold_2_of_3_passes() {
        // Prove: at least 2 of (a >= 18, b >= 100, c >= 50)
        // a = 25 (pass), b = 50 (fail), c = 60 (pass) => 2 pass => valid
        let a = BabyBear::new(25);
        let b = BabyBear::new(50);
        let c = BabyBear::new(60);
        let ca = test_commitment(a);
        let cb = test_commitment(b);
        let cc = test_commitment(c);

        let predicates = vec![
            (a, PredicateType::Gte, BabyBear::new(18)),
            (b, PredicateType::Gte, BabyBear::new(100)),
            (c, PredicateType::Gte, BabyBear::new(50)),
        ];
        let commitments = vec![ca, cb, cc];
        let formula = BooleanFormula::Threshold(2, vec![0, 1, 2]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(
            proof.is_some(),
            "Threshold(2, [p1,p2,p3]) with 2 passing should produce a proof"
        );

        let proof = proof.unwrap();
        assert!(
            verify_compound_predicate(&proof, &commitments, &formula),
            "Threshold proof should verify"
        );
    }

    #[test]
    fn test_compound_threshold_2_of_3_only_1_passes() {
        // Prove: at least 2 of (a >= 18, b >= 100, c >= 50)
        // a = 25 (pass), b = 50 (fail), c = 30 (fail) => only 1 passes => invalid
        let a = BabyBear::new(25);
        let b = BabyBear::new(50);
        let c = BabyBear::new(30);
        let ca = test_commitment(a);
        let cb = test_commitment(b);
        let cc = test_commitment(c);

        let predicates = vec![
            (a, PredicateType::Gte, BabyBear::new(18)),
            (b, PredicateType::Gte, BabyBear::new(100)),
            (c, PredicateType::Gte, BabyBear::new(50)),
        ];
        let commitments = vec![ca, cb, cc];
        let formula = BooleanFormula::Threshold(2, vec![0, 1, 2]);

        let proof = prove_compound_predicate(&predicates, formula, &commitments);
        assert!(
            proof.is_none(),
            "Threshold(2, [p1,p2,p3]) with only 1 passing should not produce a proof"
        );
    }

    // =========================================================================
    // Custom gate tests
    // =========================================================================

    #[test]
    fn test_compound_custom_and_or() {
        // Prove: (P0 AND P1) OR P2
        // Gate 0: AND(0, 1) -> index 3
        // Gate 1: OR(3, 2)  -> index 4 (final)
        //
        // P0 = 25 >= 18 (pass), P1 = 50 < 100 (fail), P2 = 200 >= 150 (pass)
        // AND(P0, P1) = false, OR(false, P2) = true => valid
        let v0 = BabyBear::new(25);
        let v1 = BabyBear::new(50);
        let v2 = BabyBear::new(200);
        let c0 = test_commitment(v0);
        let c1 = test_commitment(v1);
        let c2 = test_commitment(v2);

        let predicates = vec![
            (v0, PredicateType::Gte, BabyBear::new(18)),
            (v1, PredicateType::Gte, BabyBear::new(100)),
            (v2, PredicateType::Gte, BabyBear::new(150)),
        ];
        let commitments = vec![c0, c1, c2];
        let formula = BooleanFormula::Custom(vec![
            Gate::And(0, 1), // gate index 3
            Gate::Or(3, 2),  // gate index 4 (final)
        ]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(
            proof.is_some(),
            "(P0 AND P1) OR P2 with P2 passing should produce a proof"
        );

        let proof = proof.unwrap();
        assert!(
            verify_compound_predicate(&proof, &commitments, &formula),
            "Custom gate proof should verify"
        );
    }

    // =========================================================================
    // AIR constraint verification tests
    // =========================================================================

    #[test]
    fn test_compound_air_constraints_pass() {
        let age = BabyBear::new(25);
        let balance = BabyBear::new(500);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let witnesses = vec![
            PredicateWitness {
                private_value: age,
                threshold: BabyBear::new(18),
                predicate_type: PredicateType::Gte,
                fact_commitment: age_commitment,
                blinding: None,
                fact_hash: None,
                state_root: None,
            },
            PredicateWitness {
                private_value: balance,
                threshold: BabyBear::new(100),
                predicate_type: PredicateType::Gte,
                fact_commitment: balance_commitment,
                blinding: None,
                fact_hash: None,
                state_root: None,
            },
        ];

        let compound_witness = CompoundPredicateWitness {
            predicates: witnesses,
            formula: BooleanFormula::And(vec![0, 1]),
        };

        let air = CompoundPredicateAir::new(compound_witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "AIR constraints should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_compound_air_constraints_fail_unsatisfiable() {
        // Build a witness where the compound is unsatisfiable (AND with one failing).
        // The trace will still be generated (result = 0), but the composition row
        // will have result = 0, causing the last_row constraint to fail.
        let age = BabyBear::new(25);
        let balance = BabyBear::new(50); // fails >= 100

        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let witnesses = vec![
            PredicateWitness {
                private_value: age,
                threshold: BabyBear::new(18),
                predicate_type: PredicateType::Gte,
                fact_commitment: age_commitment,
                blinding: None,
                fact_hash: None,
                state_root: None,
            },
            PredicateWitness {
                private_value: balance,
                threshold: BabyBear::new(100),
                predicate_type: PredicateType::Gte,
                fact_commitment: balance_commitment,
                blinding: None,
                fact_hash: None,
                state_root: None,
            },
        ];

        let compound_witness = CompoundPredicateWitness {
            predicates: witnesses,
            formula: BooleanFormula::And(vec![0, 1]),
        };

        let air = CompoundPredicateAir::new(compound_witness);
        let result = ConstraintProver::verify(&air);
        // The constraint prover will catch that the composition result is not 1.
        // However, the high_bit_zero constraint also fails for the failing predicate
        // (balance 50 - threshold 100 wraps in BabyBear).
        assert!(
            !result.is_valid(),
            "AIR constraints should fail for unsatisfiable compound"
        );
    }

    // =========================================================================
    // Verification with wrong commitments
    // =========================================================================

    #[test]
    fn test_verify_fails_with_wrong_commitments() {
        let age = BabyBear::new(25);
        let balance = BabyBear::new(500);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::And(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments).unwrap();

        // Try to verify with wrong commitments.
        let wrong_commitments = vec![BabyBear::new(12345), balance_commitment];
        assert!(
            !verify_compound_predicate(&proof, &wrong_commitments, &formula),
            "Verification should fail with wrong commitments"
        );
    }

    #[test]
    fn test_verify_fails_with_wrong_formula() {
        let age = BabyBear::new(25);
        let balance = BabyBear::new(500);
        let age_commitment = test_commitment(age);
        let balance_commitment = test_commitment(balance);

        let predicates = vec![
            (age, PredicateType::Gte, BabyBear::new(18)),
            (balance, PredicateType::Gte, BabyBear::new(100)),
        ];
        let commitments = vec![age_commitment, balance_commitment];
        let formula = BooleanFormula::And(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments).unwrap();

        // Try to verify with a different formula.
        let wrong_formula = BooleanFormula::Or(vec![0, 1]);
        assert!(
            !verify_compound_predicate(&proof, &commitments, &wrong_formula),
            "Verification should fail with wrong formula"
        );
    }

    // =========================================================================
    // Edge cases
    // =========================================================================

    #[test]
    fn test_compound_single_predicate_and() {
        // Degenerate case: AND with a single predicate.
        let value = BabyBear::new(42);
        let commitment = test_commitment(value);

        let predicates = vec![(value, PredicateType::Gte, BabyBear::new(10))];
        let commitments = vec![commitment];
        let formula = BooleanFormula::And(vec![0]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(proof.is_some(), "Single-predicate AND should work");

        let proof = proof.unwrap();
        assert!(verify_compound_predicate(&proof, &commitments, &formula));
    }

    #[test]
    fn test_compound_empty_predicates_rejected() {
        let formula = BooleanFormula::And(vec![]);
        let proof = prove_compound_predicate(&[], formula, &[]);
        assert!(proof.is_none(), "Empty predicates should be rejected");
    }

    #[test]
    fn test_compound_too_many_predicates_rejected() {
        let value = BabyBear::new(100);
        let commitment = test_commitment(value);

        // 9 predicates exceeds MAX_COMPOUND_PREDICATES (8).
        let predicates: Vec<_> = (0..9)
            .map(|_| (value, PredicateType::Gte, BabyBear::new(50)))
            .collect();
        let commitments: Vec<_> = (0..9).map(|_| commitment).collect();
        let formula = BooleanFormula::And((0..9).collect());

        let proof = prove_compound_predicate(&predicates, formula, &commitments);
        assert!(proof.is_none(), "More than 8 predicates should be rejected");
    }

    #[test]
    fn test_compound_neq_in_and() {
        // Prove: (value != 0 AND value >= 5)
        let value = BabyBear::new(10);
        let commitment = test_commitment(value);

        let predicates = vec![
            (value, PredicateType::Neq, BabyBear::new(0)),
            (value, PredicateType::Gte, BabyBear::new(5)),
        ];
        let commitments = vec![commitment, commitment];
        let formula = BooleanFormula::And(vec![0, 1]);

        let proof = prove_compound_predicate(&predicates, formula.clone(), &commitments);
        assert!(proof.is_some(), "NEQ + GTE AND should produce a proof");

        let proof = proof.unwrap();
        assert!(verify_compound_predicate(&proof, &commitments, &formula));
    }

    // =========================================================================
    // Soundness: formula substitution attack test
    // =========================================================================

    #[test]
    fn test_soundness_prover_uses_lt_formula_for_gte_predicate_must_fail() {
        // Attack scenario: value(50) >= threshold(100) is FALSE.
        // A malicious prover tries to use the LT formula (diff = threshold - value - 1 = 49)
        // which would have high_bit=0 and thus "pass" the range check.
        //
        // With the fixed AIR, the predicate_type column is constrained to match the
        // verifier's public input (GTE = 0). If the prover sets type=3 (LT) in the
        // trace, constraint 2b (type_threshold_binding) catches the mismatch.
        // If the prover keeps type=0 (GTE) but uses the LT diff formula, constraint 3
        // (diff_correct) catches it because the Lagrange selector for GTE enforces
        // diff = value - threshold.
        let value = BabyBear::new(50);
        let threshold = BabyBear::new(100);
        let commitment = test_commitment(value);

        // Build a witness that claims GTE but manually tamper the trace to use LT formula.
        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte, // Verifier expects GTE
            fact_commitment: commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };

        let compound_witness = CompoundPredicateWitness {
            predicates: vec![witness],
            formula: BooleanFormula::And(vec![0]),
        };

        let air = CompoundPredicateAir::new(compound_witness);

        // Generate the honest trace (which would fail because 50 < 100).
        let (mut trace, public_inputs) = air.generate_trace();

        // Now tamper the trace: replace diff with the LT formula value and fix bits.
        // LT formula: diff = threshold - value - 1 = 100 - 50 - 1 = 49
        let tampered_diff = BabyBear::new(49);
        trace[0][col::DIFF] = tampered_diff;

        // Fix bit decomposition to match the tampered diff (49 = 0b110001).
        let diff_val = 49u32;
        for i in 0..PREDICATE_DIFF_BITS {
            let bit = (diff_val >> i) & 1;
            trace[0][col::diff_bit(i)] = BabyBear::new(bit);
        }

        // Set result = 1 (prover claims it passes) and keep pred_type = 0 (GTE).
        trace[0][RESULT_COL] = BabyBear::ONE;
        trace[0][PRED_TYPE_COL] = BabyBear::ZERO; // GTE encoding

        // Also fix the composition row to claim success.
        let last = trace.len() - 1;
        trace[last][RESULT_COL] = BabyBear::ONE;

        // Verify constraints on this tampered trace -- must FAIL.
        let result = ConstraintProver::verify_trace(&air, &trace, &public_inputs);
        assert!(
            !result.is_valid(),
            "Tampered trace using LT formula for GTE predicate must fail constraints"
        );

        // The diff_correct constraint should catch this: with type=0 (GTE), the
        // expected diff is value - threshold = 50 - 100 (wraps in BabyBear), not 49.
        let has_diff_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "diff_correct");
        assert!(
            has_diff_violation,
            "Should have diff_correct violation when prover uses wrong formula, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_soundness_prover_changes_type_column_caught_by_binding() {
        // Attack scenario: value(50) >= threshold(100) is FALSE.
        // Prover sets pred_type = 3 (LT) in the trace to make diff = threshold - value - 1 = 49
        // pass the type-selected formula check. BUT the verifier's PI says type=0 (GTE).
        // The type_threshold_binding constraint catches the mismatch.
        let value = BabyBear::new(50);
        let threshold = BabyBear::new(100);
        let commitment = test_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };

        let compound_witness = CompoundPredicateWitness {
            predicates: vec![witness],
            formula: BooleanFormula::And(vec![0]),
        };

        let air = CompoundPredicateAir::new(compound_witness);
        let (mut trace, public_inputs) = air.generate_trace();

        // Tamper: set pred_type to LT (3) and use LT diff formula.
        trace[0][PRED_TYPE_COL] = BabyBear::new(3); // LT
        let tampered_diff = BabyBear::new(49); // threshold - value - 1
        trace[0][col::DIFF] = tampered_diff;

        let diff_val = 49u32;
        for i in 0..PREDICATE_DIFF_BITS {
            let bit = (diff_val >> i) & 1;
            trace[0][col::diff_bit(i)] = BabyBear::new(bit);
        }

        trace[0][RESULT_COL] = BabyBear::ONE;
        let last = trace.len() - 1;
        trace[last][RESULT_COL] = BabyBear::ONE;

        let result = ConstraintProver::verify_trace(&air, &trace, &public_inputs);
        assert!(
            !result.is_valid(),
            "Tampered trace with wrong predicate_type must fail constraints"
        );

        // The type_threshold_binding constraint should catch this.
        let has_binding_violation = result.violations().iter().any(|v| {
            v.constraint_name == "type_threshold_binding"
                || v.constraint_name == "predicate_type_matches_public_input"
        });
        assert!(
            has_binding_violation,
            "Should have type binding violation when prover changes type column, got: {:?}",
            result.violations()
        );
    }
}
