//! Temporal predicate expressed as a CircuitDescriptor.
//!
//! Demonstrates the DSL runtime's ability to handle MULTI-ROW proofs with
//! row-to-row (transition) constraints. This is the key test for proving that
//! the `ConstraintExpr::Transition` variant correctly enforces relationships
//! between consecutive rows.
//!
//! # What this proves
//!
//! "Attribute X >= threshold for N consecutive blocks."
//!
//! # Trace layout (per row)
//!
//! | Column | Name           | Description                              |
//! |--------|----------------|------------------------------------------|
//! | 0      | value          | The attribute value at this block        |
//! | 1      | threshold      | Constant threshold across all rows       |
//! | 2      | diff           | value - threshold                        |
//! | 3..32  | diff_bits[0..29] | Bit decomposition proving diff >= 0   |
//! | 33     | accumulator    | Running step counter (1, 2, ..., N)      |
//! | 34     | step_index     | Step index (0, 1, ..., N-1)              |
//! | 35     | acc_plus_one   | accumulator + 1 (auxiliary for transition)|
//! | 36     | step_plus_one  | step_index + 1 (auxiliary for transition) |
//!
//! # Constraints
//!
//! Per-row:
//! - diff = value - threshold (Polynomial)
//! - Each diff_bit is binary (Binary)
//! - Bit reconstruction: sum(diff_bits[i] * 2^i) = diff (Polynomial)
//! - High bit is zero: diff_bits[29] = 0 (proves diff < 2^30, i.e., non-negative)
//! - acc_plus_one = accumulator + 1 (Polynomial)
//! - step_plus_one = step_index + 1 (Polynomial)
//!
//! Transition:
//! - next[accumulator] = local[acc_plus_one] (Transition)
//! - next[step_index] = local[step_plus_one] (Transition)
//!
//! Boundary:
//! - row(0).accumulator = 1 (Fixed)
//! - row(last).accumulator = num_steps (PiBinding to public_input[0])
//! - row(0).step_index = 0 (Fixed)

use pyana_circuit::field::{BabyBear, BABYBEAR_P};
use pyana_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
pub const TRACE_WIDTH: usize = STEP_PLUS_ONE + 1; // 37

/// Public input layout: [num_steps]
pub const PI_NUM_STEPS: usize = 0;
pub const PUBLIC_INPUT_COUNT: usize = 1;

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the temporal predicate `CircuitDescriptor`.
///
/// This descriptor encodes:
/// - Per-row arithmetic (diff computation, binary checks, bit reconstruction)
/// - Transition constraints (accumulator/step increment via auxiliary columns)
/// - Boundary constraints (first row initialization, last row public input binding)
pub fn temporal_predicate_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut columns = Vec::with_capacity(TRACE_WIDTH);
    columns.push(ColumnDef { name: "value".into(), index: VALUE, kind: ColumnKind::Value });
    columns.push(ColumnDef { name: "threshold".into(), index: THRESHOLD, kind: ColumnKind::Value });
    columns.push(ColumnDef { name: "diff".into(), index: DIFF, kind: ColumnKind::Value });
    for i in 0..NUM_DIFF_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: DIFF_BITS_START + i,
            kind: ColumnKind::Binary,
        });
    }
    columns.push(ColumnDef { name: "accumulator".into(), index: ACCUMULATOR, kind: ColumnKind::Value });
    columns.push(ColumnDef { name: "step_index".into(), index: STEP_INDEX, kind: ColumnKind::Value });
    columns.push(ColumnDef { name: "acc_plus_one".into(), index: ACC_PLUS_ONE, kind: ColumnKind::Value });
    columns.push(ColumnDef { name: "step_plus_one".into(), index: STEP_PLUS_ONE, kind: ColumnKind::Value });

    let mut constraints = Vec::new();

    // ─── C1: diff = value - threshold ────────────────────────────────────────
    // Expressed as: diff - value + threshold == 0
    // => +1*diff + (-1)*value + (+1)*threshold == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![DIFF] },
            PolyTerm { coeff: neg_one, col_indices: vec![VALUE] },
            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![THRESHOLD] },
        ],
    });

    // ─── C2: Each diff_bit is binary ─────────────────────────────────────────
    for i in 0..NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary { col: DIFF_BITS_START + i });
    }

    // ─── C3: Bit reconstruction matches diff ─────────────────────────────────
    // sum(diff_bits[i] * 2^i) - diff == 0
    // => +2^0 * bit_0 + 2^1 * bit_1 + ... + 2^29 * bit_29 + (-1) * diff == 0
    {
        let mut terms = Vec::with_capacity(NUM_DIFF_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![DIFF_BITS_START + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
            // Keep within BabyBear field -- all powers of 2 up to 2^29 fit in u32
        }
        // Subtract diff
        terms.push(PolyTerm { coeff: neg_one, col_indices: vec![DIFF] });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // ─── C4: High bit is zero (range proof: diff < 2^30) ────────────────────
    // diff_bits[29] == 0 is equivalent to a Polynomial with a single term.
    // We use Binary on bit 29 is already covered above (bit*(bit-1)==0), but
    // we also need bit_29 == 0 specifically. Express as: +1 * diff_bits[29] == 0.
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![DIFF_BITS_START + NUM_DIFF_BITS - 1],
        }],
    });

    // ─── C5: acc_plus_one = accumulator + 1 ─────────────────────────────────
    // acc_plus_one - accumulator - 1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![ACC_PLUS_ONE] },
            PolyTerm { coeff: neg_one, col_indices: vec![ACCUMULATOR] },
            PolyTerm { coeff: neg_one, col_indices: vec![] }, // constant -1
        ],
    });

    // ─── C6: step_plus_one = step_index + 1 ─────────────────────────────────
    // step_plus_one - step_index - 1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm { coeff: BabyBear::ONE, col_indices: vec![STEP_PLUS_ONE] },
            PolyTerm { coeff: neg_one, col_indices: vec![STEP_INDEX] },
            PolyTerm { coeff: neg_one, col_indices: vec![] }, // constant -1
        ],
    });

    // ─── C7: Transition: next[accumulator] == local[acc_plus_one] ────────────
    constraints.push(ConstraintExpr::Transition {
        next_col: ACCUMULATOR,
        local_col: ACC_PLUS_ONE,
    });

    // ─── C8: Transition: next[step_index] == local[step_plus_one] ────────────
    constraints.push(ConstraintExpr::Transition {
        next_col: STEP_INDEX,
        local_col: STEP_PLUS_ONE,
    });

    // ─── Boundaries ──────────────────────────────────────────────────────────
    let boundaries = vec![
        // First row: accumulator = 1
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: ACCUMULATOR,
            value: BabyBear::ONE,
        },
        // First row: step_index = 0
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: STEP_INDEX,
            value: BabyBear::ZERO,
        },
        // Last row: accumulator = num_steps (public input 0)
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: ACCUMULATOR,
            pi_index: PI_NUM_STEPS,
        },
    ];

    CircuitDescriptor {
        name: "pyana-temporal-predicate-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a valid temporal predicate trace.
///
/// Each row represents one block where `value >= threshold`.
/// The trace must have at least 2 rows (STARK requirement) and be a power of 2.
///
/// Returns `(trace, public_inputs)`.
pub fn generate_temporal_trace(
    values: &[u32],
    threshold: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = values.len();
    assert!(num_steps >= 1, "need at least 1 step");

    // Pad to power of 2, minimum 2.
    let padded_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(padded_len);

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];

        // For padding rows beyond num_steps, repeat the last real row's value.
        let val = if step < num_steps { values[step] } else { values[num_steps - 1] };

        row[VALUE] = BabyBear::new(val);
        row[THRESHOLD] = BabyBear::new(threshold);

        // diff = value - threshold (wraps in field if value < threshold)
        let diff = val.wrapping_sub(threshold);
        row[DIFF] = BabyBear::new(diff);

        // Bit decomposition of diff
        for i in 0..NUM_DIFF_BITS {
            row[DIFF_BITS_START + i] = BabyBear::new((diff >> i) & 1);
        }

        // Accumulator: 1-indexed (step 0 -> acc = 1, step 1 -> acc = 2, ...)
        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);

        // Step index: 0-indexed
        row[STEP_INDEX] = BabyBear::new(step as u32);

        // Auxiliary: acc + 1
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);

        // Auxiliary: step + 1
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        trace.push(row);
    }

    // Public inputs: the padded trace length is what the last-row boundary checks.
    let public_inputs = vec![BabyBear::new(padded_len as u32)];

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::stark::{self, StarkAir};
    use pyana_dsl_runtime::circuit::DslCircuit;

    // ========================================================================
    // Test 1: Valid trace -- all constraints evaluate to zero
    // ========================================================================

    #[test]
    fn test_temporal_dsl_valid_trace() {
        let descriptor = temporal_predicate_descriptor();
        assert!(descriptor.validate().is_ok(), "descriptor should be valid");

        let circuit = DslCircuit::new(descriptor);

        // 3 steps, value=100, threshold=50 => diff=50 for all rows
        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Padded to 4 rows (next power of 2 from 3).
        assert_eq!(trace.len(), 4);

        // Verify per-row + transition constraints evaluate to zero.
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &public_inputs, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Constraint nonzero at row {i} (valid trace)"
            );
        }

        // Verify accumulator reaches expected value at last row.
        let last_acc = trace.last().unwrap()[ACCUMULATOR];
        assert_eq!(last_acc, BabyBear::new(4), "accumulator should reach padded_len=4");

        // Full STARK prove/verify cycle.
        let proof = stark::prove(&circuit, &trace, &public_inputs);
        let result = stark::verify(&circuit, &proof, &public_inputs);
        assert!(result.is_ok(), "STARK verify failed on valid trace: {:?}", result.err());
    }

    // ========================================================================
    // Test 2: Invalid trace -- value < threshold at step 2
    // ========================================================================

    #[test]
    fn test_temporal_dsl_invalid_value_below_threshold() {
        let descriptor = temporal_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Step 1: value=100 (ok), Step 2: value=30 (BAD: 30 < 50), Step 3: value=100
        let values = vec![100u32, 30, 100];
        let threshold = 50u32;

        // Generate trace manually (the generator naively computes, we check constraints)
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Row 1 (index 1) has value=30, threshold=50.
        // diff = 30 - 50 = wrapping subtraction in u32 = a huge number.
        // The bit decomposition of that huge number will have bit 29 set (since it
        // represents a number >= 2^30 in the field). The "high bit zero" constraint
        // will be nonzero.
        let alpha = BabyBear::new(7);
        let row1_result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            row1_result,
            BabyBear::ZERO,
            "Constraint should be nonzero at row 1 where value < threshold"
        );
    }

    // ========================================================================
    // Test 3: Invalid trace -- accumulator gap (skip step)
    // ========================================================================

    #[test]
    fn test_temporal_dsl_invalid_accumulator_gap() {
        let descriptor = temporal_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        // Build a valid trace, then corrupt the accumulator at row 2
        // to create a gap (skip from acc=2 to acc=4).
        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (mut trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Corrupt row 2: set accumulator to 4 instead of 3
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        // Also update acc_plus_one to be consistent with the corrupt accumulator
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);

        // The transition constraint at row 1 -> row 2 checks:
        // next[ACCUMULATOR] == local[ACC_PLUS_ONE]
        // local[ACC_PLUS_ONE] at row 1 = 3 (since acc at row 1 = 2, so 2+1=3)
        // next[ACCUMULATOR] at row 2 = 4 (corrupted)
        // => Transition evaluates to 4 - 3 = 1 (nonzero!)
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Transition constraint should be nonzero when accumulator has a gap"
        );

        // Additionally, the per-row constraint at row 2 for acc_plus_one is satisfied
        // (we fixed it up), but the transition from row 1 catches the discontinuity.
        // Verify that row 0 -> row 1 is still fine.
        let result_01 = circuit.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(
            result_01,
            BabyBear::ZERO,
            "Rows 0->1 should still be valid (corruption is at row 2)"
        );
    }

    // ========================================================================
    // Test 4: Descriptor validates successfully
    // ========================================================================

    #[test]
    fn test_temporal_descriptor_validation() {
        let descriptor = temporal_predicate_descriptor();
        let result = descriptor.validate();
        assert!(result.is_ok(), "Descriptor validation failed: {:?}", result.err());

        // Check structural properties
        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.max_degree, 2);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
        assert_eq!(descriptor.name, "pyana-temporal-predicate-dsl-v1");

        // Check we have the expected constraint count:
        // 1 (diff) + 30 (binary) + 1 (reconstruction) + 1 (high bit) +
        // 1 (acc_plus_one) + 1 (step_plus_one) + 2 (transitions) = 37
        assert_eq!(descriptor.constraints.len(), 37);

        // Check boundary count: 3 (first acc, first step, last acc)
        assert_eq!(descriptor.boundaries.len(), 3);
    }

    // ========================================================================
    // Test 5: Transition constraint is specifically a Transition variant
    // ========================================================================

    #[test]
    fn test_temporal_has_transition_constraints() {
        let descriptor = temporal_predicate_descriptor();

        let transition_count = descriptor.constraints.iter().filter(|c| {
            matches!(c, ConstraintExpr::Transition { .. })
        }).count();

        assert_eq!(
            transition_count, 2,
            "Should have exactly 2 transition constraints (accumulator + step_index)"
        );
    }

    // ========================================================================
    // Test 6: Step index transition detected
    // ========================================================================

    #[test]
    fn test_temporal_dsl_invalid_step_index_gap() {
        let descriptor = temporal_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor);

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (mut trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Corrupt row 2: set step_index to 5 instead of 2
        trace[2][STEP_INDEX] = BabyBear::new(5);
        // Fix up step_plus_one to match the corrupt step_index
        trace[2][STEP_PLUS_ONE] = BabyBear::new(6);

        // Row 1 -> Row 2 transition: next[STEP_INDEX]=5, local[STEP_PLUS_ONE]=2
        // (step at row 1 is 1, so step_plus_one at row 1 is 2)
        // => 5 - 2 = 3 (nonzero!)
        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Transition constraint should catch step_index gap"
        );
    }

    // ========================================================================
    // Test 7: Full STARK prove/verify rejects tampered public inputs
    // ========================================================================

    #[test]
    fn test_temporal_dsl_stark_rejects_wrong_num_steps() {
        let descriptor = temporal_predicate_descriptor();
        let circuit = DslCircuit::new(descriptor.clone());

        let values = vec![100u32, 100, 100];
        let threshold = 50u32;
        let (trace, public_inputs) = generate_temporal_trace(&values, threshold);

        // Prove with correct public inputs
        let proof = stark::prove(&circuit, &trace, &public_inputs);

        // Verify with wrong num_steps should fail
        let wrong_pi = vec![BabyBear::new(8)]; // claims 8 steps instead of 4
        let circuit2 = DslCircuit::new(descriptor);
        let result = stark::verify(&circuit2, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong num_steps");
    }
}
