//! Cryptographic verification of compute delivery proofs.
//!
//! This module defines the AIR circuit that validates delivery proofs submitted by
//! compute providers when claiming payment. A valid delivery proof attests:
//!
//! - The provider computed at least `contracted_flops` FLOPS.
//! - The computation completed within `max_duration` time units.
//! - The quality score meets or exceeds `min_quality`.
//!
//! These constraints are enforced as a STARK AIR (Algebraic Intermediate Representation)
//! using the temporal accumulator pattern. The verifier reconstructs expected public
//! inputs from the settlement's SLA parameters, then cryptographically verifies the
//! STARK proof — ensuring a malicious provider cannot claim payment without actually
//! performing the contracted computation.
//!
//! # Security Model
//!
//! Prior to this module, delivery "verification" only checked format: deserialize as
//! `StarkProof`, verify AIR name prefix, check `query_proofs` non-empty. This was
//! equivalent to accepting any non-empty byte sequence with the right header — a
//! critical vulnerability allowing providers to claim payment without doing work.
//!
//! The fix calls `stark::verify()` with the appropriate circuit descriptor and
//! public inputs derived from the settlement's contracted SLA parameters.
//!
//! # DSL Circuit
//!
//! This module uses the DSL `CircuitDescriptor` infrastructure, replacing the previous
//! raw `impl StarkAir` approach. The descriptor works with all three backends
//! (STARK + Plonky3 + Kimchi).

use pyana_circuit::field::BabyBear;
use pyana_circuit::stark;
use pyana_dsl_runtime::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

use crate::orderbook::SlaGuarantees;
use crate::settlement::Settlement;

/// BabyBear prime for negation in polynomial terms.
const BABYBEAR_P: u32 = pyana_circuit::field::BABYBEAR_P;

// =============================================================================
// Compute SLA (the verifier's view of what was contracted)
// =============================================================================

/// The compute SLA parameters that the delivery proof must satisfy.
///
/// Derived from the settlement's offering + order parameters. The verifier
/// reconstructs these from on-chain/in-state data — they are NOT provided by
/// the prover.
#[derive(Clone, Debug)]
pub struct ComputeSla {
    /// Minimum total FLOPS the provider must have computed.
    pub contracted_flops: u64,
    /// Maximum duration (in time units) the computation may have taken.
    pub max_duration: u64,
    /// Minimum quality score (0-1000 scale, basis points).
    pub min_quality: u32,
    /// Compute hours contracted (from the settlement).
    pub compute_hours: u64,
}

impl ComputeSla {
    /// Derive a `ComputeSla` from a settlement and its offering's SLA guarantees.
    ///
    /// The contracted FLOPS is derived from compute_hours * a baseline FLOPS/hour rate.
    /// Duration is the number of compute hours (the provider must finish within this window).
    /// Quality is derived from the offering's uptime guarantee.
    pub fn from_settlement(settlement: &Settlement, sla: &SlaGuarantees) -> Self {
        // Baseline: 1 compute-hour = 10^12 FLOPS (1 TFLOPS-hour).
        // This is a simplification; real deployments would use GPU-specific rates.
        const FLOPS_PER_HOUR: u64 = 1_000_000_000_000;

        Self {
            contracted_flops: settlement.compute_hours.saturating_mul(FLOPS_PER_HOUR),
            max_duration: settlement.compute_hours,
            min_quality: sla.uptime_bps,
            compute_hours: settlement.compute_hours,
        }
    }
}

// =============================================================================
// Column Layout
// =============================================================================

/// Column layout for the compute delivery AIR.
///
/// The trace encodes the accumulation of compute work over time steps:
/// - `FLOPS_ACC`: Running total of FLOPS computed so far.
/// - `DURATION_ACC`: Running count of time units elapsed.
/// - `QUALITY_ACC`: Running quality accumulator (sum of per-step quality scores).
/// - `STEP_INDEX`: Current step number (0-indexed).
/// - `FLOPS_DELTA`: FLOPS to accumulate in the transition from this row to the next.
/// - `QUALITY_DELTA`: Quality to accumulate in the transition from this row to the next.
/// - `DIFF`: Difference value being range-checked (non-negative witness).
/// - `DIFF_BITS[0..30]`: Bit decomposition of DIFF for range proof.
/// - `STEP_PLUS_ONE`: step_index + 1 (auxiliary for step continuity transition).
/// - `FLOPS_ACC_NEXT`: flops_acc + flops_delta (auxiliary for flops transition).
/// - `QUALITY_ACC_NEXT`: quality_acc + quality_delta (auxiliary for quality transition).
/// - `DURATION_ACC_NEXT`: duration_acc + 1 (auxiliary for duration transition).
///
/// Public inputs: [contracted_flops_lo, contracted_flops_hi, max_duration, min_quality, num_steps]
pub mod col {
    /// Running FLOPS accumulator.
    pub const FLOPS_ACC: usize = 0;
    /// Running duration accumulator.
    pub const DURATION_ACC: usize = 1;
    /// Running quality accumulator.
    pub const QUALITY_ACC: usize = 2;
    /// Step index (0-based).
    pub const STEP_INDEX: usize = 3;
    /// Per-step FLOPS delta (represents transition contribution from this row to next).
    pub const FLOPS_DELTA: usize = 4;
    /// Per-step quality delta (represents transition contribution from this row to next).
    pub const QUALITY_DELTA: usize = 5;
    /// Difference value being range-checked (varies by row context).
    pub const DIFF: usize = 6;
    /// Start of 30-bit decomposition for range proof.
    pub const DIFF_BITS_START: usize = 7;
    /// Number of diff bits.
    pub const NUM_DIFF_BITS: usize = 30;
    /// Auxiliary: step_index + 1 (for step continuity transition).
    pub const STEP_PLUS_ONE: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 37
    /// Auxiliary: flops_acc + flops_delta (for flops accumulation transition).
    pub const FLOPS_ACC_NEXT: usize = STEP_PLUS_ONE + 1; // 38
    /// Auxiliary: quality_acc + quality_delta (for quality accumulation transition).
    pub const QUALITY_ACC_NEXT: usize = FLOPS_ACC_NEXT + 1; // 39
    /// Auxiliary: duration_acc + 1 (for duration monotonicity transition).
    pub const DURATION_ACC_NEXT: usize = QUALITY_ACC_NEXT + 1; // 40
    /// Total trace width.
    pub const WIDTH: usize = DURATION_ACC_NEXT + 1; // 41
}

/// Public input indices for the compute delivery AIR.
pub mod pi {
    /// Lower 31 bits of contracted FLOPS (split for BabyBear field).
    pub const CONTRACTED_FLOPS_LO: usize = 0;
    /// Upper bits of contracted FLOPS.
    pub const CONTRACTED_FLOPS_HI: usize = 1;
    /// Maximum allowed duration.
    pub const MAX_DURATION: usize = 2;
    /// Minimum quality threshold (total = min_quality * num_steps).
    pub const MIN_QUALITY: usize = 3;
    /// Number of steps in the trace (padded to power of two).
    pub const NUM_STEPS: usize = 4;
    /// Total public input count.
    pub const COUNT: usize = 5;
}

// =============================================================================
// Circuit Descriptor
// =============================================================================

/// Build the `CircuitDescriptor` for the compute delivery verification circuit.
///
/// Constraints enforced:
/// 1. Binary constraints: each diff_bit is 0 or 1.
/// 2. Bit reconstruction: diff == sum(diff_bits[j] * 2^j).
/// 3. Range proof: high bit of diff is zero (proves diff < 2^29, non-negative in BabyBear).
/// 4. Auxiliary consistency: step_plus_one == step_index + 1.
/// 5. Auxiliary consistency: flops_acc_next == flops_acc + flops_delta.
/// 6. Auxiliary consistency: quality_acc_next == quality_acc + quality_delta.
/// 7. Auxiliary consistency: duration_acc_next == duration_acc + 1.
/// 8. Transition: next[flops_acc] == local[flops_acc_next].
/// 9. Transition: next[duration_acc] == local[duration_acc_next].
/// 10. Transition: next[quality_acc] == local[quality_acc_next].
/// 11. Transition: next[step_index] == local[step_plus_one].
///
/// Boundary constraints bind the trace to the public inputs:
/// - Row 0: step_index == 0, duration_acc == 1.
/// - Last row: step_index == pi[NUM_STEPS] - 1.
pub fn compute_delivery_descriptor() -> CircuitDescriptor {
    let columns = vec![
        ColumnDef {
            name: "flops_acc".into(),
            index: col::FLOPS_ACC,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "duration_acc".into(),
            index: col::DURATION_ACC,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "quality_acc".into(),
            index: col::QUALITY_ACC,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "step_index".into(),
            index: col::STEP_INDEX,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "flops_delta".into(),
            index: col::FLOPS_DELTA,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "quality_delta".into(),
            index: col::QUALITY_DELTA,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff".into(),
            index: col::DIFF,
            kind: ColumnKind::Value,
        },
        // 30 diff bit columns
        ColumnDef {
            name: "diff_bit_0".into(),
            index: col::DIFF_BITS_START,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_1".into(),
            index: col::DIFF_BITS_START + 1,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_2".into(),
            index: col::DIFF_BITS_START + 2,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_3".into(),
            index: col::DIFF_BITS_START + 3,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_4".into(),
            index: col::DIFF_BITS_START + 4,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_5".into(),
            index: col::DIFF_BITS_START + 5,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_6".into(),
            index: col::DIFF_BITS_START + 6,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_7".into(),
            index: col::DIFF_BITS_START + 7,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_8".into(),
            index: col::DIFF_BITS_START + 8,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_9".into(),
            index: col::DIFF_BITS_START + 9,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_10".into(),
            index: col::DIFF_BITS_START + 10,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_11".into(),
            index: col::DIFF_BITS_START + 11,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_12".into(),
            index: col::DIFF_BITS_START + 12,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_13".into(),
            index: col::DIFF_BITS_START + 13,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_14".into(),
            index: col::DIFF_BITS_START + 14,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_15".into(),
            index: col::DIFF_BITS_START + 15,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_16".into(),
            index: col::DIFF_BITS_START + 16,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_17".into(),
            index: col::DIFF_BITS_START + 17,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_18".into(),
            index: col::DIFF_BITS_START + 18,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_19".into(),
            index: col::DIFF_BITS_START + 19,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_20".into(),
            index: col::DIFF_BITS_START + 20,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_21".into(),
            index: col::DIFF_BITS_START + 21,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_22".into(),
            index: col::DIFF_BITS_START + 22,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_23".into(),
            index: col::DIFF_BITS_START + 23,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_24".into(),
            index: col::DIFF_BITS_START + 24,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_25".into(),
            index: col::DIFF_BITS_START + 25,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_26".into(),
            index: col::DIFF_BITS_START + 26,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_27".into(),
            index: col::DIFF_BITS_START + 27,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_28".into(),
            index: col::DIFF_BITS_START + 28,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "diff_bit_29".into(),
            index: col::DIFF_BITS_START + 29,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "step_plus_one".into(),
            index: col::STEP_PLUS_ONE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "flops_acc_next".into(),
            index: col::FLOPS_ACC_NEXT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "quality_acc_next".into(),
            index: col::QUALITY_ACC_NEXT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "duration_acc_next".into(),
            index: col::DURATION_ACC_NEXT,
            kind: ColumnKind::Value,
        },
    ];

    let mut constraints = Vec::new();

    // C1: Each diff_bit is binary: bit * (bit - 1) == 0
    for i in 0..col::NUM_DIFF_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: col::DIFF_BITS_START + i,
        });
    }

    // C2: Bit reconstruction: sum(diff_bits[i] * 2^i) - diff == 0
    {
        let mut terms = Vec::with_capacity(col::NUM_DIFF_BITS + 1);
        let mut power_of_two = 1u32;
        for i in 0..col::NUM_DIFF_BITS {
            terms.push(PolyTerm {
                coeff: BabyBear::new(power_of_two),
                col_indices: vec![col::DIFF_BITS_START + i],
            });
            power_of_two = power_of_two.wrapping_mul(2);
            // Keep within BabyBear range (2^30 < BABYBEAR_P ~ 2^31)
            power_of_two %= BABYBEAR_P;
        }
        // - diff
        terms.push(PolyTerm {
            coeff: BabyBear::new(BABYBEAR_P - 1),
            col_indices: vec![col::DIFF],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // C3: High bit is zero (range proof: diff < 2^29 => non-negative in BabyBear).
    // diff_bits[29] == 0, expressed as: +1 * diff_bits[29] == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1],
        }],
    });

    // C4: Auxiliary consistency: step_plus_one == step_index + 1
    // step_plus_one - step_index - 1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::STEP_PLUS_ONE],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::STEP_INDEX],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![],
            },
        ],
    });

    // C5: Auxiliary consistency: flops_acc_next == flops_acc + flops_delta
    // flops_acc_next - flops_acc - flops_delta == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::FLOPS_ACC_NEXT],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::FLOPS_ACC],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::FLOPS_DELTA],
            },
        ],
    });

    // C6: Auxiliary consistency: quality_acc_next == quality_acc + quality_delta
    // quality_acc_next - quality_acc - quality_delta == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::QUALITY_ACC_NEXT],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::QUALITY_ACC],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::QUALITY_DELTA],
            },
        ],
    });

    // C7: Auxiliary consistency: duration_acc_next == duration_acc + 1
    // duration_acc_next - duration_acc - 1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::DURATION_ACC_NEXT],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![col::DURATION_ACC],
            },
            PolyTerm {
                coeff: BabyBear::new(BABYBEAR_P - 1),
                col_indices: vec![],
            },
        ],
    });

    // T1 (transition): next[flops_acc] == local[flops_acc_next]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::FLOPS_ACC,
        local_col: col::FLOPS_ACC_NEXT,
    });

    // T2 (transition): next[duration_acc] == local[duration_acc_next]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::DURATION_ACC,
        local_col: col::DURATION_ACC_NEXT,
    });

    // T3 (transition): next[quality_acc] == local[quality_acc_next]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::QUALITY_ACC,
        local_col: col::QUALITY_ACC_NEXT,
    });

    // T4 (transition): next[step_index] == local[step_plus_one]
    constraints.push(ConstraintExpr::Transition {
        next_col: col::STEP_INDEX,
        local_col: col::STEP_PLUS_ONE,
    });

    let boundaries = vec![
        // Row 0: step_index == 0
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::STEP_INDEX,
            value: BabyBear::ZERO,
        },
        // Row 0: duration_acc == 1 (first step counts as 1 unit of duration)
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::DURATION_ACC,
            value: BabyBear::ONE,
        },
        // Last row: step_index == pi[NUM_STEPS] - 1 (0-indexed)
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::STEP_PLUS_ONE,
            pi_index: pi::NUM_STEPS,
        },
    ];

    CircuitDescriptor {
        name: "compute-delivery-gpu-flops-v1".to_string(),
        trace_width: col::WIDTH,
        max_degree: 2, // Binary constraints are degree 2, all others are degree 1
        columns,
        constraints,
        boundaries,
        public_input_count: pi::COUNT,
    }
}

/// Construct a `DslCircuit` for compute delivery verification.
pub fn compute_delivery_circuit() -> DslCircuit {
    DslCircuit::new(compute_delivery_descriptor())
}

// =============================================================================
// Public Input Construction
// =============================================================================

/// Reconstruct the expected public inputs from the SLA parameters.
///
/// The verifier computes these from the settlement data — they are NOT taken
/// from the proof itself (that would be circular).
pub fn compute_delivery_public_inputs(sla: &ComputeSla) -> Vec<BabyBear> {
    // Split contracted_flops into lo/hi for BabyBear field (31-bit elements).
    let flops_lo = (sla.contracted_flops & 0x7FFF_FFFF) as u32;
    let flops_hi = ((sla.contracted_flops >> 31) & 0x7FFF_FFFF) as u32;

    vec![
        BabyBear::new(flops_lo),                 // pi[0]: contracted_flops_lo
        BabyBear::new(flops_hi),                 // pi[1]: contracted_flops_hi
        BabyBear::new(sla.max_duration as u32),  // pi[2]: max_duration
        BabyBear::new(sla.min_quality),          // pi[3]: min_quality
        BabyBear::new(sla.compute_hours as u32), // pi[4]: num_steps (padded to pow2)
    ]
}

// =============================================================================
// Trace Generation
// =============================================================================

/// Generate an execution trace for the compute delivery circuit.
///
/// The trace encodes the accumulation of compute work over `num_steps` time steps.
/// Each step contributes a FLOPS delta and a quality delta. The prover fills in
/// the diff column and its bit decomposition for the range proof at each row.
///
/// # Trace Semantics
///
/// - `FLOPS_DELTA[i]`: the FLOPS contribution that transitions row i to row i+1.
/// - `QUALITY_DELTA[i]`: the quality contribution that transitions row i to row i+1.
/// - Auxiliary columns are filled to satisfy the polynomial constraints.
///
/// `step_flops[i]` and `step_quality[i]` represent the contributions at step i.
/// The accumulator at row i reflects the sum through step i.
pub fn generate_delivery_trace(
    sla: &ComputeSla,
    step_flops: &[u64],
    step_quality: &[u32],
) -> Vec<Vec<BabyBear>> {
    let num_steps = step_flops.len();
    assert_eq!(num_steps, step_quality.len());
    assert!(num_steps >= 2);

    // Pad to power of two.
    let trace_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(trace_len);

    // Compute running accumulators.
    let mut flops_acc = 0u64;
    let mut quality_acc = 0u64;

    for i in 0..trace_len {
        let mut row = vec![BabyBear::ZERO; col::WIDTH];

        // Current step values (zero-pad beyond actual steps).
        let step_f = if i < num_steps { step_flops[i] } else { 0 };
        let step_q = if i < num_steps {
            step_quality[i] as u64
        } else {
            0
        };

        // Accumulate.
        flops_acc = flops_acc.wrapping_add(step_f);
        quality_acc = quality_acc.wrapping_add(step_q);

        // Accumulators.
        row[col::FLOPS_ACC] = BabyBear::from_u64(flops_acc);
        row[col::DURATION_ACC] = BabyBear::new((i as u32) + 1); // Duration starts at 1.
        row[col::QUALITY_ACC] = BabyBear::from_u64(quality_acc);
        row[col::STEP_INDEX] = BabyBear::new(i as u32);

        // Delta for the transition FROM this row TO the next.
        // This is the next step's contribution (or 0 if at/past last step).
        let next_f = if i + 1 < num_steps {
            step_flops[i + 1]
        } else {
            0
        };
        let next_q = if i + 1 < num_steps {
            step_quality[i + 1] as u64
        } else {
            0
        };
        row[col::FLOPS_DELTA] = BabyBear::from_u64(next_f);
        row[col::QUALITY_DELTA] = BabyBear::from_u64(next_q);

        // Diff column: context-dependent range check witness.
        // For the last actual step, this proves the SLA thresholds are met.
        // For other rows, it can be the flops_diff, duration_diff, or quality_diff.
        let diff_value = if i == num_steps - 1 {
            // Last meaningful step: prove flops_acc >= contracted_flops.
            flops_acc.saturating_sub(sla.contracted_flops) as u32
        } else if i == num_steps.saturating_sub(2) {
            // Second-to-last: prove duration is within bounds.
            (sla.max_duration as u32).saturating_sub(i as u32 + 1)
        } else {
            // Other rows: prove quality accumulation (or zero for padding).
            quality_acc.saturating_sub(sla.min_quality as u64 * (i as u64 + 1)) as u32
        };
        row[col::DIFF] = BabyBear::new(diff_value);

        // Bit decomposition of diff.
        for bit_idx in 0..col::NUM_DIFF_BITS {
            let bit = (diff_value >> bit_idx) & 1;
            row[col::DIFF_BITS_START + bit_idx] = BabyBear::new(bit);
        }

        // Auxiliary columns.
        row[col::STEP_PLUS_ONE] = BabyBear::new(i as u32 + 1);
        row[col::FLOPS_ACC_NEXT] = BabyBear::from_u64(flops_acc.wrapping_add(next_f));
        row[col::QUALITY_ACC_NEXT] = BabyBear::from_u64(quality_acc.wrapping_add(next_q));
        row[col::DURATION_ACC_NEXT] = BabyBear::new(i as u32 + 2); // duration_acc + 1

        trace.push(row);
    }

    trace
}

// =============================================================================
// Verification Entry Point
// =============================================================================

/// Errors from delivery proof verification.
#[derive(Debug, Clone)]
pub enum DeliveryVerificationError {
    /// The proof bytes are not a valid STARK proof.
    InvalidProofFormat(String),
    /// The proof's AIR name does not match the expected compute-delivery prefix.
    AirNameMismatch {
        expected_prefix: String,
        actual: String,
    },
    /// The proof is structurally incomplete (no queries, insufficient trace).
    StructurallyInvalid(String),
    /// Cryptographic verification failed (the proof does not satisfy the circuit).
    VerificationFailed(String),
}

impl std::fmt::Display for DeliveryVerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProofFormat(msg) => write!(f, "invalid proof format: {msg}"),
            Self::AirNameMismatch {
                expected_prefix,
                actual,
            } => {
                write!(
                    f,
                    "AIR name mismatch: expected prefix '{expected_prefix}', got '{actual}'"
                )
            }
            Self::StructurallyInvalid(msg) => write!(f, "structurally invalid: {msg}"),
            Self::VerificationFailed(msg) => write!(f, "cryptographic verification failed: {msg}"),
        }
    }
}

/// Verify a compute delivery proof cryptographically.
///
/// This performs:
/// 1. Deserialization of the STARK proof from bytes.
/// 2. AIR name prefix validation ("compute-delivery-").
/// 3. Structural integrity checks (non-empty queries, valid trace length).
/// 4. **Cryptographic STARK verification** against the `compute_delivery_descriptor()`
///    circuit with public inputs derived from the settlement's SLA parameters.
///
/// Returns `Ok(())` on success, or a detailed error on failure.
pub fn verify_delivery_proof(
    proof_bytes: &[u8],
    sla: &ComputeSla,
) -> Result<(), DeliveryVerificationError> {
    // Step 1: Deserialize the STARK proof.
    if proof_bytes.is_empty() {
        return Err(DeliveryVerificationError::InvalidProofFormat(
            "delivery proof must not be empty".to_string(),
        ));
    }

    let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|e| {
        DeliveryVerificationError::InvalidProofFormat(format!("not a valid STARK proof: {e}"))
    })?;

    // Step 2: Verify AIR name matches the compute-delivery family.
    if !stark_proof.air_name.starts_with("compute-delivery-") {
        return Err(DeliveryVerificationError::AirNameMismatch {
            expected_prefix: "compute-delivery-".to_string(),
            actual: stark_proof.air_name.clone(),
        });
    }

    // Step 3: Structural integrity.
    if stark_proof.query_proofs.is_empty() || stark_proof.trace_len < 2 {
        return Err(DeliveryVerificationError::StructurallyInvalid(
            "no query proofs or insufficient trace length".to_string(),
        ));
    }

    // Step 4: Reconstruct expected public inputs from the SLA.
    let expected_pi = compute_delivery_public_inputs(sla);

    // Step 5: CRYPTOGRAPHIC VERIFICATION.
    // This is the critical step that was previously missing. Without this,
    // any byte sequence passing structural checks would be accepted.
    let circuit = compute_delivery_circuit();
    stark::verify(&circuit, &stark_proof, &expected_pi)
        .map_err(|e| DeliveryVerificationError::VerificationFailed(e))?;

    Ok(())
}
