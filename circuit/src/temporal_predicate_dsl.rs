//! DSL-generated temporal predicate AIR.
//!
//! This module replaces the hand-written `temporal_predicate_air.rs` with the
//! equivalent of the `#[dregg_circuit]` macro-generated implementation. The
//! macro version (in `dregg-dsl-tests/src/temporal_macro.rs`) passes full STARK
//! prove/verify and is bit-for-bit equivalent to the manual descriptor in
//! `dregg-dsl-tests/src/temporal_dsl.rs`.
//!
//! Because proc-macro-generated code references `dregg_circuit::*` which cannot
//! resolve when compiled *within* the `dregg-circuit` crate itself, this file
//! contains the manually-expanded equivalent of what `#[dregg_circuit]` would
//! produce.
//!
//! # Migration
//!
//! All callers should use this module instead of `temporal_predicate_air`.
//! The public API is preserved: `TemporalPredicateAir`, `TemporalPredicateWitness`,
//! `TemporalPredicateProof`, `prove_temporal_predicate`, `verify_temporal_predicate`,
//! and `TemporalPredicateRequirement` are all re-exported with the same signatures.

use crate::field::BabyBear;
use crate::predicate_air::PredicateType;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

// ─────────────────────────────────────────────────────────────────────────────
// DSL-equivalent core AIR (manual expansion of #[dregg_circuit] output)
// ─────────────────────────────────────────────────────────────────────────────

/// Column layout constants for the DSL temporal AIR.
///
/// **Post AIR-soundness audit (ce1e2def #3)**: added `STATE_ROOT`
/// column so that the per-step state-root chain can be bound into
/// public inputs at the trace boundary, closing the
/// "forge proof.initial_state_root / proof.final_state_root after the
/// fact" attack. The legacy 37-column layout grew to 38.
pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
pub const STATE_ROOT: usize = STEP_PLUS_ONE + 1; // 37
pub const DSL_TRACE_WIDTH: usize = STATE_ROOT + 1; // 38

/// Public input layout:
/// `[padded_len, threshold, initial_state_root, final_state_root]`.
///
/// **Post AIR-soundness audit (commit `ce1e2def`, finding #3).** The PI
/// grew from `[padded_len]` to the four-slot layout above to close
/// three forge-the-metadata attacks:
///
/// - **PI[1]=threshold**: previously `proof.threshold` was a plain
///   serde field the verifier compared against itself. An attacker
///   could honestly prove threshold=0 (trivially satisfiable) and then
///   mutate `proof.threshold` to any value; the wrapper re-compared
///   the mutated field against the caller and accepted. Today
///   PI[1]=threshold is bound into row-0 of the THRESHOLD column via
///   [`TemporalPredicateDsl::boundary_constraints`] and held constant
///   across the trace by the T3 inter-row constraint in
///   [`TemporalPredicateDsl::eval_constraints`]. Tampering on
///   `proof.threshold` makes the verifier's reconstructed PI[1]
///   mismatch the STARK's boundary commitment and verify rejects.
/// - **PI[2]=initial_state_root**, **PI[3]=final_state_root**: same
///   attack shape — `proof.initial_state_root` and
///   `proof.final_state_root` were plain serde fields. Today the
///   prover populates the STATE_ROOT column per row from the witness
///   (padding rows hold a copy of the final real state root), and
///   boundary constraints pin row-0 STATE_ROOT to PI[2] and row-(N-1)
///   STATE_ROOT to PI[3]. The verifier reconstructs PIs from the
///   caller's expected roots, so any tampering on the proof's
///   state-root metadata is detected by STARK verification.
///
/// # Remaining (documented) gap
///
/// The per-step VALUE column is NOT bound into PIs. This is **safe by
/// contract**: the temporal predicate's promise is "the predicate held
/// at every step," not "the values were specifically X, Y, Z." The
/// per-row constraint `diff = value - threshold ≥ 0` plus the
/// bit-decomposition + high-bit-zero constraints algebraically force
/// every row's value to satisfy the predicate against the bound
/// threshold; the verifier never reveals individual values, so binding
/// them is unnecessary. (If a future caller needs value identity,
/// binding values via a Poseidon2 chain commitment in a new PI slot
/// would be the right shape.)
pub const PI_NUM_STEPS: usize = 0;
pub const PI_THRESHOLD: usize = 1;
pub const PI_INITIAL_STATE_ROOT: usize = 2;
pub const PI_FINAL_STATE_ROOT: usize = 3;
pub const DSL_PUBLIC_INPUT_COUNT: usize = 4;

/// Column index submodule (mirrors the `mod col` in the `#[dregg_circuit]` definition).
pub mod col {
    pub const VALUE: usize = 0;
    pub const THRESHOLD: usize = 1;
    pub const DIFF: usize = 2;
    pub const DIFF_BITS_START: usize = 3;
    pub const NUM_DIFF_BITS: usize = 30;
    pub const ACCUMULATOR: usize = 33;
    pub const STEP_INDEX: usize = 34;
    pub const ACC_PLUS_ONE: usize = 35;
    pub const STEP_PLUS_ONE: usize = 36;
    /// Per-step state-root column (AIR-soundness-audit ce1e2def #3).
    /// Bound at row 0 to PI[2] (initial_state_root) and at the last
    /// padded row to PI[3] (final_state_root) — see
    /// `TemporalPredicateDsl::boundary_constraints`. Padding rows hold
    /// a copy of the final real state root so the row-N-1 boundary
    /// constraint binds the prover's claimed final root regardless of
    /// where padding starts.
    pub const STATE_ROOT: usize = 37;
}

/// The DSL-generated temporal predicate AIR struct.
///
/// This is the equivalent of what `#[dregg_circuit] mod temporal_predicate_dsl { ... }`
/// would produce: a unit struct implementing `StarkAir`.
pub struct TemporalPredicateDsl;

impl StarkAir for TemporalPredicateDsl {
    fn width(&self) -> usize {
        DSL_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn air_name(&self) -> &'static str {
        "dregg-temporal_predicate_dsl-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // Per-row constraints (inlined from the `fn constraints` body)
        let constraint_values: Vec<BabyBear> = {
            let pi = public_inputs;
            let mut cs = Vec::new();

            // C1: diff = value - threshold
            cs.push(local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD]));

            // C2: Each diff_bit is binary
            for i in 0..col::NUM_DIFF_BITS {
                let bit = local[col::DIFF_BITS_START + i];
                cs.push(bit * (bit - BabyBear::ONE));
            }

            // C3: Bit reconstruction: sum(diff_bits[i] * 2^i) == diff
            {
                let mut reconstructed = BabyBear::ZERO;
                let mut power_of_two = BabyBear::ONE;
                let two = BabyBear::new(2);
                for i in 0..col::NUM_DIFF_BITS {
                    reconstructed = reconstructed + local[col::DIFF_BITS_START + i] * power_of_two;
                    power_of_two = power_of_two * two;
                }
                cs.push(reconstructed - local[col::DIFF]);
            }

            // C4: High bit is zero (range proof: diff < 2^30 => non-negative)
            cs.push(local[col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1]);

            // C5: acc_plus_one = accumulator + 1
            cs.push(local[col::ACC_PLUS_ONE] - local[col::ACCUMULATOR] - BabyBear::ONE);

            // C6: step_plus_one = step_index + 1
            cs.push(local[col::STEP_PLUS_ONE] - local[col::STEP_INDEX] - BabyBear::ONE);

            let _ = pi; // suppress unused warning
            cs
        };

        // Transition constraints (inlined from the `fn transitions` body)
        let transition_values: Vec<BabyBear> = {
            vec![
                // T1: next[accumulator] = local[acc_plus_one]
                next[col::ACCUMULATOR] - local[col::ACC_PLUS_ONE],
                // T2: next[step_index] = local[step_plus_one]
                next[col::STEP_INDEX] - local[col::STEP_PLUS_ONE],
                // T3 (AIR-soundness-audit ce1e2def finding #3): THRESHOLD
                // is constant across all rows. Combined with the row-0
                // boundary constraint binding THRESHOLD to PI[1], this
                // forces the prover's threshold to match the verifier's
                // PI[1] for every row — closing the "honest-prove for
                // threshold=0 then forge proof.threshold field" attack.
                next[col::THRESHOLD] - local[col::THRESHOLD],
            ]
        };

        // Compose all constraints with alpha powers
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;
        for c in constraint_values.iter().chain(transition_values.iter()) {
            result = result + alpha_power * *c;
            alpha_power = alpha_power * alpha;
        }
        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let pi = public_inputs;
        let raw: Vec<(usize, usize, BabyBear)> = vec![
            // First row: accumulator = 1
            (0, col::ACCUMULATOR, BabyBear::ONE),
            // First row: step_index = 0
            (0, col::STEP_INDEX, BabyBear::ZERO),
            // Last row: accumulator = padded_len (pi[0])
            (trace_len - 1, col::ACCUMULATOR, pi[0]),
            // First row: THRESHOLD = pi[1]
            // (AIR-soundness-audit ce1e2def finding #3). Combined with
            // the inter-row constancy constraint T3, this binds the
            // prover's threshold to PI[1] across the entire trace.
            (0, col::THRESHOLD, pi[1]),
            // First row: STATE_ROOT = pi[2] (initial_state_root)
            // (AIR-soundness-audit ce1e2def #3 — state-root binding).
            (0, col::STATE_ROOT, pi[2]),
            // Last row: STATE_ROOT = pi[3] (final_state_root).
            // generate_dsl_trace pads rows num_steps..padded_len with a
            // copy of the final real state root, so this boundary
            // catches the final state root regardless of trace padding.
            (trace_len - 1, col::STATE_ROOT, pi[3]),
        ];
        raw.into_iter()
            .map(|(row, col, value)| BoundaryConstraint { row, col, value })
            .collect()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API: backward-compatible types and functions
// ─────────────────────────────────────────────────────────────────────────────

/// Trace width for the temporal predicate AIR (legacy 35-column layout reference).
pub const TEMPORAL_PREDICATE_WIDTH: usize = 35;

/// Witness for a temporal predicate proof.
///
/// Contains the sequence of values and state roots over the time range,
/// plus the predicate parameters.
#[derive(Clone, Debug)]
pub struct TemporalPredicateWitness {
    /// The attribute values at each step (one per time unit).
    pub values: Vec<BabyBear>,
    /// The state roots at each step (binding to the receipt/IVC chain).
    pub state_roots: Vec<BabyBear>,
    /// The predicate type (currently only GTE is supported for temporal).
    pub predicate_type: PredicateType,
    /// The threshold the predicate must meet at every step.
    pub threshold: BabyBear,
}

impl TemporalPredicateWitness {
    /// Check whether the temporal predicate is satisfiable (all steps pass).
    pub fn is_satisfiable(&self) -> bool {
        if self.values.len() != self.state_roots.len() {
            return false;
        }
        if self.values.is_empty() {
            return false;
        }
        let threshold = self.threshold.as_u32();
        self.values.iter().all(|v| {
            let val = v.as_u32();
            match self.predicate_type {
                PredicateType::Gte | PredicateType::InRangeLow => val >= threshold,
                PredicateType::Lte | PredicateType::InRangeHigh => val <= threshold,
                PredicateType::Gt => val > threshold,
                PredicateType::Lt => val < threshold,
                PredicateType::Neq => val != threshold,
            }
        })
    }

    /// Number of steps in the temporal range.
    pub fn num_steps(&self) -> usize {
        self.values.len()
    }

    /// Compute the diff at a given step based on predicate type.
    fn compute_diff_at(&self, step: usize) -> BabyBear {
        let value = self.values[step];
        let threshold = self.threshold;
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => value - threshold,
            PredicateType::Lte | PredicateType::InRangeHigh => threshold - value,
            PredicateType::Gt => value - threshold - BabyBear::ONE,
            PredicateType::Lt => threshold - value - BabyBear::ONE,
            PredicateType::Neq => value - threshold,
        }
    }
}

/// The Temporal Predicate AIR (DSL-generated).
///
/// This is a wrapper around the DSL-generated `TemporalPredicateDsl` struct
/// that maintains the same public interface as the hand-written version. The
/// witness is stored for trace generation, while constraint evaluation is
/// delegated to the DSL-generated implementation.
pub struct TemporalPredicateAir {
    pub witness: TemporalPredicateWitness,
}

impl TemporalPredicateAir {
    pub fn new(witness: TemporalPredicateWitness) -> Self {
        Self { witness }
    }
}

/// Generate the DSL trace from a witness.
///
/// This converts from the witness format (multiple predicate types, state roots)
/// into the DSL trace layout (37-column layout with auxiliary columns).
pub fn generate_dsl_trace(
    witness: &TemporalPredicateWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = witness.num_steps();
    assert!(num_steps >= 1, "temporal witness must have at least 1 step");

    let padded_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(padded_len);

    // Final real state root — used to pad rows num_steps..padded_len so
    // the row-(N-1) STATE_ROOT boundary constraint binds the prover's
    // claimed final root regardless of where padding starts. See
    // AIR-soundness-audit ce1e2def #3.
    let final_state_root = *witness.state_roots.last().unwrap();
    let initial_state_root = witness.state_roots[0];

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; DSL_TRACE_WIDTH];

        // For padding rows beyond num_steps, repeat the last real row's value.
        let val = if step < num_steps {
            witness.values[step]
        } else {
            *witness.values.last().unwrap()
        };

        row[VALUE] = val;
        row[THRESHOLD] = witness.threshold;

        // Compute diff based on predicate type
        let diff = if step < num_steps {
            witness.compute_diff_at(step)
        } else {
            witness.compute_diff_at(num_steps - 1)
        };
        row[DIFF] = diff;

        // Bit decomposition of diff
        if witness.predicate_type != PredicateType::Neq {
            let diff_val = diff.as_u32();
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff_val >> i) & 1);
            }
        }

        // Accumulator: 1-indexed (step 0 -> acc = 1)
        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        // State root: per-step real value within num_steps; padding rows
        // hold a copy of the final real state root so the row-(N-1)
        // boundary constraint binds the prover's claimed final root.
        row[STATE_ROOT] = if step < num_steps {
            witness.state_roots[step]
        } else {
            final_state_root
        };

        trace.push(row);
    }

    // Public inputs: [padded_len, threshold, initial_state_root, final_state_root]
    // PI[1]=threshold is bound into row-0 THRESHOLD column by
    // boundary_constraints and held constant across rows by the T3
    // transition constraint. PI[2]/PI[3] are bound to row-0 / row-(N-1)
    // STATE_ROOT respectively — see AIR-soundness-audit ce1e2def #3.
    let public_inputs = vec![
        BabyBear::new(padded_len as u32),
        witness.threshold,
        initial_state_root,
        final_state_root,
    ];
    (trace, public_inputs)
}

impl StarkAir for TemporalPredicateAir {
    fn width(&self) -> usize {
        DSL_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "dregg-temporal_predicate_dsl-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // Predicate-type-aware constraint evaluation.
        // The DSL-generated TemporalPredicateDsl only hardcodes diff = value - threshold
        // (Gte semantics). TemporalPredicateAir must adapt C1 for Lte/Gt/Lt.
        let mut cs = Vec::new();

        // C1: diff computation (depends on predicate type)
        match self.witness.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow | PredicateType::Neq => {
                cs.push(local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD]));
            }
            PredicateType::Lte | PredicateType::InRangeHigh => {
                cs.push(local[col::DIFF] - (local[col::THRESHOLD] - local[col::VALUE]));
            }
            PredicateType::Gt => {
                cs.push(
                    local[col::DIFF] - (local[col::VALUE] - local[col::THRESHOLD] - BabyBear::ONE),
                );
            }
            PredicateType::Lt => {
                cs.push(
                    local[col::DIFF] - (local[col::THRESHOLD] - local[col::VALUE] - BabyBear::ONE),
                );
            }
        }

        // C2: Each diff_bit is binary
        for i in 0..col::NUM_DIFF_BITS {
            let bit = local[col::DIFF_BITS_START + i];
            cs.push(bit * (bit - BabyBear::ONE));
        }

        // C3: Bit reconstruction: sum(diff_bits[i] * 2^i) == diff
        {
            let mut reconstructed = BabyBear::ZERO;
            let mut power_of_two = BabyBear::ONE;
            let two = BabyBear::new(2);
            for i in 0..col::NUM_DIFF_BITS {
                reconstructed = reconstructed + local[col::DIFF_BITS_START + i] * power_of_two;
                power_of_two = power_of_two * two;
            }
            cs.push(reconstructed - local[col::DIFF]);
        }

        // C4: High bit is zero (range proof: diff < 2^30 => non-negative)
        cs.push(local[col::DIFF_BITS_START + col::NUM_DIFF_BITS - 1]);

        // C5: acc_plus_one = accumulator + 1
        cs.push(local[col::ACC_PLUS_ONE] - local[col::ACCUMULATOR] - BabyBear::ONE);

        // C6: step_plus_one = step_index + 1
        cs.push(local[col::STEP_PLUS_ONE] - local[col::STEP_INDEX] - BabyBear::ONE);

        // Transition constraints
        let transitions = vec![
            next[col::ACCUMULATOR] - local[col::ACC_PLUS_ONE],
            next[col::STEP_INDEX] - local[col::STEP_PLUS_ONE],
            next[col::THRESHOLD] - local[col::THRESHOLD],
        ];

        let _ = public_inputs;

        // Compose all constraints with alpha powers
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;
        for c in cs.iter().chain(transitions.iter()) {
            result = result + alpha_power * *c;
            alpha_power = alpha_power * alpha;
        }
        result
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        // Delegate to the DSL-generated implementation.
        TemporalPredicateDsl.boundary_constraints(public_inputs, trace_len)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Proof types
// ─────────────────────────────────────────────────────────────────────────────

/// A complete temporal predicate proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TemporalPredicateProof {
    /// The predicate type that was proven.
    pub predicate_type: PredicateType,
    /// The threshold (public).
    pub threshold: BabyBear,
    /// Number of REAL steps over which the predicate held (not including padding).
    pub num_steps: u32,
    /// Padded trace length (power of 2, used in STARK boundary constraints).
    pub padded_len: u32,
    /// The initial state root (binding to the start of the range).
    pub initial_state_root: BabyBear,
    /// The final state root (binding to the end of the range).
    pub final_state_root: BabyBear,
    /// The STARK proof (FRI-based, cryptographically sound).
    pub stark_proof: StarkProof,
}

// ─────────────────────────────────────────────────────────────────────────────
// Prover / Verifier API
// ─────────────────────────────────────────────────────────────────────────────

/// Generate a temporal predicate proof.
///
/// Proves that `predicate_type(value, threshold)` held at every step across the
/// provided sequence of values. The proof is bound to the receipt/IVC chain via
/// the state roots at each step.
///
/// Returns `None` if the predicate does not hold at every step (cannot prove a
/// false temporal statement).
pub fn prove_temporal_predicate(
    values: &[BabyBear],
    state_roots: &[BabyBear],
    predicate_type: PredicateType,
    threshold: BabyBear,
) -> Option<TemporalPredicateProof> {
    let witness = TemporalPredicateWitness {
        values: values.to_vec(),
        state_roots: state_roots.to_vec(),
        predicate_type,
        threshold,
    };

    if !witness.is_satisfiable() {
        return None;
    }

    let num_steps = witness.num_steps() as u32;
    let initial_state_root = witness.state_roots[0];
    let final_state_root = *witness.state_roots.last().unwrap();

    let air = TemporalPredicateAir::new(witness);
    let (trace, public_inputs) = generate_dsl_trace(&air.witness);
    let padded_len = trace.len() as u32;

    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(TemporalPredicateProof {
        predicate_type,
        threshold,
        num_steps,
        padded_len,
        initial_state_root,
        final_state_root,
        stark_proof,
    })
}

/// Verify a temporal predicate proof.
///
/// # Soundness contract (post AIR-soundness-audit ce1e2def #3)
///
/// The PI vector is now four elements:
/// `[padded_len, threshold, initial_state_root, final_state_root]`. The
/// verifier reconstructs PIs from the *caller-supplied* expected values
/// (not from the proof's plain-field metadata) and runs `stark::verify`
/// against them. A prover who tampered with any of
/// `proof.threshold` / `proof.initial_state_root` /
/// `proof.final_state_root` after the fact will have those PI slots
/// mismatch the STARK's boundary commitments and STARK verification
/// rejects.
///
/// The plain-field equality pre-checks remain as fast filters that
/// surface clear error messages on the common case of "wrong arguments
/// passed by caller," but they are no longer load-bearing — the STARK
/// boundary commitments are.
///
/// # Bound surface (today)
///
/// - PI[0]=`padded_len`: enforced via row-(N-1) ACCUMULATOR boundary
///   (`accumulator = padded_len`).
/// - PI[1]=`threshold`: row-0 THRESHOLD boundary + inter-row constancy
///   (T3 transition constraint).
/// - PI[2]=`initial_state_root`: row-0 STATE_ROOT boundary.
/// - PI[3]=`final_state_root`: row-(N-1) STATE_ROOT boundary. Padding
///   rows hold a copy of the final real root (see `generate_dsl_trace`)
///   so the boundary catches the final root regardless of padding.
///
/// # Bound by construction (intentionally not in PI)
///
/// - Per-row VALUE: not in PI. The temporal predicate's contract is
///   "predicate held at every step," not "values were specifically
///   X, Y, Z." The per-row `diff = value - threshold` constraint plus
///   bit-decomposition + high-bit-zero forces the predicate's
///   acceptance against the BOUND threshold, which is sufficient. The
///   verifier never reveals per-step values, so identifying them in PI
///   would be a contract change, not a soundness lift.
///
/// # Honest gap acknowledgement
///
/// The state-root binding pins the **first** and **last** roots only.
/// A prover could substitute interior state-root values mid-trace
/// without detection. This is structurally similar to a Merkle
/// commitment to the state-root sequence; if a future caller wants to
/// re-execute a specific intermediate root, the right lift is to add
/// a `state_root_chain_commitment` PI slot (one Poseidon2 chain over
/// the per-row STATE_ROOT column) and bind it via the IVC primitive.
pub fn verify_temporal_predicate(
    proof: &TemporalPredicateProof,
    threshold: BabyBear,
    num_steps: u32,
    initial_state_root: BabyBear,
    final_state_root: BabyBear,
) -> bool {
    // Fast pre-checks on plain proof fields. Not load-bearing post-
    // audit — the STARK below is the authoritative gate.
    if proof.threshold != threshold {
        return false;
    }
    if proof.num_steps != num_steps {
        return false;
    }
    if proof.initial_state_root != initial_state_root {
        return false;
    }
    if proof.final_state_root != final_state_root {
        return false;
    }

    let padded_len = proof.padded_len;

    // Sanity: padded_len must be >= num_steps and a power of two.
    if padded_len < num_steps || !padded_len.is_power_of_two() {
        return false;
    }

    // Reconstruct PI from CALLER-supplied values (not from proof.*).
    // Tampering on any of proof.threshold / proof.initial_state_root /
    // proof.final_state_root will produce a PI that mismatches the
    // STARK's boundary commitments and `stark::verify` rejects.
    let public_inputs = vec![
        BabyBear::new(padded_len),
        threshold,
        initial_state_root,
        final_state_root,
    ];

    // Reconstruct a dummy witness for the AIR shape.
    let dummy_witness = TemporalPredicateWitness {
        values: vec![BabyBear::ZERO; num_steps as usize],
        state_roots: vec![BabyBear::ZERO; num_steps as usize],
        predicate_type: proof.predicate_type,
        threshold,
    };
    let air = TemporalPredicateAir::new(dummy_witness);
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Intent integration: Temporal predicate requirements
// ─────────────────────────────────────────────────────────────────────────────

/// A temporal predicate requirement for intent matching.
///
/// Specifies that a counterparty must prove a property held continuously
/// for a minimum duration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemporalPredicateRequirement {
    /// The attribute being checked (e.g., "balance", "reputation").
    pub attribute: String,
    /// The predicate type (e.g., GTE for "at least").
    pub predicate_type: PredicateType,
    /// The threshold value.
    pub threshold: u64,
    /// Minimum number of consecutive steps the predicate must hold.
    pub min_duration_steps: u64,
}

impl TemporalPredicateRequirement {
    /// Check whether a temporal predicate proof satisfies this requirement.
    pub fn is_satisfied_by(&self, proof: &TemporalPredicateProof) -> bool {
        if proof.predicate_type != self.predicate_type {
            return false;
        }
        if proof.threshold.as_u32() < self.threshold as u32 {
            return false;
        }
        if (proof.num_steps as u64) < self.min_duration_steps {
            return false;
        }
        true
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Plonky3-native temporal predicate AIR (re-exported from legacy)
// ─────────────────────────────────────────────────────────────────────────────

/// Re-export the Plonky3-based temporal AIR from the legacy module.
/// The P3 variant has its own separate AIR implementation that uses Plonky3's
/// native AirBuilder and is independent of the DSL system.
#[cfg(feature = "plonky3")]
pub mod p3_temporal {
    pub use crate::temporal_predicate_air::p3_temporal::*;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: generate state roots for testing (sequential hashes).
    fn test_state_roots(n: usize) -> Vec<BabyBear> {
        (0..n).map(|i| BabyBear::new(1000 + i as u32)).collect()
    }

    // =========================================================================
    // DSL struct basic checks
    // =========================================================================

    #[test]
    fn test_dsl_circuit_struct_exists() {
        let circuit = TemporalPredicateDsl;
        // Width grew 37 → 38 with the STATE_ROOT column addition
        // (AIR-soundness-audit ce1e2def #3).
        assert_eq!(circuit.width(), DSL_TRACE_WIDTH);
        assert_eq!(DSL_TRACE_WIDTH, 38);
        assert_eq!(circuit.constraint_degree(), 2);
        assert_eq!(circuit.air_name(), "dregg-temporal_predicate_dsl-v1");
    }

    #[test]
    fn test_dsl_circuit_valid_trace() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);
        assert_eq!(trace.len(), 4); // next power of 2

        let alpha = BabyBear::new(7);
        for i in 0..trace.len() - 1 {
            let result = circuit.eval_constraints(&trace[i], &trace[i + 1], &public_inputs, alpha);
            assert_eq!(
                result,
                BabyBear::ZERO,
                "Constraint nonzero at row {i} (valid trace)"
            );
        }
    }

    #[test]
    fn test_dsl_circuit_invalid_value_below_threshold() {
        let circuit = TemporalPredicateDsl;

        let values: Vec<BabyBear> = vec![100, 30, 100].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);

        let alpha = BabyBear::new(7);
        let row1_result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            row1_result,
            BabyBear::ZERO,
            "Constraint should be nonzero at row 1 where value < threshold"
        );
    }

    #[test]
    fn test_dsl_circuit_transition_detects_gap() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (mut trace, public_inputs) = generate_dsl_trace(&witness);

        // Corrupt row 2: accumulator gap
        trace[2][ACCUMULATOR] = BabyBear::new(4);
        trace[2][ACC_PLUS_ONE] = BabyBear::new(5);

        let alpha = BabyBear::new(7);
        let result = circuit.eval_constraints(&trace[1], &trace[2], &public_inputs, alpha);
        assert_ne!(
            result,
            BabyBear::ZERO,
            "Transition constraint should be nonzero when accumulator has a gap"
        );

        // Row 0 -> Row 1 still fine
        let result_01 = circuit.eval_constraints(&trace[0], &trace[1], &public_inputs, alpha);
        assert_eq!(result_01, BabyBear::ZERO);
    }

    // =========================================================================
    // Full prove/verify cycle (matches old API)
    // =========================================================================

    #[test]
    fn test_temporal_gte_all_pass() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![150, 200, 300, 100, 500, 120, 999, 101, 100, 250]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(10);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(proof.is_some(), "All values >= 100, proof should succeed");

        let proof = proof.unwrap();
        assert_eq!(proof.num_steps, 10);
        assert_eq!(proof.threshold, threshold);

        let valid =
            verify_temporal_predicate(&proof, threshold, 10, state_roots[0], state_roots[9]);
        assert!(valid, "Verification should pass");
    }

    #[test]
    fn test_temporal_gte_edge_exactly_at_threshold() {
        let threshold = BabyBear::new(50);
        let values: Vec<BabyBear> = vec![50; 5].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_some(),
            "Values exactly at threshold should pass GTE"
        );
    }

    #[test]
    fn test_temporal_gte_dip_below_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![150, 200, 300, 100, 500, 99, 999, 101, 100, 250]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(10);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_none(),
            "Value 99 < 100 at step 5 should cause proof generation to fail"
        );
    }

    #[test]
    fn test_verify_fails_wrong_threshold() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid =
            verify_temporal_predicate(&proof, BabyBear::new(50), 3, state_roots[0], state_roots[2]);
        assert!(!valid, "Wrong threshold should fail verification");
    }

    #[test]
    fn test_verify_fails_wrong_num_steps() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid = verify_temporal_predicate(&proof, threshold, 5, state_roots[0], state_roots[2]);
        assert!(!valid, "Wrong num_steps should fail verification");
    }

    #[test]
    fn test_verify_fails_wrong_state_root() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let valid =
            verify_temporal_predicate(&proof, threshold, 3, BabyBear::new(99999), state_roots[2]);
        assert!(!valid, "Wrong initial state root should fail verification");

        let valid =
            verify_temporal_predicate(&proof, threshold, 3, state_roots[0], BabyBear::new(99999));
        assert!(!valid, "Wrong final state root should fail verification");
    }

    #[test]
    fn test_temporal_lte_all_pass() {
        let threshold = BabyBear::new(500);
        let values: Vec<BabyBear> = vec![100, 200, 500, 300, 50]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Lte, threshold);
        assert!(proof.is_some(), "All values <= 500, should succeed");
    }

    #[test]
    fn test_temporal_lte_violation() {
        let threshold = BabyBear::new(500);
        let values: Vec<BabyBear> = vec![100, 200, 501, 300, 50]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(5);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Lte, threshold);
        assert!(proof.is_none(), "Value 501 > 500 should cause failure");
    }

    #[test]
    fn test_temporal_gt_all_pass() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![101, 200, 999].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gt, threshold);
        assert!(proof.is_some(), "All values > 100, should succeed");
    }

    #[test]
    fn test_temporal_gt_equal_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![101, 100, 200].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gt, threshold);
        assert!(
            proof.is_none(),
            "Value 100 is not > 100, should fail for GT"
        );
    }

    #[test]
    fn test_temporal_single_step() {
        let threshold = BabyBear::new(50);
        let values = vec![BabyBear::new(100)];
        let state_roots = vec![BabyBear::new(1000)];

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();
        assert_eq!(proof.num_steps, 1);

        let valid = verify_temporal_predicate(&proof, threshold, 1, state_roots[0], state_roots[0]);
        assert!(valid);
    }

    #[test]
    fn test_temporal_empty_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![];
        let state_roots: Vec<BabyBear> = vec![];

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(proof.is_none(), "Empty sequence should not produce a proof");
    }

    #[test]
    fn test_temporal_mismatched_lengths_fails() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 300].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);

        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold);
        assert!(
            proof.is_none(),
            "Mismatched lengths should not produce a proof"
        );
    }

    #[test]
    fn test_temporal_requirement_satisfied() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200; 30].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(30);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let requirement = TemporalPredicateRequirement {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };

        assert!(
            requirement.is_satisfied_by(&proof),
            "30 steps >= 100 should satisfy requirement"
        );
    }

    #[test]
    fn test_temporal_requirement_insufficient_duration() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200; 10].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(10);

        let proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold).unwrap();

        let requirement = TemporalPredicateRequirement {
            attribute: "balance".to_string(),
            predicate_type: PredicateType::Gte,
            threshold: 100,
            min_duration_steps: 30,
        };

        assert!(
            !requirement.is_satisfied_by(&proof),
            "10 steps < 30 required should not satisfy"
        );
    }

    #[test]
    fn test_temporal_soundness_cannot_fabricate_duration() {
        let threshold = BabyBear::new(100);
        let state_roots_3 = test_state_roots(3);

        let values_3: Vec<BabyBear> = vec![200, 150, 300].into_iter().map(BabyBear::new).collect();
        let proof_3 =
            prove_temporal_predicate(&values_3, &state_roots_3, PredicateType::Gte, threshold)
                .expect("3 valid steps should produce a proof");
        assert_eq!(proof_3.num_steps, 3);

        let state_roots_10 = test_state_roots(10);
        let bogus_verify = verify_temporal_predicate(
            &proof_3,
            threshold,
            10,
            state_roots_10[0],
            state_roots_10[9],
        );
        assert!(
            !bogus_verify,
            "A 3-step proof must NOT verify as a 10-step proof"
        );

        let valid =
            verify_temporal_predicate(&proof_3, threshold, 3, state_roots_3[0], state_roots_3[2]);
        assert!(valid, "3-step proof should verify with correct parameters");
    }

    // =========================================================================
    // DSL STARK full prove/verify
    // =========================================================================

    #[test]
    fn test_dsl_stark_prove_verify() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);

        let proof = stark::prove(&circuit, &trace, &public_inputs);
        let result = stark::verify(&circuit, &proof, &public_inputs);
        assert!(
            result.is_ok(),
            "STARK verify failed on valid trace: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_dsl_stark_rejects_wrong_public_inputs() {
        let circuit = TemporalPredicateDsl;

        let values = vec![BabyBear::new(100); 3];
        let state_roots = test_state_roots(3);
        let witness = TemporalPredicateWitness {
            values,
            state_roots,
            predicate_type: PredicateType::Gte,
            threshold: BabyBear::new(50),
        };

        let (trace, public_inputs) = generate_dsl_trace(&witness);
        let proof = stark::prove(&circuit, &trace, &public_inputs);

        let wrong_pi = vec![BabyBear::new(8)];
        let result = stark::verify(&circuit, &proof, &wrong_pi);
        assert!(result.is_err(), "Should reject proof with wrong num_steps");
    }

    // ─────────────────────────────────────────────────────────────────
    // AIR-soundness-audit (ce1e2def) finding #3 adversarial tests.
    //
    // Pre-audit attack (verbatim from the audit doc):
    //   - Attacker constructs a witness with threshold=0 (trivially
    //     satisfiable) and arbitrary values + arbitrary state-roots.
    //   - stark::prove succeeds.
    //   - Attacker mutates proof.threshold / proof.initial_state_root /
    //     proof.final_state_root after the fact.
    //   - Verifier wrapper compared the mutated fields against
    //     themselves and accepted.
    //
    // Post-audit: PI[1]=threshold, PI[2]=initial_state_root,
    // PI[3]=final_state_root are bound into STARK boundaries; mutating
    // the proof's plain-field metadata changes nothing about the STARK,
    // so the verifier reconstructs the PI from the caller's expected
    // values and STARK verify rejects.
    // ─────────────────────────────────────────────────────────────────

    /// Reconstruct the threshold-forge attack: honest prove for
    /// threshold=0, then claim threshold=99999. The verifier's
    /// fast-pre-check guards against this, but to *bypass* the fast
    /// check the attacker could also lie to the verifier; we simulate
    /// by passing the LIED threshold as the verifier's expectation.
    /// The STARK then catches it because PI[1] mismatches the row-0
    /// THRESHOLD boundary commitment.
    #[test]
    fn audit_attack_threshold_forge_rejected_by_stark_binding() {
        // Honestly prove for threshold=0 (trivially satisfiable).
        let honest_threshold = BabyBear::new(0);
        let values: Vec<BabyBear> = vec![10, 20, 30].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);
        let mut proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, honest_threshold)
                .expect("honest threshold=0 prove succeeds");

        // Tamper the plain field — claim threshold=99999.
        let forged_threshold = BabyBear::new(99999);
        proof.threshold = forged_threshold;

        // Now: a verifier who *also* lies (passing forged_threshold as
        // expected) will fail the STARK check. PI[1] reconstruction =
        // forged_threshold, but the STARK boundary committed to 0.
        let valid =
            verify_temporal_predicate(&proof, forged_threshold, 3, state_roots[0], state_roots[2]);
        assert!(
            !valid,
            "tampered threshold must be rejected by STARK PI[1] boundary commitment"
        );
    }

    #[test]
    fn audit_attack_initial_state_root_forge_rejected_by_stark_binding() {
        // Honest prove with real state roots.
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 300, 400].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);
        let mut proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold)
                .expect("honest prove succeeds");

        // Forge the initial state root.
        let forged_initial = BabyBear::new(123456);
        proof.initial_state_root = forged_initial;

        // A verifier who consumes proof.initial_state_root as truth
        // would normally be safe via the plain-field check, but to
        // simulate the *fully-coordinated* attack we pass the forged
        // value as expected. The STARK then rejects via PI[2] vs row-0
        // STATE_ROOT boundary mismatch.
        let valid = verify_temporal_predicate(&proof, threshold, 3, forged_initial, state_roots[2]);
        assert!(
            !valid,
            "tampered initial_state_root must be rejected by STARK PI[2] boundary commitment"
        );
    }

    #[test]
    fn audit_attack_final_state_root_forge_rejected_by_stark_binding() {
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 300, 400].into_iter().map(BabyBear::new).collect();
        let state_roots = test_state_roots(3);
        let mut proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold)
                .expect("honest prove succeeds");

        let forged_final = BabyBear::new(789012);
        proof.final_state_root = forged_final;

        let valid = verify_temporal_predicate(&proof, threshold, 3, state_roots[0], forged_final);
        assert!(
            !valid,
            "tampered final_state_root must be rejected by STARK PI[3] boundary commitment"
        );
    }

    /// Sanity: an honestly-produced proof still verifies under the
    /// post-audit PI layout. (Regression guard for the boundary /
    /// constancy constraint additions.)
    #[test]
    fn audit_honest_proof_still_verifies_under_new_pi_layout() {
        let threshold = BabyBear::new(50);
        let values: Vec<BabyBear> = vec![60, 70, 80, 90, 100]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let state_roots = test_state_roots(5);
        let proof = prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold)
            .expect("honest prove succeeds");
        assert!(verify_temporal_predicate(
            &proof,
            threshold,
            5,
            state_roots[0],
            state_roots[4]
        ));
    }
}
