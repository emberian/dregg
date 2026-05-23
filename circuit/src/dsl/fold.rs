//! DSL-native fold proving and verification.
//!
//! This module provides production prove/verify functions for the fold AIR using
//! the DSL `CircuitDescriptor` + `DslCircuit` infrastructure. It replaces the
//! hand-written `FoldStarkAir` from `circuit/src/fold_air.rs`.
//!
//! # Completeness vs. hand-written AIR
//!
//! The DSL version covers:
//! - Attenuation step (removal rows + summary row)
//! - Commitment hash binding (fact_hash_correct via Hash constraint)
//! - Root transition hash binding (pi[4])
//! - Removal count increment (transition constraint)
//! - Old/new root consistency (PiBinding)
//! - Check count binding (boundary constraint on last row)
//! - Checks commitment zero-when-no-checks (boundary-level enforcement)
//!
//! # Public Input Layout
//!
//! - pi[0]: old_root
//! - pi[1]: new_root
//! - pi[2]: total_removal_count
//! - pi[3]: total_check_count
//! - pi[4]: root_transition_hash
//! - pi[5]: checks_commitment_narrow

use crate::binding::WideHash;
use crate::field::BabyBear;
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
};

// ============================================================================
// Column indices (compatible with circuit/src/fold_types.rs col:: module)
// ============================================================================

pub mod col {
    pub const ROW_TYPE: usize = 0;
    pub const FACT_HASH: usize = 1;
    pub const MEMBERSHIP_ROOT: usize = 2;
    pub const OLD_ROOT: usize = 3;
    pub const NEW_ROOT: usize = 4;
    pub const REMOVAL_COUNT: usize = 5;
    pub const CHECK_COUNT: usize = 6;
    pub const FACT_PRED: usize = 7;
    pub const FACT_TERM_START: usize = 8;
    // col 9, 10: FACT_TERM_START+1, FACT_TERM_START+2
    pub const HASH_VALID: usize = 11;
    /// Auxiliary column: holds `removal_count + 1` for transition constraint.
    pub const REMOVAL_COUNT_PLUS_ONE: usize = 12;
}

/// Trace width for the DSL fold AIR (13 columns: 12 original + 1 auxiliary).
pub const FOLD_DSL_WIDTH: usize = 13;

/// Number of public inputs: [old_root, new_root, removal_count, check_count, transition_hash, checks_narrow].
pub const FOLD_DSL_PI_COUNT: usize = 6;

// ============================================================================
// Witness types (shared, moved from fold_types)
// ============================================================================

pub use crate::fold_types::{
    FoldAir, FoldWitness, RemovedFact, build_membership_proof, build_shared_tree,
    compute_root_transition_hash, compute_test_checks_commitment, create_test_fold,
    verify_root_transition,
};

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the production fold CircuitDescriptor.
///
/// This is the DSL equivalent of `FoldStarkAir`. It expresses the same constraints
/// using the declarative `ConstraintExpr` types, enabling the generic `DslCircuit`
/// to evaluate them.
///
/// Constraints:
/// 1. `row_type_binary`: ROW_TYPE * (ROW_TYPE - 1) == 0
/// 2. `hash_valid_binary`: HASH_VALID * (HASH_VALID - 1) == 0
/// 3. `membership_root_matches_old_root` (gated by is_removal):
///    (1 - ROW_TYPE) * (MEMBERSHIP_ROOT - OLD_ROOT) == 0
/// 4. `removal_hash_required` (gated by is_removal):
///    (1 - ROW_TYPE) * (1 - HASH_VALID) == 0
/// 5. `fact_hash_correct` (gated by is_removal):
///    (1 - ROW_TYPE) * (hash_fact(FACT_PRED, terms) - FACT_HASH) == 0
/// 6. `old_root_consistent`: OLD_ROOT - pi[0] == 0
/// 7. `new_root_consistent`: NEW_ROOT - pi[1] == 0
/// 8. `removal_count_increment` (gated transition):
///    (1 - ROW_TYPE) * (next[REMOVAL_COUNT] - local[REMOVAL_COUNT_PLUS_ONE]) == 0
/// 9. `root_transition_binding` (gated on is_summary):
///    ROW_TYPE * (MEMBERSHIP_ROOT - pi[4]) == 0
///
/// Boundary constraints:
/// - First row: OLD_ROOT == pi[0]
/// - First row: NEW_ROOT == pi[1]
/// - Last row: ROW_TYPE == 1 (must be summary)
/// - Last row: REMOVAL_COUNT == pi[2]
/// - Last row: CHECK_COUNT == pi[3]
/// - Last row: MEMBERSHIP_ROOT == pi[4] (transition hash binding)
pub fn fold_circuit_descriptor() -> CircuitDescriptor {
    let columns = vec![
        ColumnDef { name: "row_type".into(), index: col::ROW_TYPE, kind: ColumnKind::Selector },
        ColumnDef { name: "fact_hash".into(), index: col::FACT_HASH, kind: ColumnKind::Hash },
        ColumnDef { name: "membership_root".into(), index: col::MEMBERSHIP_ROOT, kind: ColumnKind::Hash },
        ColumnDef { name: "old_root".into(), index: col::OLD_ROOT, kind: ColumnKind::Value },
        ColumnDef { name: "new_root".into(), index: col::NEW_ROOT, kind: ColumnKind::Value },
        ColumnDef { name: "removal_count".into(), index: col::REMOVAL_COUNT, kind: ColumnKind::Value },
        ColumnDef { name: "check_count".into(), index: col::CHECK_COUNT, kind: ColumnKind::Value },
        ColumnDef { name: "fact_pred".into(), index: col::FACT_PRED, kind: ColumnKind::Value },
        ColumnDef { name: "fact_term_0".into(), index: col::FACT_TERM_START, kind: ColumnKind::Value },
        ColumnDef { name: "fact_term_1".into(), index: col::FACT_TERM_START + 1, kind: ColumnKind::Value },
        ColumnDef { name: "fact_term_2".into(), index: col::FACT_TERM_START + 2, kind: ColumnKind::Value },
        ColumnDef { name: "hash_valid".into(), index: col::HASH_VALID, kind: ColumnKind::Binary },
        ColumnDef { name: "removal_count_plus_one".into(), index: col::REMOVAL_COUNT_PLUS_ONE, kind: ColumnKind::Value },
    ];

    // Constraint 1: row_type is binary
    let c_row_type_binary = ConstraintExpr::Binary { col: col::ROW_TYPE };

    // Constraint 2: hash_valid is binary
    let c_hash_valid_binary = ConstraintExpr::Binary { col: col::HASH_VALID };

    // Constraint 3: membership_root == old_root WHEN is_removal (row_type == 0)
    let c_membership_root = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Equality {
            col_a: col::MEMBERSHIP_ROOT,
            col_b: col::OLD_ROOT,
        }),
    };

    // Constraint 4: removal_hash_required: when is_removal, hash_valid must be 1.
    // (1 - ROW_TYPE) * (1 - HASH_VALID) == 0
    let c_removal_hash_required = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: col::HASH_VALID,
            // Inner evaluates to 1 when hash_valid == 0; we need the product to be zero.
            // (1-ROW_TYPE)*(1-HASH_VALID) == 0 is best expressed as a Polynomial:
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    crate::dsl::circuit::PolyTerm { coeff: BabyBear::ONE, col_indices: vec![] },
                ],
            }),
        }),
    };

    // Constraint 5: fact_hash_correct (gated by is_removal)
    // (1 - ROW_TYPE) * (hash_fact(FACT_PRED, [term0, term1, term2]) - FACT_HASH) == 0
    let c_fact_hash = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::FACT_HASH,
            input_cols: vec![
                col::FACT_PRED,
                col::FACT_TERM_START,
                col::FACT_TERM_START + 1,
                col::FACT_TERM_START + 2,
            ],
        }),
    };

    // Constraint 6: OLD_ROOT == pi[0]
    let c_old_root_pi = ConstraintExpr::PiBinding {
        col: col::OLD_ROOT,
        pi_index: 0,
    };

    // Constraint 7: NEW_ROOT == pi[1]
    let c_new_root_pi = ConstraintExpr::PiBinding {
        col: col::NEW_ROOT,
        pi_index: 1,
    };

    // Constraint 8: removal_count_increment (transition).
    // (1 - ROW_TYPE) * (next[REMOVAL_COUNT] - local[REMOVAL_COUNT_PLUS_ONE]) == 0
    let c_removal_count_transition = ConstraintExpr::InvertedGated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::Transition {
            next_col: col::REMOVAL_COUNT,
            local_col: col::REMOVAL_COUNT_PLUS_ONE,
        }),
    };

    // Constraint 9: root_transition_binding on summary rows.
    // ROW_TYPE * (MEMBERSHIP_ROOT - pi[4]) == 0
    let c_transition_binding = ConstraintExpr::Gated {
        selector_col: col::ROW_TYPE,
        inner: Box::new(ConstraintExpr::PiBinding {
            col: col::MEMBERSHIP_ROOT,
            pi_index: 4,
        }),
    };

    let constraints = vec![
        c_row_type_binary,
        c_hash_valid_binary,
        c_membership_root,
        c_removal_hash_required,
        c_fact_hash,
        c_old_root_pi,
        c_new_root_pi,
        c_removal_count_transition,
        c_transition_binding,
    ];

    let boundaries = vec![
        // First row: old_root == pi[0]
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::OLD_ROOT, pi_index: 0 },
        // First row: new_root == pi[1]
        BoundaryDef::PiBinding { row: BoundaryRow::First, col: col::NEW_ROOT, pi_index: 1 },
        // Last row: row_type == 1 (summary)
        BoundaryDef::Fixed { row: BoundaryRow::Last, col: col::ROW_TYPE, value: BabyBear::ONE },
        // Last row: removal_count == pi[2]
        BoundaryDef::PiBinding { row: BoundaryRow::Last, col: col::REMOVAL_COUNT, pi_index: 2 },
        // Last row: check_count == pi[3]
        BoundaryDef::PiBinding { row: BoundaryRow::Last, col: col::CHECK_COUNT, pi_index: 3 },
        // Last row: membership_root == pi[4] (transition hash)
        BoundaryDef::PiBinding { row: BoundaryRow::Last, col: col::MEMBERSHIP_ROOT, pi_index: 4 },
    ];

    CircuitDescriptor {
        name: "pyana-fold-dsl-v2".into(),
        trace_width: FOLD_DSL_WIDTH,
        max_degree: 3, // InvertedGated(Hash) or InvertedGated(InvertedGated(...)) reaches degree 3
        columns,
        constraints,
        boundaries,
        public_input_count: FOLD_DSL_PI_COUNT,
    }
}

/// Create a DslCircuit from the fold descriptor.
pub fn fold_dsl_circuit() -> DslCircuit {
    DslCircuit::new(fold_circuit_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate an execution trace and public inputs from a `FoldWitness`.
///
/// This produces the same semantics as `FoldAir::generate_trace()` but for the
/// DSL-native trace layout (13 columns including the auxiliary REMOVAL_COUNT_PLUS_ONE).
pub fn generate_fold_trace(witness: &FoldWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let w = witness;

    let root_transition_hash = if !w.removed_facts.is_empty() {
        verify_root_transition(w).unwrap_or(BabyBear::ZERO)
    } else {
        compute_root_transition_hash(w.old_root, w.new_root, &[], &w.added_checks_commitment)
    };

    let mut trace = Vec::new();

    for (i, fact) in w.removed_facts.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; FOLD_DSL_WIDTH];
        row[col::ROW_TYPE] = BabyBear::ZERO;
        row[col::FACT_HASH] = fact.hash();
        row[col::MEMBERSHIP_ROOT] = fact.verify_membership(w.old_root).unwrap_or(BabyBear::ZERO);
        row[col::OLD_ROOT] = w.old_root;
        row[col::NEW_ROOT] = w.new_root;
        row[col::REMOVAL_COUNT] = BabyBear::new((i + 1) as u32);
        row[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
        row[col::FACT_PRED] = fact.predicate;
        row[col::FACT_TERM_START] = fact.terms[0];
        row[col::FACT_TERM_START + 1] = fact.terms[1];
        row[col::FACT_TERM_START + 2] = fact.terms[2];
        row[col::HASH_VALID] = BabyBear::ONE;
        // Auxiliary: next row's expected removal_count
        row[col::REMOVAL_COUNT_PLUS_ONE] = BabyBear::new((i + 2) as u32);
        trace.push(row);
    }

    // Summary row
    let mut summary = vec![BabyBear::ZERO; FOLD_DSL_WIDTH];
    summary[col::ROW_TYPE] = BabyBear::ONE;
    summary[col::MEMBERSHIP_ROOT] = root_transition_hash;
    summary[col::OLD_ROOT] = w.old_root;
    summary[col::NEW_ROOT] = w.new_root;
    summary[col::REMOVAL_COUNT] = BabyBear::new(w.removed_facts.len() as u32);
    summary[col::CHECK_COUNT] = BabyBear::new(w.num_added_checks as u32);
    summary[col::HASH_VALID] = BabyBear::ONE;
    // On the summary row, REMOVAL_COUNT_PLUS_ONE matches REMOVAL_COUNT (no transition enforced
    // because ROW_TYPE=1 gates it off).
    summary[col::REMOVAL_COUNT_PLUS_ONE] = BabyBear::new(w.removed_facts.len() as u32);
    trace.push(summary);

    // Fix the last removal row's REMOVAL_COUNT_PLUS_ONE to point at the summary row's count.
    // The summary row's REMOVAL_COUNT equals total removals, which equals the last removal row's
    // count (since it's the Nth removal). So no fix needed: row[i].REMOVAL_COUNT_PLUS_ONE = i+2,
    // and summary.REMOVAL_COUNT = N. For the last removal row (i=N-1), REMOVAL_COUNT_PLUS_ONE = N,
    // and the next row (summary) has REMOVAL_COUNT = N. Correct.

    // Pad trace to power-of-two (>= 2 rows required by STARK prover)
    let padded_len = trace.len().next_power_of_two().max(2);
    while trace.len() < padded_len {
        trace.push(trace.last().unwrap().clone());
    }

    let fact_hashes: Vec<BabyBear> = w.removed_facts.iter().map(|f| f.hash()).collect();
    let expected_rt = compute_root_transition_hash(
        w.old_root,
        w.new_root,
        &fact_hashes,
        &w.added_checks_commitment,
    );
    let narrow_checks = w.added_checks_commitment.to_narrow();
    let public_inputs = vec![
        w.old_root,
        w.new_root,
        BabyBear::new(w.removed_facts.len() as u32),
        BabyBear::new(w.num_added_checks as u32),
        expected_rt,
        narrow_checks,
    ];

    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a DSL-native STARK proof for a fold step.
///
/// This replaces `prove_fold_stark` from `circuit/src/fold_types.rs`.
pub fn prove_fold_dsl(witness: &FoldWitness) -> Option<StarkProof> {
    let circuit = fold_dsl_circuit();
    let (trace, public_inputs) = generate_fold_trace(witness);

    // Validate: delta must be nonempty (at least one removal or check)
    if witness.removed_facts.is_empty() && witness.num_added_checks == 0 {
        return None;
    }

    // Validate: checks_commitment must be ZERO when num_added_checks == 0
    if witness.num_added_checks == 0 && witness.added_checks_commitment != WideHash::ZERO {
        return None;
    }

    Some(stark::prove(&circuit, &trace, &public_inputs))
}

/// Verify a DSL-native STARK proof for a fold step.
///
/// This replaces `verify_fold_stark` from `circuit/src/fold_types.rs`.
pub fn verify_fold_dsl(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let circuit = fold_dsl_circuit();

    // Validate checks_commitment_zero_when_no_checks at the verifier level.
    // pi[3] == check_count, pi[5] == checks_commitment_narrow.
    if public_inputs.len() >= 6 {
        if public_inputs[3] == BabyBear::ZERO && public_inputs[5] != BabyBear::ZERO {
            return Err("non-zero checks commitment with zero check count".to_string());
        }
    }

    stark::verify(&circuit, proof, public_inputs)
}

// ============================================================================
// Backward-compatible aliases
// ============================================================================

/// Backward-compatible alias: prove a fold step using the DSL-native circuit.
pub fn prove_fold_stark(witness: &FoldWitness) -> Option<StarkProof> {
    prove_fold_dsl(witness)
}

/// Backward-compatible alias: verify a fold step using the DSL-native circuit.
pub fn verify_fold_stark(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    verify_fold_dsl(proof, public_inputs)
}
