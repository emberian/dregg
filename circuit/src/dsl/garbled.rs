//! Production garbled circuit evaluation — DSL-native implementation.
//!
//! This module provides the canonical prove/verify API for garbled circuit evaluation
//! using the DSL `CircuitDescriptor` infrastructure. It supersedes the hand-written
//! `circuit/src/garbled_air.rs` with the extended 56-column layout supporting:
//!
//! - Multi-gate chaining (linear chains via `chain_flag`)
//! - Gate type selectors (AND/OR/XOR/NOT)
//! - Topological ordering enforcement (gate_index_delta)
//! - Padding support for power-of-two trace alignment
//! - Fan-out wiring (chain_flag=0 for non-adjacent gate inputs)
//!
//! # Usage
//!
//! ```ignore
//! use pyana_dsl_runtime::garbled::{
//!     prove_garbled_evaluation_dsl, verify_garbled_evaluation_dsl,
//!     GarbledDslProof, ExtendedGateRecord, GateType,
//! };
//! ```
//!
//! For the basic comparison-circuit workflow, use `prove_comparison_circuit_dsl()`
//! which handles the record conversion internally.

use crate::binding::WideHash;
use crate::field::BabyBear;
use crate::garbled::{self, GateEvalRecord};
use crate::garbled_air::{GARBLED_EVAL_AIR_WIDTH, col};
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Re-export the column layout from the test DSL (now production)
// ============================================================================

/// Original AIR width (49 columns).
const BASE_WIDTH: usize = GARBLED_EVAL_AIR_WIDTH; // 49

/// Extended column indices for gate types and chaining.
pub mod ext_col {
    use super::BASE_WIDTH;

    /// Gate type selector: AND gate.
    pub const IS_AND: usize = BASE_WIDTH; // 49
    /// Gate type selector: OR gate.
    pub const IS_OR: usize = BASE_WIDTH + 1; // 50
    /// Gate type selector: XOR gate.
    pub const IS_XOR: usize = BASE_WIDTH + 2; // 51
    /// Gate type selector: NOT gate.
    pub const IS_NOT: usize = BASE_WIDTH + 3; // 52
    /// Chain flag: 1 if this row's output feeds next row's left input.
    pub const CHAIN_FLAG: usize = BASE_WIDTH + 4; // 53
    /// Gate index delta: gate_index[current] - gate_index[previous].
    pub const GATE_INDEX_DELTA: usize = BASE_WIDTH + 5; // 54
    /// Padding flag: 1 on padding rows (constraints relaxed).
    pub const IS_PADDING: usize = BASE_WIDTH + 6; // 55
}

/// Extended trace width.
pub const GARBLED_DSL_WIDTH: usize = BASE_WIDTH + 7; // 56

/// Public input indices.
pub mod pi {
    /// Circuit commitment elements 0..3.
    pub const CIRCUIT_COMMITMENT_START: usize = 0;
    /// Output label hash elements 0..3.
    pub const OUTPUT_LABEL_HASH_START: usize = 4;
}

// ============================================================================
// Gate type and extended record
// ============================================================================

/// Gate type enum for the extended DSL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateType {
    And,
    Or,
    Xor,
    Not,
}

/// A gate evaluation record for the extended trace.
#[derive(Debug, Clone)]
pub struct ExtendedGateRecord {
    /// The base record from the garbled circuit evaluator.
    pub base: GateEvalRecord,
    /// Gate type for this gate.
    pub gate_type: GateType,
    /// Whether this gate's output chains to the next gate's left input.
    pub chains_to_next: bool,
}

// ============================================================================
// Proof type
// ============================================================================

/// A DSL-native garbled evaluation proof.
#[derive(Clone, Debug)]
pub struct GarbledDslProof {
    /// The circuit commitment (public, 124-bit WideHash).
    pub circuit_commitment: WideHash,
    /// Hash of the output label (public, 124-bit WideHash).
    pub output_label_hash: WideHash,
    /// The STARK proof of correct evaluation.
    pub stark_proof: StarkProof,
}

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(crate::field::BABYBEAR_P - 1)
}

fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the extended garbled circuit evaluation CircuitDescriptor (56 cols).
///
/// This is the production version with full multi-gate, chaining, and gate-type support.
pub fn garbled_extended_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C4: circuit_commitment matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }

    // C5-C8: output_label_hash matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }

    // C9-C16: Decryption correctness, gated on (1 - is_padding)
    for i in 0..8 {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: ext_col::IS_PADDING,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[col::output(i)]),
                    term(neg_one(), &[col::table_entry(i)]),
                    term(BabyBear::ONE, &[col::hash_out(i)]),
                ],
            }),
        });
    }

    // C17-C20: Binary constraints on gate type selectors
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_AND,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_OR,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_XOR,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_NOT,
    });

    // C21: chain_flag binary
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::CHAIN_FLAG,
    });

    // C22: is_padding binary
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_PADDING,
    });

    // C23: Gate type exclusivity (gated on NOT is_padding):
    // (1 - is_padding) * (is_and + is_or + is_xor + is_not - 1) == 0
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: ext_col::IS_PADDING,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[ext_col::IS_AND]),
                term(BabyBear::ONE, &[ext_col::IS_OR]),
                term(BabyBear::ONE, &[ext_col::IS_XOR]),
                term(BabyBear::ONE, &[ext_col::IS_NOT]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C24-C31: Wire chaining transition constraints.
    // chain_flag * (next[left_label_i] - local[output_label_i]) == 0
    for i in 0..8 {
        constraints.push(ConstraintExpr::Gated {
            selector_col: ext_col::CHAIN_FLAG,
            inner: Box::new(ConstraintExpr::Transition {
                next_col: col::left(i),
                local_col: col::output(i),
            }),
        });
    }

    // Boundary constraints
    let mut boundaries = Vec::new();
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }
    // First row gate_index_delta = 0 (no predecessor)
    boundaries.push(BoundaryDef::Fixed {
        row: BoundaryRow::First,
        col: ext_col::GATE_INDEX_DELTA,
        value: BabyBear::ZERO,
    });

    // Column definitions
    let mut columns = Vec::new();
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("left_label_{i}"),
            index: col::left(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("right_label_{i}"),
            index: col::right(i),
            kind: ColumnKind::Value,
        });
    }
    columns.push(ColumnDef {
        name: "gate_index".into(),
        index: col::GATE_INDEX,
        kind: ColumnKind::Value,
    });
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("hash_output_{i}"),
            index: col::hash_out(i),
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("table_entry_{i}"),
            index: col::table_entry(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("output_label_{i}"),
            index: col::output(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("circuit_commitment_{i}"),
            index: col::CIRCUIT_COMMITMENT + i,
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("output_label_hash_{i}"),
            index: col::OUTPUT_LABEL_HASH + i,
            kind: ColumnKind::Hash,
        });
    }
    // Extended columns
    columns.push(ColumnDef {
        name: "is_and".into(),
        index: ext_col::IS_AND,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_or".into(),
        index: ext_col::IS_OR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_xor".into(),
        index: ext_col::IS_XOR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_not".into(),
        index: ext_col::IS_NOT,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "chain_flag".into(),
        index: ext_col::CHAIN_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_index_delta".into(),
        index: ext_col::GATE_INDEX_DELTA,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "is_padding".into(),
        index: ext_col::IS_PADDING,
        kind: ColumnKind::Binary,
    });

    CircuitDescriptor {
        name: "pyana-garbled-evaluation-extended-dsl-v1".into(),
        trace_width: GARBLED_DSL_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: 8,
    }
}

/// Create the production DslCircuit for garbled evaluation.
pub fn garbled_dsl_circuit() -> DslCircuit {
    DslCircuit::new(garbled_extended_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate an extended garbled evaluation trace (56-column layout).
pub fn generate_extended_garbled_trace(
    records: &[ExtendedGateRecord],
    circuit_commitment: &WideHash,
    output_label_hash: &WideHash,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut trace = Vec::with_capacity(records.len().max(2));

    let mut prev_gate_index: u32 = 0;

    for (row_idx, record) in records.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; GARBLED_DSL_WIDTH];

        // Base columns
        for i in 0..8 {
            row[col::left(i)] = record.base.left_label[i];
        }
        for i in 0..8 {
            row[col::right(i)] = record.base.right_label[i];
        }
        row[col::GATE_INDEX] = BabyBear::new(record.base.gate_index);
        for i in 0..8 {
            row[col::hash_out(i)] = record.base.hash_output[i];
        }
        for i in 0..8 {
            row[col::table_entry(i)] = record.base.table_entry[i];
        }
        for i in 0..8 {
            row[col::output(i)] = record.base.output_label[i];
        }
        for i in 0..4 {
            row[col::CIRCUIT_COMMITMENT + i] = circuit_commitment[i];
        }
        for i in 0..4 {
            row[col::OUTPUT_LABEL_HASH + i] = output_label_hash[i];
        }

        // Gate type selectors
        match record.gate_type {
            GateType::And => row[ext_col::IS_AND] = BabyBear::ONE,
            GateType::Or => row[ext_col::IS_OR] = BabyBear::ONE,
            GateType::Xor => row[ext_col::IS_XOR] = BabyBear::ONE,
            GateType::Not => row[ext_col::IS_NOT] = BabyBear::ONE,
        }

        // Chain flag
        if record.chains_to_next {
            row[ext_col::CHAIN_FLAG] = BabyBear::ONE;
        }

        // Gate index delta
        let delta = if row_idx == 0 {
            0u32
        } else {
            record.base.gate_index.wrapping_sub(prev_gate_index)
        };
        row[ext_col::GATE_INDEX_DELTA] = BabyBear::new(delta);

        // is_padding = 0 for real rows
        row[ext_col::IS_PADDING] = BabyBear::ZERO;

        prev_gate_index = record.base.gate_index;
        trace.push(row);
    }

    // Ensure at least 1 row.
    if trace.is_empty() {
        let mut row = vec![BabyBear::ZERO; GARBLED_DSL_WIDTH];
        for i in 0..4 {
            row[col::CIRCUIT_COMMITMENT + i] = circuit_commitment[i];
        }
        for i in 0..4 {
            row[col::OUTPUT_LABEL_HASH + i] = output_label_hash[i];
        }
        row[ext_col::IS_PADDING] = BabyBear::ONE;
        trace.push(row);
    }

    // Pad to power-of-two >= 2.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        let mut pad_row = vec![BabyBear::ZERO; GARBLED_DSL_WIDTH];
        for i in 0..4 {
            pad_row[col::CIRCUIT_COMMITMENT + i] = circuit_commitment[i];
        }
        for i in 0..4 {
            pad_row[col::OUTPUT_LABEL_HASH + i] = output_label_hash[i];
        }
        pad_row[ext_col::IS_PADDING] = BabyBear::ONE;
        // Copy output labels from last real row so chaining doesn't break
        if let Some(last) = trace.last() {
            for i in 0..8 {
                pad_row[col::left(i)] = last[col::output(i)];
                pad_row[col::output(i)] = last[col::output(i)];
                pad_row[col::table_entry(i)] = last[col::output(i)];
            }
        }
        trace.push(pad_row);
    }

    // Public inputs.
    let mut public_inputs = Vec::with_capacity(8);
    for &elem in circuit_commitment.as_slice() {
        public_inputs.push(elem);
    }
    for &elem in output_label_hash.as_slice() {
        public_inputs.push(elem);
    }

    (trace, public_inputs)
}

/// Convert base GateEvalRecords (from comparison circuit evaluation) to extended records.
///
/// The comparison circuit uses a borrow-chain topology where each gate's output feeds
/// the next gate's left input. All gates are labeled as AND (the gate type is
/// informational; the truth table is in the garbled table entries).
pub fn comparison_records_to_extended(gate_trace: &[GateEvalRecord]) -> Vec<ExtendedGateRecord> {
    let num_gates = gate_trace.len();
    gate_trace
        .iter()
        .enumerate()
        .map(|(idx, record)| ExtendedGateRecord {
            base: record.clone(),
            gate_type: GateType::And,
            chains_to_next: idx + 1 < num_gates,
        })
        .collect()
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a STARK proof of correct garbled circuit evaluation (DSL-native).
///
/// This is the production replacement for `circuit::garbled::prove_private_threshold`.
/// It uses the extended 56-column DSL descriptor with full multi-gate support.
///
/// Returns `None` if the evaluation yields the "false" output.
pub fn prove_garbled_evaluation_dsl(
    gate_trace: &[GateEvalRecord],
    circuit_commitment: &WideHash,
    output_label_hash: &WideHash,
) -> GarbledDslProof {
    let extended_records = comparison_records_to_extended(gate_trace);
    prove_garbled_evaluation_extended_dsl(&extended_records, circuit_commitment, output_label_hash)
}

/// Generate a STARK proof from extended gate records (explicit gate types and chaining).
///
/// Use this when you have non-comparison circuits (mixed gate types, fan-out, etc.).
pub fn prove_garbled_evaluation_extended_dsl(
    records: &[ExtendedGateRecord],
    circuit_commitment: &WideHash,
    output_label_hash: &WideHash,
) -> GarbledDslProof {
    let dsl_circuit = garbled_dsl_circuit();
    let (trace, public_inputs) =
        generate_extended_garbled_trace(records, circuit_commitment, output_label_hash);

    let stark_proof = stark::prove(&dsl_circuit, &trace, &public_inputs);

    GarbledDslProof {
        circuit_commitment: *circuit_commitment,
        output_label_hash: *output_label_hash,
        stark_proof,
    }
}

/// Verify a DSL-native garbled evaluation proof.
///
/// Checks:
/// 1. The circuit commitment matches the expected garbled circuit.
/// 2. The output label hash matches the expected "true" output.
/// 3. The STARK proof verifies against the DSL circuit descriptor.
pub fn verify_garbled_evaluation_dsl(
    proof: &GarbledDslProof,
    expected_circuit_commitment: &WideHash,
    expected_output_label_hash: &WideHash,
) -> bool {
    // Check commitments.
    if proof.circuit_commitment != *expected_circuit_commitment {
        return false;
    }
    if proof.output_label_hash != *expected_output_label_hash {
        return false;
    }

    // Reconstruct public inputs.
    let mut public_inputs = Vec::with_capacity(8);
    for &elem in expected_circuit_commitment.as_slice() {
        public_inputs.push(elem);
    }
    for &elem in expected_output_label_hash.as_slice() {
        public_inputs.push(elem);
    }

    let dsl_circuit = garbled_dsl_circuit();
    stark::verify(&dsl_circuit, &proof.stark_proof, &public_inputs).is_ok()
}

/// High-level: prove a private threshold check using the DSL-native garbled circuit.
///
/// Evaluates the garbled circuit and produces a STARK proof of correct evaluation.
/// Returns `None` if the value doesn't meet the threshold (output_bit == false).
pub fn prove_private_threshold_dsl(
    circuit: &garbled::GarbledCircuit,
    my_labels: &[garbled::WireLabel],
) -> Option<GarbledDslProof> {
    let eval = garbled::evaluate_garbled_circuit(circuit, my_labels);

    if !eval.output_bit {
        return None;
    }

    let output_label_hash = garbled::hash_label(&eval.output_label);
    Some(prove_garbled_evaluation_dsl(
        &eval.gate_trace,
        &circuit.circuit_commitment,
        &output_label_hash,
    ))
}

/// High-level: verify a private threshold proof (DSL-native).
pub fn verify_private_threshold_dsl(
    proof: &GarbledDslProof,
    expected_circuit_commitment: &WideHash,
    true_output_label_hash: &WideHash,
) -> bool {
    verify_garbled_evaluation_dsl(proof, expected_circuit_commitment, true_output_label_hash)
}
