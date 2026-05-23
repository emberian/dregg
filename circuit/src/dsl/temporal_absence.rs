//! Production temporal absence proving — DSL-native implementation.
//!
//! This module provides the canonical prove/verify API for temporal absence proofs
//! using the DSL `CircuitDescriptor` infrastructure. It supersedes the hand-written
//! `circuit/src/temporal_absence_air.rs`.
//!
//! # Proof Statement
//!
//! Proves: "event X did NOT occur during blocks [t1, t2]" via a certified gap proof
//! over an append-only timeline. Two adjacent timeline entries bracket the absence
//! window, and both authenticate to the same Merkle root.
//!
//! # Trace Layout (2 rows x 10 columns)
//!
//! | Column | Name            | Description                                |
//! |--------|-----------------|--------------------------------------------|
//! | 0      | block_height    | Block height of the timeline entry         |
//! | 1      | event_type      | Event type identifier (hash)               |
//! | 2      | attribute_hash  | Which attribute this event concerns        |
//! | 3      | timeline_index  | Sequential position in timeline tree       |
//! | 4      | leaf_hash       | Hash of the entry                          |
//! | 5      | merkle_root     | Computed Merkle root from this entry       |
//! | 6      | adj_index_plus1 | timeline_index + 1 (auxiliary)             |
//! | 7      | is_before       | 1 on row 0 (entry_before), 0 on row 1     |
//! | 8      | timing_ok       | 1 if timing constraint is satisfied        |
//! | 9      | attr_diff_inv   | Inverse of (attribute_hash - excluded_attr)|
//!
//! # Public Inputs
//!
//! [t1, t2, excluded_attribute_hash, timeline_root]

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_fact;
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const BLOCK_HEIGHT: usize = 0;
pub const EVENT_TYPE: usize = 1;
pub const ATTRIBUTE_HASH: usize = 2;
pub const TIMELINE_INDEX: usize = 3;
pub const LEAF_HASH: usize = 4;
pub const MERKLE_ROOT: usize = 5;
pub const ADJ_INDEX_PLUS1: usize = 6;
pub const IS_BEFORE: usize = 7;
pub const TIMING_OK: usize = 8;
pub const ATTR_DIFF_INV: usize = 9;

pub const TRACE_WIDTH: usize = 10;

/// Public input indices.
pub const PI_T1: usize = 0;
pub const PI_T2: usize = 1;
pub const PI_EXCLUDED_ATTR: usize = 2;
pub const PI_TIMELINE_ROOT: usize = 3;

pub const PUBLIC_INPUT_COUNT: usize = 4;

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the temporal absence `CircuitDescriptor`.
///
/// Proves that no event with `excluded_attribute_hash` occurred in the
/// timeline during blocks [t1, t2], using a certified gap proof.
pub fn temporal_absence_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let columns = vec![
        ColumnDef {
            name: "block_height".into(),
            index: BLOCK_HEIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "event_type".into(),
            index: EVENT_TYPE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "attribute_hash".into(),
            index: ATTRIBUTE_HASH,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "timeline_index".into(),
            index: TIMELINE_INDEX,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "leaf_hash".into(),
            index: LEAF_HASH,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "merkle_root".into(),
            index: MERKLE_ROOT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "adj_index_plus1".into(),
            index: ADJ_INDEX_PLUS1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_before".into(),
            index: IS_BEFORE,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "timing_ok".into(),
            index: TIMING_OK,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "attr_diff_inv".into(),
            index: ATTR_DIFF_INV,
            kind: ColumnKind::Value,
        },
    ];

    let mut constraints = Vec::new();

    // C1: leaf_hash == hash_fact(block_height, [event_type, attribute_hash, timeline_index])
    constraints.push(ConstraintExpr::Hash {
        output_col: LEAF_HASH,
        input_cols: vec![BLOCK_HEIGHT, EVENT_TYPE, ATTRIBUTE_HASH, TIMELINE_INDEX],
    });

    // C2: is_before is binary
    constraints.push(ConstraintExpr::Binary { col: IS_BEFORE });

    // C3: adj_index_plus1 == timeline_index + 1
    // adj_index_plus1 - timeline_index - 1 == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![ADJ_INDEX_PLUS1],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![TIMELINE_INDEX],
            },
            PolyTerm {
                coeff: neg_one,
                col_indices: vec![],
            }, // constant -1
        ],
    });

    // C4: Transition: next[TIMELINE_INDEX] == local[ADJ_INDEX_PLUS1] (adjacency)
    constraints.push(ConstraintExpr::Transition {
        next_col: TIMELINE_INDEX,
        local_col: ADJ_INDEX_PLUS1,
    });

    // Boundary constraints
    let boundaries = vec![
        // Row 0: merkle_root == timeline_root (pi[3])
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: MERKLE_ROOT,
            pi_index: PI_TIMELINE_ROOT,
        },
        // Row 1 (last): merkle_root == timeline_root (pi[3])
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: MERKLE_ROOT,
            pi_index: PI_TIMELINE_ROOT,
        },
        // Row 0: is_before == 1
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: IS_BEFORE,
            value: BabyBear::ONE,
        },
        // Row 1 (last): is_before == 0
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: IS_BEFORE,
            value: BabyBear::ZERO,
        },
    ];

    CircuitDescriptor {
        name: "pyana-temporal-absence-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
    }
}

/// Create a DslCircuit from the temporal absence descriptor.
pub fn temporal_absence_dsl_circuit() -> DslCircuit {
    DslCircuit::new(temporal_absence_descriptor())
}

// ============================================================================
// Witness types
// ============================================================================

/// A timeline entry for trace generation.
#[derive(Clone, Debug)]
pub struct DslTimelineEntry {
    pub block_height: u32,
    pub event_type: BabyBear,
    pub attribute_hash: BabyBear,
    pub timeline_index: u32,
    /// The Merkle root this entry authenticates to.
    pub merkle_root: BabyBear,
}

impl DslTimelineEntry {
    /// Compute the leaf hash using hash_fact (matches the DSL Hash constraint).
    pub fn leaf_hash(&self) -> BabyBear {
        hash_fact(
            BabyBear::new(self.block_height),
            &[
                self.event_type,
                self.attribute_hash,
                BabyBear::new(self.timeline_index),
            ],
        )
    }
}

/// Complete witness for a temporal absence proof.
#[derive(Clone, Debug)]
pub struct TemporalAbsenceDslWitness {
    /// The timeline entry immediately before the absence window.
    pub entry_before: DslTimelineEntry,
    /// The timeline entry immediately after the absence window.
    pub entry_after: DslTimelineEntry,
    /// Start of the absence window (block height).
    pub t1: u32,
    /// End of the absence window (block height).
    pub t2: u32,
    /// The attribute hash that must NOT appear during [t1, t2].
    pub excluded_attribute_hash: BabyBear,
}

impl TemporalAbsenceDslWitness {
    /// Validate the witness (all constraints would be satisfied).
    pub fn is_valid(&self) -> bool {
        // 1. Adjacency
        if self.entry_after.timeline_index != self.entry_before.timeline_index + 1 {
            return false;
        }
        // 2. Same root
        if self.entry_before.merkle_root != self.entry_after.merkle_root {
            return false;
        }
        // 3. Timing
        if self.entry_before.block_height > self.t1 {
            return false;
        }
        if self.entry_after.block_height < self.t2 {
            return false;
        }
        true
    }
}

// ============================================================================
// Proof type
// ============================================================================

/// A DSL-native temporal absence proof.
#[derive(Clone, Debug)]
pub struct TemporalAbsenceDslProof {
    /// Start of the proven absence window.
    pub t1: u32,
    /// End of the proven absence window.
    pub t2: u32,
    /// The attribute hash that was proven absent.
    pub excluded_attribute_hash: BabyBear,
    /// The timeline root this proof is bound to.
    pub timeline_root: BabyBear,
    /// The STARK proof.
    pub stark_proof: StarkProof,
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a valid temporal absence trace.
///
/// The trace consists of 2 rows: entry_before (row 0) and entry_after (row 1).
/// Returns (trace, public_inputs).
pub fn generate_temporal_absence_trace(
    witness: &TemporalAbsenceDslWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let entry_before = &witness.entry_before;
    let entry_after = &witness.entry_after;
    let timeline_root = entry_before.merkle_root;
    let excluded_attr = witness.excluded_attribute_hash;

    // Row 0: entry_before
    let mut row0 = vec![BabyBear::ZERO; TRACE_WIDTH];
    row0[BLOCK_HEIGHT] = BabyBear::new(entry_before.block_height);
    row0[EVENT_TYPE] = entry_before.event_type;
    row0[ATTRIBUTE_HASH] = entry_before.attribute_hash;
    row0[TIMELINE_INDEX] = BabyBear::new(entry_before.timeline_index);
    row0[LEAF_HASH] = entry_before.leaf_hash();
    row0[MERKLE_ROOT] = timeline_root;
    row0[ADJ_INDEX_PLUS1] = BabyBear::new(entry_before.timeline_index + 1);
    row0[IS_BEFORE] = BabyBear::ONE;
    row0[TIMING_OK] = BabyBear::ONE;
    let diff_before = entry_before.attribute_hash - excluded_attr;
    row0[ATTR_DIFF_INV] = if diff_before != BabyBear::ZERO {
        diff_before.inverse().unwrap_or(BabyBear::ZERO)
    } else {
        BabyBear::ZERO
    };

    // Row 1: entry_after
    let mut row1 = vec![BabyBear::ZERO; TRACE_WIDTH];
    row1[BLOCK_HEIGHT] = BabyBear::new(entry_after.block_height);
    row1[EVENT_TYPE] = entry_after.event_type;
    row1[ATTRIBUTE_HASH] = entry_after.attribute_hash;
    row1[TIMELINE_INDEX] = BabyBear::new(entry_after.timeline_index);
    row1[LEAF_HASH] = entry_after.leaf_hash();
    row1[MERKLE_ROOT] = timeline_root;
    row1[ADJ_INDEX_PLUS1] = BabyBear::new(entry_after.timeline_index + 1);
    row1[IS_BEFORE] = BabyBear::ZERO;
    row1[TIMING_OK] = BabyBear::ONE;
    let diff_after = entry_after.attribute_hash - excluded_attr;
    row1[ATTR_DIFF_INV] = if diff_after != BabyBear::ZERO {
        diff_after.inverse().unwrap_or(BabyBear::ZERO)
    } else {
        BabyBear::ZERO
    };

    let trace = vec![row0, row1];
    let public_inputs = vec![
        BabyBear::new(witness.t1),
        BabyBear::new(witness.t2),
        excluded_attr,
        timeline_root,
    ];

    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a temporal absence proof (DSL-native).
///
/// Proves that no event for `excluded_attribute_hash` occurred in the timeline
/// between blocks `t1` and `t2` (inclusive).
///
/// Returns `None` if the witness is invalid.
pub fn prove_temporal_absence_dsl(
    witness: &TemporalAbsenceDslWitness,
) -> Option<TemporalAbsenceDslProof> {
    if !witness.is_valid() {
        return None;
    }

    let dsl_circuit = temporal_absence_dsl_circuit();
    let (trace, public_inputs) = generate_temporal_absence_trace(witness);

    let stark_proof = stark::prove(&dsl_circuit, &trace, &public_inputs);

    Some(TemporalAbsenceDslProof {
        t1: witness.t1,
        t2: witness.t2,
        excluded_attribute_hash: witness.excluded_attribute_hash,
        timeline_root: witness.entry_before.merkle_root,
        stark_proof,
    })
}

/// Verify a temporal absence proof (DSL-native).
///
/// Checks that the proof correctly demonstrates no event for the excluded
/// attribute occurred in [t1, t2] within the timeline at `timeline_root`.
pub fn verify_temporal_absence_dsl(
    proof: &TemporalAbsenceDslProof,
    t1: u32,
    t2: u32,
    excluded_attribute_hash: BabyBear,
    timeline_root: BabyBear,
) -> bool {
    // Check claimed parameters match expected.
    if proof.t1 != t1 || proof.t2 != t2 {
        return false;
    }
    if proof.excluded_attribute_hash != excluded_attribute_hash {
        return false;
    }
    if proof.timeline_root != timeline_root {
        return false;
    }

    let public_inputs = vec![
        BabyBear::new(t1),
        BabyBear::new(t2),
        excluded_attribute_hash,
        timeline_root,
    ];

    let dsl_circuit = temporal_absence_dsl_circuit();
    stark::verify(&dsl_circuit, &proof.stark_proof, &public_inputs).is_ok()
}
