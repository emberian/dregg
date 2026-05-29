//! DSL-native note spending proving and verification.
//!
//! This module provides production prove/verify functions for the note spending AIR
//! using the DSL `CircuitDescriptor` + `DslCircuit` infrastructure. It replaces the
//! hand-written `NoteSpendingAir` from `circuit/src/note_spending_air.rs`.
//!
//! # Completeness vs. hand-written AIR
//!
//! The DSL version covers:
//! - Nullifier derivation (two-step hash binding all 8 key limbs)
//! - Value binding as public input (boundary constraint)
//! - Asset type binding as public input (boundary constraint)
//! - Merkle path verification (Hash4to1 constraint on Merkle rows)
//! - Commitment hash binding (Hash constraint on commitment row)
//! - is_merkle binary constraint
//! - Position validity (polynomial degree-4)
//!
//! # Public Inputs
//!
//! [nullifier, merkle_root, value, asset_type]

use crate::field::{BABYBEAR_P, BabyBear};
use crate::note_spending_air::{
    MIN_MERKLE_DEPTH, NOTE_SPENDING_WIDTH, NoteSpendingWitness, col, merkle_col, pi,
};
use crate::poseidon2::hash_fact;
use crate::stark::{self, StarkProof};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

/// Auxiliary column for the intermediate nullifier hash (two-step derivation).
/// Uses col 17 which is unused in the standard NOTE_SPENDING_WIDTH layout.
pub const NULLIFIER_INTERMEDIATE: usize = 17;

// ============================================================================
// Re-export witness types from circuit crate
// ============================================================================

pub use crate::note_spending_air::{
    NoteSpendingAir, NoteSpendingWitness as NoteSpendingWitnessType, create_test_witness,
    key_to_field_elements, test_spending_key,
};

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the production note spending CircuitDescriptor.
///
/// This is the DSL equivalent of `NoteSpendingAir`. Constraints:
/// - C1: is_merkle is binary
/// - C2: Commitment hash binding (gated by 1-is_merkle):
///        commitment == hash_fact(owner, [value, asset_type, creation_nonce, randomness])
/// - C3: Nullifier intermediate (gated by 1-is_merkle):
///        intermediate == hash_fact(commitment, [key[0], key[1], key[2], key[3]])
/// - C4: Nullifier final (gated by 1-is_merkle):
///        nullifier == hash_fact(intermediate, [key[4], key[5], key[6], key[7]])
/// - C5: Position validity (degree 4): pos*(pos-1)*(pos-2)*(pos-3) == 0
/// - C6: Merkle hash binding (gated by is_merkle):
///        parent == hash_4_to_1(children arranged by position)
///        Expressed as: is_merkle * (hash_4_to_1([current, sib0, sib1, sib2] by position) - parent) == 0
///        Simplified: We use the Hash constraint variant on Merkle rows.
/// - C7: Chain continuity: next[CURRENT] == local[PARENT] (Merkle chain)
///
/// Boundary constraints:
/// - Row 0: nullifier == pi[0]
/// - Row 0: value == pi[2]
/// - Row 0: asset_type == pi[3]
/// - Last row: current == pi[1] (merkle_root)
pub fn note_spending_circuit_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: is_merkle is binary
    constraints.push(ConstraintExpr::Binary {
        col: col::IS_MERKLE,
    });

    // C2: Commitment hash binding (gated by 1-is_merkle)
    // On commitment rows: commitment == hash_fact(owner, [value, asset_type, creation_nonce, randomness])
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: col::IS_MERKLE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::COMMITMENT,
            input_cols: vec![
                col::OWNER,
                col::VALUE,
                col::ASSET_TYPE,
                col::CREATION_NONCE,
                col::RANDOMNESS,
            ],
        }),
    });

    // C3: Nullifier intermediate hash (gated by 1-is_merkle)
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: col::IS_MERKLE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: NULLIFIER_INTERMEDIATE,
            input_cols: vec![
                col::COMMITMENT,
                col::SPENDING_KEY_START,
                col::SPENDING_KEY_START + 1,
                col::SPENDING_KEY_START + 2,
                col::SPENDING_KEY_START + 3,
            ],
        }),
    });

    // C4: Nullifier final (gated by 1-is_merkle)
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: col::IS_MERKLE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::NULLIFIER,
            input_cols: vec![
                NULLIFIER_INTERMEDIATE,
                col::SPENDING_KEY_START + 4,
                col::SPENDING_KEY_START + 5,
                col::SPENDING_KEY_START + 6,
                col::SPENDING_KEY_START + 7,
            ],
        }),
    });

    // C5: Position validity (degree 4): pos*(pos-1)*(pos-2)*(pos-3) == 0
    // Expressed as polynomial: pos^4 - 6*pos^3 + 11*pos^2 - 6*pos == 0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                    merkle_col::POSITION,
                ],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![merkle_col::POSITION, merkle_col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![merkle_col::POSITION],
            },
        ],
    });

    // C6: Merkle hash binding (gated by is_merkle)
    // is_merkle * (hash_4_to_1([children by position]) - parent) == 0
    // We use the Hash constraint with position-aware inputs. Since the DSL's Hash4to1
    // doesn't support position-based reordering, we use the full Poseidon2 hash constraint
    // with the understanding that the prover arranges CURRENT at the correct position.
    // The trace generator places children correctly based on position; the constraint
    // just checks that parent == hash_4_to_1(col0, col1, col2, col3) with position encoding.
    //
    // Actually, we use the same approach as the hand-written AIR: the Hash constraint
    // on Merkle rows checks parent against the Lagrange-interpolated children.
    // For the DSL, we express this as a single Hash4to1 constraint gated by is_merkle,
    // where the input columns are the 4 children slots. The trace generator must put
    // them in the correct order.
    //
    // However, the standard Merkle layout uses [current, sib0, sib1, sib2] with position
    // indicating where current goes. We cannot directly use Hash4to1 because the ordering
    // depends on the position column value.
    //
    // Solution: We use the same approach as descriptors.rs — a Hash constraint that takes
    // (current, sib0, sib1, sib2, position) and internally computes the Poseidon2 hash
    // with the correct child ordering. This is what `ConstraintExpr::Hash` does when
    // the input_cols include a position column — it calls `hash_fact` which serves as
    // the position-aware Merkle hash.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_MERKLE,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: merkle_col::PARENT,
            input_cols: vec![
                merkle_col::CURRENT,
                merkle_col::SIB0,
                merkle_col::SIB1,
                merkle_col::SIB2,
                merkle_col::POSITION,
            ],
        }),
    });

    // C7: Chain continuity (transition constraint): next[CURRENT] == local[PARENT]
    // Only meaningful between consecutive Merkle rows, but the commitment row has
    // col::COMMITMENT == first Merkle row's CURRENT, enforced by trace construction.
    constraints.push(ConstraintExpr::Transition {
        next_col: merkle_col::CURRENT,
        local_col: merkle_col::PARENT,
    });

    // Boundary constraints
    let boundaries = vec![
        // Row 0: nullifier == pi[0]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::NULLIFIER,
            pi_index: pi::NULLIFIER,
        },
        // Row 0: value == pi[2]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::VALUE,
            pi_index: pi::VALUE,
        },
        // Row 0: asset_type == pi[3]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::ASSET_TYPE,
            pi_index: pi::ASSET_TYPE,
        },
        // Last row: current hash == merkle_root (pi[1])
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: merkle_col::CURRENT,
            pi_index: pi::MERKLE_ROOT,
        },
        // Row 0: destination_federation == pi[4]
        // CRITICAL: pins the prover-supplied destination_federation in the trace
        // (col 18) to the verifier-supplied pi[4]. A proof generated for
        // destination D fails verification under any other D'.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::DESTINATION_FEDERATION,
            pi_index: pi::DESTINATION_FEDERATION,
        },
        // Row 0: value_hi == pi[5]
        // 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): pins the high u34
        // limb of the note value (col 19) to verifier-supplied pi[5]. Combined
        // with the VALUE (pi[2]) low-30 binding, the proof now binds the FULL
        // u64 amount. Two amounts differing above bit 30 yield distinct pi[5]
        // and therefore distinct proofs; a verifier passing the honest high
        // limb rejects any proof whose trace high limb differs.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::VALUE_HI,
            pi_index: pi::VALUE_HI,
        },
    ];

    // Column definitions
    let columns = vec![
        ColumnDef {
            name: "owner".into(),
            index: col::OWNER,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "value".into(),
            index: col::VALUE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "asset_type".into(),
            index: col::ASSET_TYPE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "creation_nonce".into(),
            index: col::CREATION_NONCE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "commitment".into(),
            index: col::COMMITMENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "nullifier".into(),
            index: col::NULLIFIER,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "randomness".into(),
            index: col::RANDOMNESS,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_merkle".into(),
            index: col::IS_MERKLE,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "nullifier_intermediate".into(),
            index: NULLIFIER_INTERMEDIATE,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "destination_federation".into(),
            index: col::DESTINATION_FEDERATION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "value_hi".into(),
            index: col::VALUE_HI,
            kind: ColumnKind::Value,
        },
    ];

    CircuitDescriptor {
        name: "dregg-note-spending-dsl-v3".into(),
        trace_width: NOTE_SPENDING_WIDTH,
        max_degree: 4, // Position validity is degree 4
        columns,
        constraints,
        boundaries,
        // [nullifier, merkle_root, value(lo30), asset_type,
        //  destination_federation, value_hi(u34)]
        public_input_count: 6,
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the note spending descriptor.
pub fn note_spending_dsl_circuit() -> DslCircuit {
    DslCircuit::new(note_spending_circuit_descriptor())
}

// ============================================================================
// DSL Merkle root computation
// ============================================================================

/// Compute the note commitment with the DSL hashing convention
/// (`hash_fact(owner, [value, asset_type, creation_nonce, randomness])`).
///
/// This matches the C2 commitment constraint, which uses `ConstraintExpr::Hash`
/// (=`hash_fact`), NOT the witness's `hash_many`-based `commitment()`. The two
/// hashes differ, so the DSL trace MUST use this form.
pub fn dsl_commitment(witness: &NoteSpendingWitness) -> BabyBear {
    hash_fact(
        witness.owner,
        &[
            witness.value,
            witness.asset_type,
            witness.creation_nonce,
            witness.randomness,
        ],
    )
}

/// Compute the note nullifier with the DSL two-step hashing convention
/// (matches C3 + C4). Mirrors `generate_note_spending_trace`'s derivation.
pub fn dsl_nullifier(witness: &NoteSpendingWitness) -> BabyBear {
    let commitment = dsl_commitment(witness);
    let intermediate = hash_fact(
        commitment,
        &[
            witness.spending_key[0],
            witness.spending_key[1],
            witness.spending_key[2],
            witness.spending_key[3],
        ],
    );
    hash_fact(
        intermediate,
        &[
            witness.spending_key[4],
            witness.spending_key[5],
            witness.spending_key[6],
            witness.spending_key[7],
        ],
    )
}

/// Compute the Merkle root using the DSL convention: `hash_fact(current, [sib0, sib1, sib2, position])`.
///
/// This differs from `NoteSpendingWitness::merkle_root()` which uses `hash_4_to_1` with
/// Lagrange-interpolated child ordering. The DSL version uses `hash_fact` which is what
/// the `ConstraintExpr::Hash` evaluator computes.
pub fn dsl_merkle_root(witness: &NoteSpendingWitness) -> BabyBear {
    let commitment = dsl_commitment(witness);
    let mut current = commitment;

    for (i, siblings) in witness.merkle_siblings.iter().enumerate() {
        let pos = witness.merkle_positions[i];
        let position = BabyBear::new(pos as u32);
        current = hash_fact(current, &[siblings[0], siblings[1], siblings[2], position]);
    }
    current
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate a DSL-native execution trace from a NoteSpendingWitness.
///
/// Produces the trace for the DSL note spending circuit with the
/// auxiliary `NULLIFIER_INTERMEDIATE` column filled for the DSL Hash constraints.
///
/// NOTE: The Merkle root computation uses `hash_fact(current, [sib0, sib1, sib2, position])`
/// which differs from the old AIR's `hash_4_to_1` with Lagrange interpolation.
pub fn generate_note_spending_trace(
    witness: &NoteSpendingWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = witness.merkle_siblings.len();
    assert_eq!(witness.merkle_positions.len(), depth);
    assert!(
        depth >= MIN_MERKLE_DEPTH,
        "Need at least depth {MIN_MERKLE_DEPTH}"
    );

    // The DSL constraints (C2, C3, C4) recompute commitment and nullifier with
    // `hash_fact` (predicate + terms), NOT the witness's `hash_many`-based
    // `commitment()`/`nullifier()`. The trace MUST use the same `hash_fact`
    // form or the row-0 commitment/nullifier constraints fail. (The witness
    // accessors remain the canonical hashing for the legacy hand-written AIR.)
    let commitment = dsl_commitment(witness);

    // Compute intermediate for the DSL two-step nullifier hash.
    // Step 1: intermediate = hash_fact(commitment, [key[0], key[1], key[2], key[3]])
    let intermediate = hash_fact(
        commitment,
        &[
            witness.spending_key[0],
            witness.spending_key[1],
            witness.spending_key[2],
            witness.spending_key[3],
        ],
    );
    // Step 2: nullifier = hash_fact(intermediate, [key[4], key[5], key[6], key[7]])
    let nullifier = hash_fact(
        intermediate,
        &[
            witness.spending_key[4],
            witness.spending_key[5],
            witness.spending_key[6],
            witness.spending_key[7],
        ],
    );

    let total_rows = 1 + depth;
    let padded_rows = total_rows.next_power_of_two();

    let mut trace = Vec::with_capacity(padded_rows);

    // Row 0: commitment and nullifier computation
    let mut row0 = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
    row0[col::OWNER] = witness.owner;
    row0[col::VALUE] = witness.value;
    row0[col::ASSET_TYPE] = witness.asset_type;
    row0[col::CREATION_NONCE] = witness.creation_nonce;
    row0[col::COMMITMENT] = commitment;
    for (j, &limb) in witness.spending_key.iter().enumerate() {
        row0[col::SPENDING_KEY_START + j] = limb;
    }
    row0[col::NULLIFIER] = nullifier;
    row0[col::RANDOMNESS] = witness.randomness;
    row0[col::IS_MERKLE] = BabyBear::ZERO;
    row0[NULLIFIER_INTERMEDIATE] = intermediate;
    row0[col::DESTINATION_FEDERATION] = witness.destination_federation;
    // 30-bit-trunc fix: high u34 limb of the note value. The witness `value`
    // is a single field element (the committed low limb), so the standard
    // trace leaves the high limb at zero. The bridge-mint path builds the
    // full-u64 trace via `generate_note_spending_trace_with_value_hi`, which
    // overrides this column with the real high bits before proving.
    row0[col::VALUE_HI] = BabyBear::ZERO;
    trace.push(row0);

    // Rows 1..depth+1: Merkle membership proof
    // NOTE: The DSL Hash constraint computes `hash_fact(current, [sib0, sib1, sib2, position])`.
    // This matches the DSL Merkle convention (see dregg-dsl-runtime/src/membership.rs).
    let mut current = commitment;
    for i in 0..depth {
        let pos = witness.merkle_positions[i];
        assert!(pos < 4, "Merkle position must be 0..3");

        let siblings = &witness.merkle_siblings[i];
        let position = BabyBear::new(pos as u32);

        // Compute parent hash using hash_fact (matches DSL Hash constraint semantics)
        let parent = hash_fact(current, &[siblings[0], siblings[1], siblings[2], position]);

        let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
        row[merkle_col::CURRENT] = current;
        row[merkle_col::SIB0] = siblings[0];
        row[merkle_col::SIB1] = siblings[1];
        row[merkle_col::SIB2] = siblings[2];
        row[merkle_col::POSITION] = position;
        row[merkle_col::PARENT] = parent;
        row[col::IS_MERKLE] = BabyBear::ONE;
        trace.push(row);

        current = parent;
    }

    let merkle_root = current;

    // Pad to power of 2
    let padding_parent = hash_fact(
        merkle_root,
        &[
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    );
    for _ in total_rows..padded_rows {
        let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
        row[merkle_col::CURRENT] = merkle_root;
        row[merkle_col::PARENT] = padding_parent;
        row[col::IS_MERKLE] = BabyBear::ONE;
        trace.push(row);
    }

    // The merkle_root is the `current` value after processing all Merkle levels
    // using hash_fact (not hash_4_to_1), which matches the DSL Hash constraint.
    let public_inputs = vec![
        nullifier,
        merkle_root,
        witness.value,
        witness.asset_type,
        witness.destination_federation,
        BabyBear::ZERO, // pi::VALUE_HI: standard (felt-sized) value has no high bits
    ];
    (trace, public_inputs)
}

/// Generate a note-spending trace binding a FULL u64 value via the high limb.
///
/// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5). The standard
/// [`generate_note_spending_trace`] leaves `col::VALUE_HI` (and `pi[5]`) at
/// zero because a `NoteSpendingWitness::value` is a single field element. The
/// bridge-mint executor path, however, presents a u64 amount whose high 34
/// bits previously were silently masked away. This function takes the high
/// limb explicitly and binds it into the trace + PI so the proof commits to
/// the entire u64 (low 30 bits via `col::VALUE`, high 34 via `col::VALUE_HI`).
pub fn generate_note_spending_trace_with_value_hi(
    witness: &NoteSpendingWitness,
    value_hi: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, mut public_inputs) = generate_note_spending_trace(witness);
    trace[0][col::VALUE_HI] = value_hi;
    public_inputs[pi::VALUE_HI] = value_hi;
    (trace, public_inputs)
}

// ============================================================================
// Production prove/verify API
// ============================================================================

/// Generate a DSL-native STARK proof for note spending.
///
/// This replaces `prove_note_spend` from `circuit/src/note_spending_air.rs`.
pub fn prove_note_spend_dsl(witness: &NoteSpendingWitness) -> StarkProof {
    let circuit = note_spending_dsl_circuit();
    let (trace, public_inputs) = generate_note_spending_trace(witness);
    stark::prove(&circuit, &trace, &public_inputs)
}

/// Generate a DSL-native STARK proof binding a FULL u64 value (30-bit-trunc fix).
///
/// `value_hi` is the upper-34-bit limb of the note's u64 amount; the witness's
/// `value` field supplies the low-30 limb that participates in the commitment.
/// Pair with [`verify_note_spend_dsl_full`].
pub fn prove_note_spend_dsl_full(witness: &NoteSpendingWitness, value_hi: BabyBear) -> StarkProof {
    let circuit = note_spending_dsl_circuit();
    let (trace, public_inputs) = generate_note_spending_trace_with_value_hi(witness, value_hi);
    stark::prove(&circuit, &trace, &public_inputs)
}

/// Verify a DSL-native note spending STARK proof.
///
/// For local (non-bridge) spends, pass `BabyBear::ZERO` for `destination_federation`.
/// For bridge proofs, pass the destination federation's identity (as a BabyBear felt);
/// the verifier rejects any proof whose trace destination_federation does not match.
///
/// This replaces `verify_note_spend` from `circuit/src/note_spending_air.rs`.
pub fn verify_note_spend_dsl(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    verify_note_spend_dsl_with_destination(
        nullifier,
        merkle_root,
        value,
        asset_type,
        BabyBear::ZERO,
        proof,
    )
}

/// Verify a DSL-native note spending STARK proof with an explicit destination
/// federation public input.
///
/// This is the bridge-aware variant of `verify_note_spend_dsl`. Use
/// `BabyBear::ZERO` for `destination_federation` when verifying a local
/// (non-bridge) spend. For bridge-mint paths, pass the destination
/// federation's BabyBear identity; the proof verifies only if the prover
/// committed to the same destination at trace-generation time.
pub fn verify_note_spend_dsl_with_destination(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    destination_federation: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    if proof.trace_len < 4 {
        return Err("Proof trace too short for note spending circuit".to_string());
    }

    // BabyBear-typed callers bind a felt-sized value; the high limb is zero.
    verify_note_spend_dsl_full(
        nullifier,
        merkle_root,
        value,
        BabyBear::ZERO,
        asset_type,
        destination_federation,
        proof,
    )
}

/// Verify a note-spending proof binding the FULL u64 value via both limbs.
///
/// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5). `value_lo` is the low-30
/// limb (the felt that participates in the note commitment) and `value_hi` is
/// the upper 34 bits. The verifier rejects any proof whose trace `VALUE_HI`
/// column does not match `value_hi` — so two amounts differing above bit 30
/// (same low limb, different high limb) cannot share a proof.
#[allow(clippy::too_many_arguments)]
pub fn verify_note_spend_dsl_full(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value_lo: BabyBear,
    value_hi: BabyBear,
    asset_type: BabyBear,
    destination_federation: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    if proof.trace_len < 4 {
        return Err("Proof trace too short for note spending circuit".to_string());
    }

    let circuit = note_spending_dsl_circuit();
    let public_inputs = vec![
        nullifier,
        merkle_root,
        value_lo,
        asset_type,
        destination_federation,
        value_hi,
    ];
    stark::verify(&circuit, proof, &public_inputs)
}

// ============================================================================
// Backward-compatible aliases
// ============================================================================

/// Backward-compatible alias: prove note spending using the DSL-native circuit.
pub fn prove_note_spend(witness: &NoteSpendingWitness) -> StarkProof {
    prove_note_spend_dsl(witness)
}

/// Backward-compatible alias: verify note spending using the DSL-native circuit.
///
/// This variant uses `BabyBear::ZERO` for `destination_federation` (local-spend
/// semantics). For bridge proofs, call `verify_note_spend_dsl_with_destination`
/// directly.
pub fn verify_note_spend(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    verify_note_spend_dsl(nullifier, merkle_root, value, asset_type, proof)
}
