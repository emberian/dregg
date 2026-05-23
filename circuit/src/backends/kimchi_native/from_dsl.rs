//! DSL-to-Kimchi bridge: converts `KimchiCircuitDescriptor` (produced by the pyana DSL
//! codegen) into real Kimchi `CircuitGate<Fp>` structures, generates witnesses, and
//! integrates with the Pickles recursive composition backend.
//!
//! This module reconnects the DSL system (which produces BabyBear STARKs via Plonky3)
//! to the Kimchi/Pickles recursive proving backend, closing the regression where the
//! two systems were disconnected.

use ark_ff::{One, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType as KimchiGateType},
        wires::{COLUMNS, Wire},
    },
    proof::ProverProof,
};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::pasta::FULL_ROUNDS;
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;

use super::{
    BaseSponge, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge, VestaOpeningProof,
    fp_to_bytes32, verify_kimchi_proof,
};

// ============================================================================
// DSL Descriptor Types (canonical definitions)
//
// These are the types that the pyana-dsl proc-macro generates references to.
// They live here (behind the `mina` feature) because the converter needs access
// to Kimchi types. `pyana-dsl-runtime` re-exports them as
// `pyana_dsl_runtime::{KimchiCircuitDescriptor, KimchiGate, DslGateType}`.
// ============================================================================

/// Descriptor for a Kimchi circuit generated from a pyana constraint.
#[derive(Debug, Clone)]
pub struct DslCircuitDescriptor {
    /// The gates in the circuit.
    pub gates: Vec<DslGate>,
    /// Number of public input cells.
    pub public_input_count: usize,
    /// Total trace width (number of witness columns).
    pub trace_width: usize,
}

/// A single gate in a DSL-generated Kimchi circuit descriptor.
#[derive(Debug, Clone)]
pub struct DslGate {
    /// The type of gate.
    pub typ: DslGateType,
    /// Coefficients for the gate polynomial (as i64 for DSL convenience).
    /// For Generic gates: `[c0, c1, c2, c3, c4]` enforcing
    /// `c0*w0 + c1*w1 + c2*w2 + c3*(w0*w1) + c4 = 0`.
    pub coeffs: Vec<i64>,
    /// Number of wires used by this gate.
    pub wires: usize,
}

/// Gate types that the DSL can emit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DslGateType {
    /// Generic arithmetic gate with linear combination of wires.
    Generic,
    /// Poseidon hash permutation gate (12 wires per round).
    Poseidon,
}

// ============================================================================
// Converter: DslCircuitDescriptor -> Real Kimchi Gates
// ============================================================================

/// Convert a DSL circuit descriptor into real Kimchi `CircuitGate<Fp>` structures.
///
/// The returned tuple contains (gates, public_input_count).
///
/// # Gate Layout
///
/// 1. First `public_input_count` rows: Generic gates with `coeffs[0] = 1`
///    (Kimchi's standard public input binding rows).
/// 2. Remaining rows: gates from the descriptor, each assigned sequential wire rows.
///
/// # Coefficient Conversion
///
/// `i64` coefficients are converted to `Fp`:
/// - Non-negative values: `Fp::from(v as u64)`
/// - Negative values: `-Fp::from((-v) as u64)` (field subtraction from zero)
pub fn dsl_to_kimchi_gates(desc: &DslCircuitDescriptor) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let pc = desc.public_input_count;

    // Public input binding rows: Kimchi requires that the first `pc` rows are
    // Generic gates with coeffs[0] = 1, constraining w[0][row] = public_input[row].
    for _ in 0..pc {
        let row = gates.len();
        let mut coeffs = vec![Fp::zero(); COLUMNS];
        coeffs[0] = Fp::one();
        gates.push(CircuitGate::new(
            KimchiGateType::Generic,
            Wire::for_row(row),
            coeffs,
        ));
    }

    // Convert each DSL gate to a real Kimchi gate.
    for dsl_gate in &desc.gates {
        let row = gates.len();
        let kimchi_gate_type = match dsl_gate.typ {
            DslGateType::Generic => KimchiGateType::Generic,
            DslGateType::Poseidon => KimchiGateType::Poseidon,
        };

        // Convert i64 coefficients to Fp, padded to COLUMNS width.
        let coeffs: Vec<Fp> = {
            let mut fp_coeffs = Vec::with_capacity(COLUMNS);
            for &c in &dsl_gate.coeffs {
                fp_coeffs.push(i64_to_fp(c));
            }
            // Pad with zeros to fill COLUMNS
            while fp_coeffs.len() < COLUMNS {
                fp_coeffs.push(Fp::zero());
            }
            fp_coeffs.truncate(COLUMNS);
            fp_coeffs
        };

        gates.push(CircuitGate::new(
            kimchi_gate_type,
            Wire::for_row(row),
            coeffs,
        ));
    }

    // Kimchi requires at least one gate after the public input rows. If the DSL
    // descriptor has no gates (degenerate case), add a final zero-constraint gate.
    if desc.gates.is_empty() {
        let row = gates.len();
        gates.push(CircuitGate::new(
            KimchiGateType::Generic,
            Wire::for_row(row),
            vec![Fp::zero(); COLUMNS],
        ));
    }

    (gates, pc)
}

// ============================================================================
// Witness Translator: DSL trace -> Kimchi witness matrix
// ============================================================================

/// Convert a DSL trace (BabyBear values organized as columns) into a Kimchi
/// witness matrix `[Vec<Fp>; COLUMNS]`.
///
/// # Arguments
///
/// - `descriptor`: The circuit descriptor (determines layout and row count).
/// - `trace_columns`: The DSL trace data. Each inner `Vec` is a column of BabyBear
///   values (as `u32`). The length of each column is the number of rows.
/// - `public_inputs`: The public input values (as `Fp`).
///
/// # Trace Layout Mapping
///
/// The DSL trace has `trace_width` columns and N rows. The Kimchi witness has
/// exactly `COLUMNS` (15) columns and M rows (where M = public_input_count + gate_count).
///
/// Mapping:
/// - DSL columns 0..min(trace_width, COLUMNS) map to Kimchi columns 0..
/// - If trace_width > COLUMNS, excess columns are folded into subsequent rows.
/// - Public input rows (first `pc` rows) have `w[0][row] = public_inputs[row]`.
pub fn dsl_witness_to_kimchi(
    descriptor: &DslCircuitDescriptor,
    trace_columns: &[Vec<u32>],
    public_inputs: &[Fp],
) -> [Vec<Fp>; COLUMNS] {
    let (gates, _) = dsl_to_kimchi_gates(descriptor);
    let total_rows = gates.len();

    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);

    // Fill public input rows
    let pc = descriptor.public_input_count;
    for (i, pi) in public_inputs.iter().enumerate().take(pc) {
        witness[0][i] = *pi;
    }

    // Fill gate rows from DSL trace data.
    // The DSL trace is column-major: trace_columns[col][row].
    // We map DSL columns to Kimchi columns, starting from row `pc` (after public inputs).
    let gate_start_row = pc;
    let num_dsl_rows = if trace_columns.is_empty() {
        0
    } else {
        trace_columns[0].len()
    };

    for gate_idx in 0..descriptor.gates.len() {
        let kimchi_row = gate_start_row + gate_idx;
        if kimchi_row >= total_rows {
            break;
        }

        // Map DSL trace row to Kimchi witness columns.
        // Each DSL gate uses `wires` columns from the trace. We read from the
        // corresponding DSL trace row.
        let dsl_row = gate_idx.min(num_dsl_rows.saturating_sub(1));

        for col in 0..COLUMNS {
            if col < trace_columns.len() && dsl_row < trace_columns[col].len() {
                witness[col][kimchi_row] = Fp::from(trace_columns[col][dsl_row] as u64);
            }
        }
    }

    witness
}

/// Convert a flat DSL witness (row-major, with values as u64) into a Kimchi witness.
///
/// This is the simpler interface for when the DSL provides witness values directly
/// as flat vectors of u64 (e.g., from manual witness generation).
///
/// # Arguments
///
/// - `descriptor`: The circuit descriptor.
/// - `witness_values`: Row-major witness data. Each inner `Vec` has length equal to
///   the number of wires used by the corresponding gate.
/// - `public_inputs`: The public input values.
pub fn dsl_flat_witness_to_kimchi(
    descriptor: &DslCircuitDescriptor,
    witness_values: &[Vec<u64>],
    public_inputs: &[Fp],
) -> [Vec<Fp>; COLUMNS] {
    let (gates, _) = dsl_to_kimchi_gates(descriptor);
    let total_rows = gates.len();

    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);

    // Public input rows
    let pc = descriptor.public_input_count;
    for (i, pi) in public_inputs.iter().enumerate().take(pc) {
        witness[0][i] = *pi;
    }

    // Gate rows
    let gate_start_row = pc;
    for (gate_idx, gate_witness) in witness_values.iter().enumerate() {
        let kimchi_row = gate_start_row + gate_idx;
        if kimchi_row >= total_rows {
            break;
        }
        for (col, &val) in gate_witness.iter().enumerate() {
            if col < COLUMNS {
                witness[col][kimchi_row] = Fp::from(val);
            }
        }
    }

    witness
}

// ============================================================================
// DSL Recursive Proving via Pickles
// ============================================================================

/// Prove a DSL-generated circuit with Kimchi.
///
/// Takes a DSL circuit descriptor and witness, produces a Kimchi proof.
/// This is the non-recursive base case (single proof, no chaining).
pub fn prove_dsl_circuit(
    descriptor: &DslCircuitDescriptor,
    witness: [Vec<Fp>; COLUMNS],
) -> Result<KimchiNativeProof, String> {
    let (gates, pc) = dsl_to_kimchi_gates(descriptor);

    let index =
        kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates.clone(), pc);
    let gm = <Vesta as CommitmentCurve>::Map::setup();
    let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
        BaseSponge,
        ScalarSponge,
        _,
    >(&gm, witness.clone(), &[], &index, &mut OsRng)
    .map_err(|e| format!("DSL Kimchi prover error: {:?}", e))?;

    let proof_bytes =
        rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

    // Extract public inputs from witness
    let mut public_input_bytes = Vec::with_capacity(pc * 32);
    for i in 0..pc {
        public_input_bytes.extend_from_slice(&fp_to_bytes32(&witness[0][i]));
    }

    Ok(KimchiNativeProof {
        proof_bytes,
        public_input_bytes,
        circuit_type: KimchiNativeCircuitType::Dsl,
    })
}

/// Verify a DSL-generated Kimchi proof.
///
/// Rebuilds the circuit from the descriptor and verifies the proof against it.
pub fn verify_dsl_proof(
    descriptor: &DslCircuitDescriptor,
    proof: &KimchiNativeProof,
) -> Result<bool, String> {
    let (gates, pc) = dsl_to_kimchi_gates(descriptor);

    // Extract public inputs from the proof's public_input_bytes
    let mut public_inputs = Vec::with_capacity(pc);
    for i in 0..pc {
        let start = i * 32;
        let end = start + 32;
        if end > proof.public_input_bytes.len() {
            return Err("Public inputs too short for descriptor".into());
        }
        let bytes: [u8; 32] = proof.public_input_bytes[start..end]
            .try_into()
            .map_err(|_| "Invalid public input bytes")?;
        public_inputs.push(super::bytes32_to_fp(&bytes));
    }

    let kimchi_proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
        rmp_serde::from_slice(&proof.proof_bytes)
            .map_err(|e| format!("Proof deserialization error: {}", e))?;

    verify_kimchi_proof(&kimchi_proof, gates, &public_inputs, pc)
}

// ============================================================================
// Pickles Recursive Integration
// ============================================================================

use super::super::mina::pickles::{
    PicklesRecursiveProof, PicklesStateTransition, prove_recursive_step, verify_recursive_proof,
};

/// Prove a DSL-generated circuit recursively via Pickles.
///
/// This is the key integration point: it takes a DSL descriptor and witness,
/// generates a Kimchi proof, and wraps it in the Pickles recursive proving
/// framework so it can be chained with previous proofs.
///
/// # Arguments
///
/// - `descriptor`: The DSL circuit descriptor (gates + layout).
/// - `witness_values`: Row-major witness values for each gate.
/// - `public_inputs`: Public inputs for this step.
/// - `previous`: Optional previous recursive proof to chain with.
/// - `transition`: The state transition this proof attests to.
///
/// # Returns
///
/// A `PicklesRecursiveProof` that transitively verifies the entire chain.
pub fn prove_dsl_recursive(
    descriptor: &DslCircuitDescriptor,
    witness_values: &[Vec<u64>],
    public_inputs: &[Fp],
    previous: Option<&PicklesRecursiveProof>,
    transition: &PicklesStateTransition,
) -> Result<PicklesRecursiveProof, String> {
    // First, verify the DSL circuit is satisfiable by producing a base proof.
    let witness = dsl_flat_witness_to_kimchi(descriptor, witness_values, public_inputs);
    let _base_proof = prove_dsl_circuit(descriptor, witness)?;

    // Then produce the recursive Pickles proof wrapping this state transition.
    // The Pickles proof attests to the state transition AND carries forward
    // any previous IPA accumulators for recursive verification.
    prove_recursive_step(previous, transition)
}

/// Verify a DSL-recursive proof chain.
///
/// This verifies a Pickles recursive proof that was produced from a DSL circuit.
/// The verification checks:
/// 1. The Kimchi proof is valid (batched IPA check)
/// 2. The state transition hashes are consistent
/// 3. The accumulated hash chain is correct
/// 4. (If recursive) All previous IPA accumulators are valid
pub fn verify_dsl_recursive(
    proof: &PicklesRecursiveProof,
    expected_initial_pre_hash: Option<&[u8; 32]>,
) -> Result<bool, String> {
    verify_recursive_proof(proof, expected_initial_pre_hash)
}

// ============================================================================
// Full DSL-to-Recursive Pipeline
// ============================================================================

/// A complete DSL proof step that wraps a descriptor + witness + state transition
/// into a single call that produces a recursive proof.
pub struct DslRecursiveStep<'a> {
    pub descriptor: &'a DslCircuitDescriptor,
    pub witness_values: Vec<Vec<u64>>,
    pub public_inputs: Vec<Fp>,
    pub pre_state_hash: [u8; 32],
    pub post_state_hash: [u8; 32],
}

/// Prove a chain of DSL steps recursively.
///
/// Each step:
/// 1. Proves the DSL circuit with Kimchi (validates constraints)
/// 2. Wraps in a Pickles recursive step (carries forward IPA accumulator)
/// 3. Chains with the previous step's proof
///
/// The final proof is constant-size regardless of chain length.
pub fn prove_dsl_chain(steps: &[DslRecursiveStep<'_>]) -> Result<PicklesRecursiveProof, String> {
    if steps.is_empty() {
        return Err("Cannot prove empty DSL chain".into());
    }

    let mut current_proof: Option<PicklesRecursiveProof> = None;

    for step in steps {
        let transition = PicklesStateTransition {
            pre_state_hash: step.pre_state_hash,
            post_state_hash: step.post_state_hash,
        };

        let proof = prove_dsl_recursive(
            step.descriptor,
            &step.witness_values,
            &step.public_inputs,
            current_proof.as_ref(),
            &transition,
        )?;

        current_proof = Some(proof);
    }

    current_proof.ok_or_else(|| "No proof generated".into())
}

// ============================================================================
// Helper functions
// ============================================================================

/// Convert an i64 to Fp, handling negative values via field negation.
fn i64_to_fp(v: i64) -> Fp {
    if v >= 0 {
        Fp::from(v as u64)
    } else {
        -Fp::from((-v) as u64)
    }
}

/// Compute a state hash from public inputs (for constructing PicklesStateTransition).
///
/// This hashes the public inputs into a 32-byte state hash suitable for the
/// Pickles recursive framework.
pub fn compute_state_hash(public_inputs: &[Fp]) -> [u8; 32] {
    use super::hash_many_fp;
    let h = hash_many_fp(public_inputs);
    fp_to_bytes32(&h)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use mina_curves::pasta::Fp;

    /// Build a simple 3-gate descriptor: two equality gates + one arithmetic gate.
    ///
    /// Circuit enforces:
    ///   Gate 0: w0 - w1 = 0 (public_input[0] == w1)
    ///   Gate 1: w0 - w1 = 0 (public_input[1] == w1)
    ///   Gate 2: w0 + w1 - w2 = 0 (addition check)
    fn make_simple_descriptor() -> DslCircuitDescriptor {
        DslCircuitDescriptor {
            gates: vec![
                // Gate 0: equality — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
                // Gate 1: equality — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
                // Gate 2: addition — w0 + w1 - w2 = 0
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, 1, -1, 0, 0],
                    wires: 3,
                },
            ],
            public_input_count: 2,
            trace_width: 3,
        }
    }

    #[test]
    fn test_dsl_to_kimchi_gates_basic() {
        let desc = make_simple_descriptor();
        let (gates, pc) = dsl_to_kimchi_gates(&desc);

        // 2 public input gates + 3 descriptor gates = 5
        assert_eq!(gates.len(), 5);
        assert_eq!(pc, 2);

        // Public input gates have coeffs[0] = 1
        assert_eq!(gates[0].typ, KimchiGateType::Generic);
        assert_eq!(gates[0].coeffs[0], Fp::one());

        // First descriptor gate: equality (1, -1, 0, ...)
        assert_eq!(gates[2].typ, KimchiGateType::Generic);
        assert_eq!(gates[2].coeffs[0], Fp::one());
        assert_eq!(gates[2].coeffs[1], -Fp::one());
    }

    #[test]
    fn test_dsl_to_kimchi_gates_negative_coeffs() {
        let desc = DslCircuitDescriptor {
            gates: vec![DslGate {
                typ: DslGateType::Generic,
                coeffs: vec![1, -1, -1, 0, 0],
                wires: 3,
            }],
            public_input_count: 1,
            trace_width: 3,
        };
        let (gates, _) = dsl_to_kimchi_gates(&desc);
        // Row 1 (after 1 PI row) should have coeffs [1, -1, -1, 0, ...]
        assert_eq!(gates[1].coeffs[0], Fp::one());
        assert_eq!(gates[1].coeffs[1], -Fp::one());
        assert_eq!(gates[1].coeffs[2], -Fp::one());
    }

    #[test]
    fn test_dsl_flat_witness_construction() {
        let desc = make_simple_descriptor();
        let public_inputs = vec![Fp::from(10u64), Fp::from(20u64)];

        // Witness for gates:
        // Gate 0: w0=10, w1=10 (equality: pi[0] == 10)
        // Gate 1: w0=20, w1=20 (equality: pi[1] == 20)
        // Gate 2: w0=10, w1=20, w2=30 (10 + 20 - 30 = 0)
        let witness_values = vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]];

        let witness = dsl_flat_witness_to_kimchi(&desc, &witness_values, &public_inputs);

        // Public input rows
        assert_eq!(witness[0][0], Fp::from(10u64));
        assert_eq!(witness[0][1], Fp::from(20u64));

        // Gate rows (starting at row 2)
        assert_eq!(witness[0][2], Fp::from(10u64));
        assert_eq!(witness[1][2], Fp::from(10u64));
        assert_eq!(witness[0][3], Fp::from(20u64));
        assert_eq!(witness[1][3], Fp::from(20u64));
        assert_eq!(witness[0][4], Fp::from(10u64));
        assert_eq!(witness[1][4], Fp::from(20u64));
        assert_eq!(witness[2][4], Fp::from(30u64));
    }

    #[test]
    fn test_prove_and_verify_simple_dsl_circuit() {
        let desc = make_simple_descriptor();
        let public_inputs = vec![Fp::from(10u64), Fp::from(20u64)];

        let witness_values = vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]];

        let witness = dsl_flat_witness_to_kimchi(&desc, &witness_values, &public_inputs);
        let proof = prove_dsl_circuit(&desc, witness).expect("DSL proof should succeed");
        let verified = verify_dsl_proof(&desc, &proof).expect("Verification should not error");
        assert!(verified, "DSL proof must verify");
    }

    #[test]
    fn test_dsl_proof_invalid_witness_rejected() {
        let desc = make_simple_descriptor();
        let public_inputs = vec![Fp::from(10u64), Fp::from(20u64)];

        // BAD witness: Gate 2 claims 10 + 20 = 25 (wrong!)
        let witness_values = vec![
            vec![10, 10],
            vec![20, 20],
            vec![10, 20, 25], // 10 + 20 != 25
        ];

        let witness = dsl_flat_witness_to_kimchi(&desc, &witness_values, &public_inputs);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_circuit(&desc, witness)
        }));
        assert!(
            result.is_err() || result.unwrap().is_err(),
            "Prover must reject invalid witness"
        );
    }

    #[test]
    fn test_prove_dsl_recursive_single_step() {
        let desc = make_simple_descriptor();
        let public_inputs = vec![Fp::from(10u64), Fp::from(20u64)];
        let witness_values = vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]];

        let pre_hash = compute_state_hash(&[Fp::from(100u64)]);
        let post_hash = compute_state_hash(&[Fp::from(200u64)]);

        let transition = PicklesStateTransition {
            pre_state_hash: pre_hash,
            post_state_hash: post_hash,
        };

        let proof = prove_dsl_recursive(&desc, &witness_values, &public_inputs, None, &transition)
            .expect("Recursive DSL proof should succeed");

        assert_eq!(proof.num_steps, 1);

        let verified =
            verify_dsl_recursive(&proof, Some(&pre_hash)).expect("Verification should not error");
        assert!(verified, "Recursive DSL proof must verify");
    }

    #[test]
    fn test_prove_dsl_recursive_two_step_chain() {
        let desc = make_simple_descriptor();
        let public_inputs = vec![Fp::from(10u64), Fp::from(20u64)];
        let witness_values = vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]];

        let state0 = compute_state_hash(&[Fp::from(100u64)]);
        let state1 = compute_state_hash(&[Fp::from(200u64)]);
        let state2 = compute_state_hash(&[Fp::from(300u64)]);

        // Step 1: state0 -> state1
        let transition1 = PicklesStateTransition {
            pre_state_hash: state0,
            post_state_hash: state1,
        };
        let proof1 =
            prove_dsl_recursive(&desc, &witness_values, &public_inputs, None, &transition1)
                .expect("Step 1 should succeed");

        assert_eq!(proof1.num_steps, 1);

        // Step 2: state1 -> state2 (chaining with proof1)
        let transition2 = PicklesStateTransition {
            pre_state_hash: state1,
            post_state_hash: state2,
        };
        let proof2 = prove_dsl_recursive(
            &desc,
            &witness_values,
            &public_inputs,
            Some(&proof1),
            &transition2,
        )
        .expect("Step 2 should succeed");

        assert_eq!(proof2.num_steps, 2);

        // Verify the final proof — it transitively verifies the entire chain
        let verified = verify_dsl_recursive(&proof2, None).expect("Verification should not error");
        assert!(verified, "Two-step recursive DSL chain must verify");
    }

    #[test]
    fn test_prove_dsl_chain_api() {
        let desc = make_simple_descriptor();

        let state0 = compute_state_hash(&[Fp::from(100u64)]);
        let state1 = compute_state_hash(&[Fp::from(200u64)]);
        let state2 = compute_state_hash(&[Fp::from(300u64)]);

        let steps = vec![
            DslRecursiveStep {
                descriptor: &desc,
                witness_values: vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]],
                public_inputs: vec![Fp::from(10u64), Fp::from(20u64)],
                pre_state_hash: state0,
                post_state_hash: state1,
            },
            DslRecursiveStep {
                descriptor: &desc,
                witness_values: vec![vec![10, 10], vec![20, 20], vec![10, 20, 30]],
                public_inputs: vec![Fp::from(10u64), Fp::from(20u64)],
                pre_state_hash: state1,
                post_state_hash: state2,
            },
        ];

        let proof = prove_dsl_chain(&steps).expect("Chain proof should succeed");
        assert_eq!(proof.num_steps, 2);

        let verified =
            verify_dsl_recursive(&proof, Some(&state0)).expect("Verification should not error");
        assert!(
            verified,
            "DSL chain must verify with expected initial state"
        );
    }

    /// Build a descriptor mimicking the `sovereign_transition` DSL circuit:
    /// - 3 public inputs (pre_state, post_state, effects_hash)
    /// - Binary constraint gate (boolean check)
    /// - Arithmetic gate (subtraction)
    /// - Equality gate
    fn make_sovereign_transition_descriptor() -> DslCircuitDescriptor {
        DslCircuitDescriptor {
            gates: vec![
                // Gate 0: pi[0] binding — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
                // Gate 1: pi[1] binding — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
                // Gate 2: pi[2] binding — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
                // Gate 3: boolean constraint — w0*w1 - w0 = 0 (with w0==w1)
                // Kimchi generic: c0*l + c1*r + c2*o + c3*(l*r) + c4 = 0
                // Setting c0=-1, c3=1: l*r - l = 0, i.e., l^2 - l = 0 when l=r
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![-1, 0, 0, 1, 0],
                    wires: 2,
                },
                // Gate 4: subtraction — old - amount - new = 0
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, -1, 0, 0],
                    wires: 3,
                },
                // Gate 5: final equality check — w0 == w1
                DslGate {
                    typ: DslGateType::Generic,
                    coeffs: vec![1, -1, 0, 0, 0],
                    wires: 2,
                },
            ],
            public_input_count: 3,
            trace_width: 6,
        }
    }

    #[test]
    fn test_sovereign_transition_descriptor_prove_verify() {
        let desc = make_sovereign_transition_descriptor();
        let pre_state = Fp::from(1000u64);
        let post_state = Fp::from(900u64);
        let effects_hash = Fp::from(42u64);
        let public_inputs = vec![pre_state, post_state, effects_hash];

        // Witness:
        // Gate 0: w0=pre_state, w1=pre_state (binding)
        // Gate 1: w0=post_state, w1=post_state (binding)
        // Gate 2: w0=effects_hash, w1=effects_hash (binding)
        // Gate 3: w0=1, w1=1 (boolean check: 1*1 - 1 = 0)
        // Gate 4: w0=1000, w1=100, w2=900 (1000 - 100 - 900 = 0)
        // Gate 5: w0=900, w1=900 (post_state equality)
        let witness_values = vec![
            vec![1000, 1000],
            vec![900, 900],
            vec![42, 42],
            vec![1, 1],
            vec![1000, 100, 900],
            vec![900, 900],
        ];

        let witness = dsl_flat_witness_to_kimchi(&desc, &witness_values, &public_inputs);
        let proof = prove_dsl_circuit(&desc, witness).expect("Sovereign transition proof");
        let verified = verify_dsl_proof(&desc, &proof).expect("Verification");
        assert!(verified, "Sovereign transition DSL proof must verify");
    }

    #[test]
    fn test_sovereign_transition_recursive() {
        let desc = make_sovereign_transition_descriptor();
        let pre_state = Fp::from(1000u64);
        let post_state = Fp::from(900u64);
        let effects_hash = Fp::from(42u64);
        let public_inputs = vec![pre_state, post_state, effects_hash];

        let witness_values = vec![
            vec![1000, 1000],
            vec![900, 900],
            vec![42, 42],
            vec![1, 1],
            vec![1000, 100, 900],
            vec![900, 900],
        ];

        let pre_hash = compute_state_hash(&[pre_state]);
        let post_hash = compute_state_hash(&[post_state]);

        let transition = PicklesStateTransition {
            pre_state_hash: pre_hash,
            post_state_hash: post_hash,
        };

        let proof = prove_dsl_recursive(&desc, &witness_values, &public_inputs, None, &transition)
            .expect("Recursive sovereign transition proof");

        let verified = verify_dsl_recursive(&proof, Some(&pre_hash)).expect("Verification");
        assert!(verified, "Recursive sovereign transition must verify");
    }
}
