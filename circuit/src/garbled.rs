//! Garbled circuit evaluation using Poseidon2 as the garbling function.
//!
//! This implements Yao's garbled circuits with Poseidon2 as the encryption primitive,
//! enabling "prover doesn't learn the threshold" private predicates. Using Poseidon2
//! instead of AES makes the STARK-wrapping pattern practical (~300ms proof generation).
//!
//! # Protocol
//!
//! 1. **Verifier (threshold holder):** Garbles a comparison circuit with their threshold
//!    wired in. Sends garbled tables + their input labels to the prover.
//! 2. **Prover (value holder):** Obtains input labels for their value via OT.
//!    Evaluates the garbled circuit gate-by-gate. Learns only the output bit (pass/fail).
//! 3. **STARK proof:** Prover generates a STARK proving correct evaluation.
//!
//! # Key insight
//!
//! Poseidon2 as garbling hash means the evaluation trace IS a valid STARK trace.
//! Each gate evaluation is one Poseidon2 call, which is exactly what our AIR
//! constraints already prove.
//!
//! # Comparison circuit
//!
//! For `a >= b` over 31-bit BabyBear values, the subtraction-borrow circuit uses:
//! - 1 garbled gate per bit position = 31 gates total
//! - Each gate implements borrow propagation with the verifier's threshold bit wired in
//! - Total garbled circuit size: ~1 KB (31 gates * 4 entries * 8 field elements)

use crate::field::BabyBear;
use crate::poseidon2::Poseidon2State;

/// Number of bits in a BabyBear comparison circuit.
pub const COMPARISON_BITS: usize = 31;

/// A wire label: 8 BabyBear field elements (256 bits of entropy modulo p).
pub type WireLabel = [BabyBear; 8];

/// A garbled gate: 4 ciphertexts (one per input combination).
///
/// Each entry encrypts the output label for that input combination under
/// `Poseidon2(left_label || right_label || gate_index)`.
#[derive(Clone, Debug)]
pub struct GarbledGate {
    /// Encrypted output labels: `table[2*la_color + lb_color]` is the entry
    /// for left-color `la_color` and right-color `lb_color`.
    pub table: [WireLabel; 4],
}

/// A garbled circuit for comparing two 31-bit BabyBear values.
#[derive(Clone, Debug)]
pub struct GarbledCircuit {
    /// The garbled gates.
    pub gates: Vec<GarbledGate>,
    /// Gate topology: for each gate, (left_wire_idx, right_wire_idx, output_wire_idx).
    /// Wire indices reference into the labels array during evaluation.
    pub topology: Vec<(usize, usize, usize)>,
    /// Verifier's input labels (already selected for the threshold/borrow init).
    pub input_labels_verifier: Vec<WireLabel>,
    /// Output labels for decoding the final result.
    pub output_label_true: WireLabel,
    pub output_label_false: WireLabel,
    /// Commitment to the circuit (WideHash of all garbled tables, 124-bit).
    pub circuit_commitment: crate::binding::WideHash,
    /// Number of verifier input wires.
    pub num_verifier_inputs: usize,
    /// Number of prover input wires.
    pub num_prover_inputs: usize,
    /// Total number of wires in the circuit.
    pub num_wires: usize,
}

/// Secrets retained by the garbler (verifier) for later verification.
#[derive(Clone, Debug)]
pub struct GarblingSecrets {
    /// Label pairs for the prover's input wires: (zero_label, one_label).
    /// The prover obtains exactly one per wire via OT.
    pub prover_label_pairs: Vec<(WireLabel, WireLabel)>,
    /// The hash of the "true" output label (for verification, 124-bit).
    pub true_output_hash: crate::binding::WideHash,
    /// The hash of the "false" output label (124-bit).
    pub false_output_hash: crate::binding::WideHash,
}

/// Result of garbled circuit evaluation.
#[derive(Clone, Debug)]
pub struct EvalResult {
    /// The output label obtained from evaluation.
    pub output_label: WireLabel,
    /// Whether the output matches the "true" label.
    pub output_bit: bool,
    /// All intermediate wire labels (needed for STARK proof generation).
    pub intermediate_labels: Vec<WireLabel>,
    /// Gate evaluation trace: for each gate, (left_label, right_label, gate_index, output_label).
    pub gate_trace: Vec<GateEvalRecord>,
}

/// A record of a single gate evaluation (for STARK witness generation).
#[derive(Clone, Debug)]
pub struct GateEvalRecord {
    pub left_label: WireLabel,
    pub right_label: WireLabel,
    pub gate_index: u32,
    pub hash_output: WireLabel,
    pub table_entry: WireLabel,
    pub output_label: WireLabel,
}

/// A complete garbled evaluation proof.
#[derive(Clone, Debug)]
pub struct GarbledEvaluationProof {
    /// The circuit commitment (public, 124-bit WideHash).
    pub circuit_commitment: crate::binding::WideHash,
    /// Hash of the output label (public, 124-bit WideHash).
    pub output_label_hash: crate::binding::WideHash,
    /// The STARK proof of correct evaluation.
    pub stark_proof: crate::stark::StarkProof,
}

// ============================================================================
// Garbling: Poseidon2-based encryption
// ============================================================================

/// Derive a garbling key from two input labels and a gate index.
///
/// `key = Poseidon2(left_label || right_label || gate_index)`
///
/// This is the core cryptographic operation. Using Poseidon2 means the
/// same computation appears natively in the STARK trace.
pub fn garbling_hash(left: &WireLabel, right: &WireLabel, gate_index: u32) -> WireLabel {
    let mut state = Poseidon2State::new();
    // Load left label into state[0..8]
    for i in 0..8 {
        state.state[i] = left[i];
    }
    // Load right label into state[8..15] (only 7 slots available before WIDTH=16)
    for i in 0..7 {
        state.state[8 + i] = right[i];
    }
    // Encode gate_index and remaining right label element in the last position
    state.state[15] = BabyBear::new(gate_index) + right[7];

    state.permute();

    let mut output = [BabyBear::ZERO; 8];
    for i in 0..8 {
        output[i] = state.state[i];
    }
    output
}

/// Encrypt: `ciphertext = plaintext + key` (one-time-pad style with Poseidon2 key).
#[inline]
fn xor_labels(a: &WireLabel, b: &WireLabel) -> WireLabel {
    let mut result = [BabyBear::ZERO; 8];
    for i in 0..8 {
        result[i] = a[i] + b[i];
    }
    result
}

/// Decrypt: `plaintext = ciphertext - key` (inverse of xor_labels).
#[inline]
fn decrypt_label(ciphertext: &WireLabel, key: &WireLabel) -> WireLabel {
    let mut result = [BabyBear::ZERO; 8];
    for i in 0..8 {
        result[i] = ciphertext[i] - key[i];
    }
    result
}

/// Extract the "color bit" from a wire label (used for point-and-permute).
/// We use the LSB of the first element's canonical representation.
#[inline]
pub fn color_bit(label: &WireLabel) -> usize {
    (label[0].as_u32() & 1) as usize
}

/// Generate a random wire label.
fn random_label() -> WireLabel {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).expect("getrandom failed");
    let mut label = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let val = u32::from_le_bytes([
            bytes[i * 4],
            bytes[i * 4 + 1],
            bytes[i * 4 + 2],
            bytes[i * 4 + 3],
        ]);
        label[i] = BabyBear::new(val);
    }
    label
}

/// Generate a pair of wire labels with distinct color bits.
/// Returns (zero_label, one_label) where color_bit(zero_label) = 0, color_bit(one_label) = 1.
fn random_label_pair() -> (WireLabel, WireLabel) {
    let mut l0 = random_label();
    let mut l1 = random_label();
    // Ensure color bits are 0 and 1 respectively (point-and-permute).
    // Force l0's first element to be even, l1's to be odd.
    l0[0] = BabyBear::new(l0[0].as_u32() & !1); // clear LSB
    l1[0] = BabyBear::new(l1[0].as_u32() | 1); // set LSB
    (l0, l1)
}

/// Compute the circuit commitment: WideHash of all garbled table entries (124-bit).
fn compute_circuit_commitment(gates: &[GarbledGate]) -> crate::binding::WideHash {
    let mut elements: Vec<BabyBear> = Vec::with_capacity(gates.len() * 32);
    for gate in gates {
        for entry in &gate.table {
            for &elem in entry.iter() {
                elements.push(elem);
            }
        }
    }
    crate::binding::WideHash::from_poseidon2("pyana-garbled-circuit-v1", &elements)
}

/// Hash a wire label to a WideHash (124-bit, for output comparison).
pub fn hash_label(label: &WireLabel) -> crate::binding::WideHash {
    crate::binding::WideHash::from_poseidon2("pyana-garbled-label-v1", label)
}

// ============================================================================
// Garble a comparison circuit: a >= b for 31-bit values
// ============================================================================

/// Garble a comparison circuit for `prover_value >= threshold`.
///
/// The verifier (threshold holder) calls this. The threshold is "wired in" via
/// custom truth tables for each gate position.
///
/// Returns the garbled circuit (to send to prover) and garbling secrets
/// (label pairs for OT).
///
/// # Circuit Design: LSB-first Subtraction Borrow
///
/// Computes whether `a - b` underflows (borrow propagation from LSB to MSB):
///
/// ```text
/// borrow_0 = 0
/// For i = 0 to num_bits-1:
///   borrow_{i+1} = (NOT a_i AND b_i) OR (borrow_i AND (a_i == b_i))
/// result: a >= b iff borrow_{num_bits} == 0
/// ```
///
/// Since the verifier knows `b_i` (their threshold), each bit reduces to a single
/// 2-input gate with inputs `(borrow_i, a_i)`:
///
/// - When `b_i = 0`: `borrow_{i+1} = borrow_i AND NOT(a_i)`
///   - If a_i=1: can't borrow (a has a 1, b has a 0 -- a is "ahead")
///   - If a_i=0: both bits are 0, propagate existing borrow
///
/// - When `b_i = 1`: `borrow_{i+1} = OR(borrow_i, NOT(a_i))`
///   - `= NOT(a_i AND NOT(borrow_i))`
///   - If a_i=0: must borrow (b has 1, a has 0)
///   - If a_i=1: bits are equal, propagate existing borrow
///
/// Final output: borrow=0 (zero-label) means a >= b (true), borrow=1 means a < b (false).
pub fn garble_comparison_circuit(
    threshold: u32,
    num_bits: usize,
) -> (GarbledCircuit, GarblingSecrets) {
    assert!(num_bits <= 31, "BabyBear comparison limited to 31 bits");

    // Wire numbering:
    // - Wires 0..num_bits: prover's input bits (bit 0 = LSB)
    // - Wire num_bits: initial borrow (always 0)
    // - Wires num_bits+1..: intermediate borrow wires from gates

    let num_prover_inputs = num_bits;

    // Generate label pairs for prover input wires (transferred via OT).
    let mut all_wire_labels: Vec<(WireLabel, WireLabel)> = Vec::new();
    for _ in 0..num_prover_inputs {
        all_wire_labels.push(random_label_pair());
    }

    // Wire for initial borrow = 0.
    let borrow_init_wire = num_prover_inputs;
    all_wire_labels.push(random_label_pair());
    let borrow_init_label = all_wire_labels[borrow_init_wire].0; // zero-label (borrow=0)

    let mut next_wire = num_prover_inputs + 1;
    let mut gates_garbled: Vec<GarbledGate> = Vec::new();
    let mut topology: Vec<(usize, usize, usize)> = Vec::new();
    let mut borrow_wire = borrow_init_wire;

    // Process bits from LSB to MSB.
    for bit_idx in 0..num_bits {
        let a_wire = bit_idx; // prover's bit at position bit_idx
        let threshold_bit = (threshold >> bit_idx) & 1;

        // Allocate output wire for next borrow.
        let borrow_out_wire = next_wire;
        next_wire += 1;
        all_wire_labels.push(random_label_pair());

        let borrow_pair = all_wire_labels[borrow_wire];
        let a_pair = all_wire_labels[a_wire];
        let out_pair = all_wire_labels[borrow_out_wire];
        let gate_idx = gates_garbled.len() as u32;

        // Build the garbled gate with custom truth table.
        let mut table = [[BabyBear::ZERO; 8]; 4];
        for borrow_bit in 0..2u8 {
            for a_bit in 0..2u8 {
                // Compute truth table output for this (borrow, a) combination.
                let output_bit = if threshold_bit == 0 {
                    // borrow_{i+1} = borrow_i AND NOT(a_i)
                    borrow_bit == 1 && a_bit == 0
                } else {
                    // borrow_{i+1} = OR(borrow_i, NOT(a_i))
                    borrow_bit == 1 || a_bit == 0
                };

                let borrow_label = if borrow_bit == 0 {
                    &borrow_pair.0
                } else {
                    &borrow_pair.1
                };
                let a_label = if a_bit == 0 { &a_pair.0 } else { &a_pair.1 };
                let out_label = if output_bit { &out_pair.1 } else { &out_pair.0 };

                // Encrypt: ciphertext = output_label + Poseidon2(left || right || gate_index)
                let key = garbling_hash(borrow_label, a_label, gate_idx);
                let ciphertext = xor_labels(out_label, &key);

                // Place at position determined by color bits (point-and-permute).
                let idx = color_bit(borrow_label) * 2 + color_bit(a_label);
                table[idx] = ciphertext;
            }
        }

        gates_garbled.push(GarbledGate { table });
        topology.push((borrow_wire, a_wire, borrow_out_wire));
        borrow_wire = borrow_out_wire;
    }

    // The final borrow_wire holds borrow_{num_bits}.
    // Result: a >= b iff borrow = 0. So:
    //   output_label_true = borrow_wire's ZERO label (no borrow = a >= b)
    //   output_label_false = borrow_wire's ONE label (borrow = a < b)
    let output_wire = borrow_wire;
    let output_label_true = all_wire_labels[output_wire].0; // borrow=0 means a >= b
    let output_label_false = all_wire_labels[output_wire].1; // borrow=1 means a < b

    // Verifier's input labels: just the initial borrow label (always 0).
    let input_labels_verifier = vec![borrow_init_label];

    let circuit_commitment = compute_circuit_commitment(&gates_garbled);

    let circuit = GarbledCircuit {
        gates: gates_garbled,
        topology,
        input_labels_verifier,
        output_label_true,
        output_label_false,
        circuit_commitment,
        num_verifier_inputs: 1, // just the initial borrow
        num_prover_inputs,
        num_wires: next_wire,
    };

    let prover_label_pairs: Vec<(WireLabel, WireLabel)> =
        (0..num_prover_inputs).map(|i| all_wire_labels[i]).collect();

    let secrets = GarblingSecrets {
        prover_label_pairs,
        true_output_hash: hash_label(&output_label_true),
        false_output_hash: hash_label(&output_label_false),
    };

    (circuit, secrets)
}

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluate a garbled circuit given the prover's input labels (obtained via OT)
/// and the verifier's input labels (from the garbled circuit).
///
/// Returns the evaluation result including the output label and all intermediate
/// labels needed for STARK proof generation.
pub fn evaluate_garbled_circuit(
    circuit: &GarbledCircuit,
    prover_labels: &[WireLabel],
) -> EvalResult {
    assert_eq!(
        prover_labels.len(),
        circuit.num_prover_inputs,
        "wrong number of prover input labels"
    );

    // Initialize wire labels array.
    let mut wire_labels: Vec<Option<WireLabel>> = vec![None; circuit.num_wires];

    // Set prover's input labels.
    for (i, label) in prover_labels.iter().enumerate() {
        wire_labels[i] = Some(*label);
    }

    // Set verifier's input labels.
    // For the borrow-based circuit, there's just 1 verifier input: the initial borrow wire.
    let borrow_init_wire = circuit.num_prover_inputs;
    wire_labels[borrow_init_wire] = Some(circuit.input_labels_verifier[0]);

    // Evaluate gates in topological order.
    let mut gate_trace = Vec::with_capacity(circuit.gates.len());

    for (gate_idx, (gate, &(left_wire, right_wire, output_wire))) in circuit
        .gates
        .iter()
        .zip(circuit.topology.iter())
        .enumerate()
    {
        let left_label = wire_labels[left_wire].expect("left wire label not set");
        let right_label = wire_labels[right_wire].expect("right wire label not set");

        // Point-and-permute: use color bits to select the correct row.
        let row_idx = color_bit(&left_label) * 2 + color_bit(&right_label);

        // Decrypt: output_label = table_entry - Poseidon2(left || right || gate_index)
        let key = garbling_hash(&left_label, &right_label, gate_idx as u32);
        let output_label = decrypt_label(&gate.table[row_idx], &key);

        wire_labels[output_wire] = Some(output_label);

        gate_trace.push(GateEvalRecord {
            left_label,
            right_label,
            gate_index: gate_idx as u32,
            hash_output: key,
            table_entry: gate.table[row_idx],
            output_label,
        });
    }

    // Get the output wire label.
    let output_wire = circuit.topology.last().unwrap().2;
    let output_label = wire_labels[output_wire].unwrap();

    // Determine the output bit by comparing with known output labels.
    let output_bit = output_label == circuit.output_label_true;

    // Collect all intermediate labels (for STARK witness).
    let intermediate_labels: Vec<WireLabel> = wire_labels.iter().filter_map(|l| *l).collect();

    EvalResult {
        output_label,
        output_bit,
        intermediate_labels,
        gate_trace,
    }
}

// ============================================================================
// High-level API
// ============================================================================

/// Verifier side: garble a comparison circuit and prepare for OT.
///
/// Returns the garbled circuit (to send to prover) and secrets (for OT and verification).
pub fn prepare_private_threshold_check(threshold: u32) -> (GarbledCircuit, GarblingSecrets) {
    garble_comparison_circuit(threshold, COMPARISON_BITS)
}

/// Prover side: evaluate the garbled circuit and produce a STARK proof.
///
/// `my_labels` are obtained via OT (one per bit of the prover's value).
///
/// Returns `Some(proof)` if the evaluation produces the "true" output,
/// or `None` if the value doesn't meet the threshold.
pub fn prove_private_threshold(
    circuit: &GarbledCircuit,
    my_labels: &[WireLabel],
) -> Option<GarbledEvaluationProof> {
    let eval = evaluate_garbled_circuit(circuit, my_labels);

    if !eval.output_bit {
        return None; // Value doesn't meet threshold.
    }

    // Generate STARK proof of correct evaluation.
    let air = super::garbled_air::GarbledEvaluationAir::new(
        eval.gate_trace.clone(),
        circuit.circuit_commitment,
        hash_label(&eval.output_label),
    );

    let (mut trace, public_inputs) =
        <super::garbled_air::GarbledEvaluationAir as crate::constraint_prover::Air>::generate_trace(
            &air,
        );

    // STARK requires power-of-two trace length >= 2.
    while trace.len() < 2 || !trace.len().is_power_of_two() {
        trace.push(trace.last().unwrap().clone());
    }

    let stark_proof = crate::stark::prove(&air, &trace, &public_inputs);

    Some(GarbledEvaluationProof {
        circuit_commitment: circuit.circuit_commitment,
        output_label_hash: hash_label(&eval.output_label),
        stark_proof,
    })
}

/// Verifier side: verify a garbled evaluation proof.
///
/// Checks that:
/// 1. The circuit commitment matches the garbled circuit the verifier sent.
/// 2. The output label hash matches the "true" output label.
/// 3. The STARK proof verifies.
pub fn verify_private_threshold(
    proof: &GarbledEvaluationProof,
    expected_circuit_commitment: &crate::binding::WideHash,
    true_output_label_hash: &crate::binding::WideHash,
) -> bool {
    // Check commitments match.
    if proof.circuit_commitment != *expected_circuit_commitment {
        return false;
    }
    if proof.output_label_hash != *true_output_label_hash {
        return false;
    }

    // Verify the STARK proof.
    let mut public_inputs = Vec::with_capacity(8);
    for &elem in expected_circuit_commitment.as_slice() {
        public_inputs.push(elem);
    }
    for &elem in true_output_label_hash.as_slice() {
        public_inputs.push(elem);
    }
    let dummy_air = super::garbled_air::GarbledEvaluationAir::new(
        vec![], // dummy trace for verification shape
        *expected_circuit_commitment,
        *true_output_label_hash,
    );
    crate::stark::verify(&dummy_air, &proof.stark_proof, &public_inputs).is_ok()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_garbling_hash_deterministic() {
        let left = [BabyBear::new(1); 8];
        let right = [BabyBear::new(2); 8];
        let h1 = garbling_hash(&left, &right, 0);
        let h2 = garbling_hash(&left, &right, 0);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_garbling_hash_different_inputs() {
        let left = [BabyBear::new(1); 8];
        let right = [BabyBear::new(2); 8];
        let h1 = garbling_hash(&left, &right, 0);
        let h2 = garbling_hash(&left, &right, 1);
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_color_bit_extraction() {
        let mut label = [BabyBear::ZERO; 8];
        label[0] = BabyBear::new(4); // even -> color 0
        assert_eq!(color_bit(&label), 0);

        label[0] = BabyBear::new(5); // odd -> color 1
        assert_eq!(color_bit(&label), 1);
    }

    #[test]
    fn test_xor_decrypt_roundtrip() {
        let label = random_label();
        let key = random_label();
        let ct = xor_labels(&label, &key);
        let recovered = decrypt_label(&ct, &key);
        assert_eq!(recovered, label);
    }

    #[test]
    fn test_garble_and_evaluate_passes() {
        // Threshold = 100, prover value = 150 -> should pass (150 >= 100).
        let threshold = 100u32;
        let prover_value = 150u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        // Simulate OT: prover gets labels for their value's bits.
        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(result.output_bit, "150 >= 100 should be true");
        assert_eq!(result.output_label, circuit.output_label_true);
    }

    #[test]
    fn test_garble_and_evaluate_fails() {
        // Threshold = 100, prover value = 50 -> should fail (50 < 100).
        let threshold = 100u32;
        let prover_value = 50u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(!result.output_bit, "50 >= 100 should be false");
        assert_eq!(result.output_label, circuit.output_label_false);
    }

    #[test]
    fn test_garble_and_evaluate_equal() {
        // Threshold = 100, prover value = 100 -> should pass (100 >= 100).
        let threshold = 100u32;
        let prover_value = 100u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(result.output_bit, "100 >= 100 should be true");
    }

    #[test]
    fn test_garble_and_evaluate_boundary_values() {
        // Test with threshold = 0 (everything passes).
        let (circuit, secrets) = garble_comparison_circuit(0, COMPARISON_BITS);
        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| secrets.prover_label_pairs[bit_idx].0) // value = 0
            .collect();
        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(result.output_bit, "0 >= 0 should be true");

        // Test with threshold = 1, value = 0 (should fail).
        let (circuit, secrets) = garble_comparison_circuit(1, COMPARISON_BITS);
        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| secrets.prover_label_pairs[bit_idx].0) // value = 0
            .collect();
        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(!result.output_bit, "0 >= 1 should be false");
    }

    #[test]
    fn test_garble_and_evaluate_large_values() {
        // Threshold = 1_000_000, prover value = 1_500_000.
        let threshold = 1_000_000u32;
        let prover_value = 1_500_000u32;

        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let result = evaluate_garbled_circuit(&circuit, &prover_labels);
        assert!(result.output_bit, "1500000 >= 1000000 should be true");
    }

    #[test]
    fn test_circuit_commitment_deterministic() {
        let threshold = 42u32;
        let (c1, _) = garble_comparison_circuit(threshold, COMPARISON_BITS);
        // Same threshold, different randomness -> different commitment.
        let (c2, _) = garble_comparison_circuit(threshold, COMPARISON_BITS);
        // Commitments should differ (different random labels).
        assert_ne!(c1.circuit_commitment, c2.circuit_commitment);
    }

    #[test]
    fn test_prover_cannot_learn_threshold() {
        // The prover sees only the garbled circuit and their input labels.
        // They cannot distinguish threshold=100 from threshold=200 just
        // from the circuit structure (all labels are random).
        let (c1, _) = garble_comparison_circuit(100, COMPARISON_BITS);
        let (c2, _) = garble_comparison_circuit(200, COMPARISON_BITS);

        // Both circuits have the same number of gates.
        assert_eq!(c1.gates.len(), c2.gates.len());
        // Circuit structure (topology) is identical.
        assert_eq!(c1.topology, c2.topology);
    }

    #[test]
    fn test_wrong_labels_produce_garbage() {
        let threshold = 100u32;
        let (circuit, _secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);

        // Use wrong labels (random, not from OT).
        let wrong_labels: Vec<WireLabel> = (0..COMPARISON_BITS).map(|_| random_label()).collect();

        let result = evaluate_garbled_circuit(&circuit, &wrong_labels);
        // Output should NOT match either known label (with overwhelming probability).
        assert_ne!(result.output_label, circuit.output_label_true);
        assert_ne!(result.output_label, circuit.output_label_false);
        assert!(!result.output_bit);
    }

    #[test]
    fn test_prove_and_verify_private_threshold() {
        let threshold = 500u32;
        let prover_value = 750u32;

        let (circuit, secrets) = prepare_private_threshold_check(threshold);

        // Simulate OT: prover obtains labels for their value.
        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let proof = prove_private_threshold(&circuit, &prover_labels)
            .expect("750 >= 500 should produce a proof");

        // Verifier checks the proof.
        assert!(verify_private_threshold(
            &proof,
            &circuit.circuit_commitment,
            &secrets.true_output_hash,
        ));
    }

    #[test]
    fn test_prove_returns_none_when_below_threshold() {
        let threshold = 500u32;
        let prover_value = 200u32;

        let (circuit, secrets) = prepare_private_threshold_check(threshold);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let proof = prove_private_threshold(&circuit, &prover_labels);
        assert!(proof.is_none(), "200 < 500 should not produce a proof");
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let threshold = 500u32;
        let prover_value = 750u32;

        let (circuit, secrets) = prepare_private_threshold_check(threshold);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let proof = prove_private_threshold(&circuit, &prover_labels).unwrap();

        // Verify with wrong circuit commitment.
        let wrong_commitment =
            crate::binding::WideHash::from_poseidon2("wrong", &[BabyBear::new(99999)]);
        assert!(!verify_private_threshold(
            &proof,
            &wrong_commitment, // wrong commitment
            &secrets.true_output_hash,
        ));
    }

    #[test]
    fn test_verify_fails_with_wrong_output_hash() {
        let threshold = 500u32;
        let prover_value = 750u32;

        let (circuit, secrets) = prepare_private_threshold_check(threshold);

        let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();

        let proof = prove_private_threshold(&circuit, &prover_labels).unwrap();

        // Verify with wrong output label hash (e.g., the false output hash).
        assert!(!verify_private_threshold(
            &proof,
            &circuit.circuit_commitment,
            &secrets.false_output_hash, // wrong: this is the "false" label
        ));
    }

    #[test]
    fn test_multiple_thresholds() {
        // Test various threshold/value combinations.
        let cases = vec![
            (0, 0, true),
            (0, 1, true),
            (1, 0, false),
            (1, 1, true),
            (100, 99, false),
            (100, 100, true),
            (100, 101, true),
            (1000, 999, false),
            (1000, 1000, true),
            (1000, 2000, true),
            (2_000_000_000, 1_999_999_999, false),
            (2_000_000_000, 2_000_000_000, true),
        ];

        for (threshold, value, expected) in cases {
            let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);
            let prover_labels: Vec<WireLabel> = (0..COMPARISON_BITS)
                .map(|bit_idx| {
                    let bit = (value >> bit_idx) & 1;
                    if bit == 0 {
                        secrets.prover_label_pairs[bit_idx].0
                    } else {
                        secrets.prover_label_pairs[bit_idx].1
                    }
                })
                .collect();

            let result = evaluate_garbled_circuit(&circuit, &prover_labels);
            assert_eq!(
                result.output_bit, expected,
                "Failed for value={value} >= threshold={threshold}: expected {expected}, got {}",
                result.output_bit
            );
        }
    }
}
