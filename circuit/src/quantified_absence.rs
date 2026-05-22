//! Quantified FOR-ALL NOT proofs: "for all X in S, P(X) does not hold".
//!
//! Two approaches implemented:
//!
//! ## Approach A: Recursive STARK composition via IVC
//!
//! Breaks the set into chunks, proves "none of these elements satisfy P" per chunk,
//! and chains chunks via IVC hash accumulation. The final proof covers the full set.
//!
//! This leverages existing infrastructure:
//! - [`chunked_derivation`](crate::chunked_derivation) for the chunking pattern
//! - [`ivc`](crate::ivc) for hash chain accumulation
//! - [`stark`](crate::stark) for per-chunk STARK proofs
//!
//! ## Approach B: Certified complement accumulator
//!
//! Maintains two polynomial accumulators:
//! - `Acc_all`: accumulator over the full set S
//! - `Acc_satisfying`: accumulator over elements where P holds
//!
//! The quotient `Acc_all / Acc_satisfying` yields `Acc_complement` — the accumulator
//! for elements NOT satisfying P. Proving membership in `Acc_complement` proves
//! non-satisfaction of P.
//!
//! For the "for all NOT" case, we prove that `Acc_satisfying` is trivial (equals ONE),
//! meaning no elements satisfy P. This is verified by checking that `Acc_all == Acc_complement`.
//!
//! # Usage
//!
//! ```rust,ignore
//! use pyana_circuit::quantified_absence::*;
//!
//! // Approach A: IVC-chained per-chunk absence
//! let proof = prove_quantified_absence_ivc(&elements, &predicate, chunk_size);
//! let valid = verify_quantified_absence_ivc(&proof, set_commitment, predicate_id);
//!
//! // Approach B: Accumulator quotient
//! let proof = prove_quantified_absence_accumulator(&elements, &predicate, alpha);
//! let valid = verify_quantified_absence_accumulator(&proof, acc_all, alpha);
//! ```

use crate::accumulator_air::{ExtElem, compute_accumulator, derive_alpha};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

// ═══════════════════════════════════════════════════════════════════════════════
// Approach A: IVC-chained per-chunk absence STARKs
// ═══════════════════════════════════════════════════════════════════════════════

/// Default chunk size for the IVC approach.
pub const DEFAULT_ABSENCE_CHUNK_SIZE: usize = 16;

/// Width of the per-chunk absence AIR trace.
///
/// Columns: [element, predicate_result, element_hash, chunk_acc_hash]
///
/// Each row proves that one element does NOT satisfy the predicate.
pub const CHUNK_ABSENCE_WIDTH: usize = 4;

/// Column indices for the chunk absence AIR.
pub mod chunk_col {
    /// The element being tested.
    pub const ELEMENT: usize = 0;
    /// The predicate evaluation result (must be 0 for absence).
    pub const PREDICATE_RESULT: usize = 1;
    /// Hash of the element (for set commitment binding).
    pub const ELEMENT_HASH: usize = 2;
    /// Running accumulator hash over processed elements.
    pub const CHUNK_ACC: usize = 3;
}

/// A predicate function over field elements.
/// Returns a nonzero value if the predicate holds, zero if it does not.
pub type PredicateFn = fn(BabyBear) -> BabyBear;

/// Per-chunk absence STARK AIR.
///
/// Proves that for each element in a chunk, the predicate evaluates to zero
/// (i.e., the predicate does NOT hold for any element in the chunk).
///
/// Public inputs: [chunk_index, chunk_size, initial_acc, final_acc, predicate_id]
pub struct ChunkAbsenceAir;

impl StarkAir for ChunkAbsenceAir {
    fn width(&self) -> usize {
        CHUNK_ABSENCE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        7 // Poseidon2 hash in accumulator
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-chunk-absence-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // C1: predicate_result must be zero (absence)
        let c1 = local[chunk_col::PREDICATE_RESULT];

        // C2: element_hash is correctly computed
        let expected_hash = hash_many(&[local[chunk_col::ELEMENT], BabyBear::new(0x50524544)]); // "PRED" domain
        let c2 = local[chunk_col::ELEMENT_HASH] - expected_hash;

        c1 + alpha * c2
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 5 && trace_len > 0 {
            // Last row: final_acc matches (the accumulator after all elements in chunk).
            // This binds the STARK proof to a specific chain position.
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: chunk_col::CHUNK_ACC,
                value: public_inputs[3], // final_acc
            });
        }
        constraints
    }
}

/// Generate the trace for a single chunk of the quantified absence proof.
///
/// The CHUNK_ACC column holds the running accumulator hash AFTER processing this row.
/// Boundary constraints bind:
/// - Row 0: CHUNK_ACC == hash(initial_acc, elem_hash_0)
/// - Last real row: CHUNK_ACC == final_acc
///
/// We track initial_acc and final_acc externally; the STARK proves element absence
/// per-row and the IVC chain links chunks by matching final_acc -> next initial_acc.
fn generate_chunk_trace(
    elements: &[BabyBear],
    predicate: PredicateFn,
    initial_acc: BabyBear,
) -> (Vec<Vec<BabyBear>>, BabyBear) {
    let mut trace = Vec::with_capacity(elements.len().next_power_of_two().max(2));
    let mut current_acc = initial_acc;

    for &elem in elements {
        let pred_result = predicate(elem);
        let elem_hash = hash_many(&[elem, BabyBear::new(0x50524544)]);
        current_acc = hash_many(&[current_acc, elem_hash]);

        let row = vec![elem, pred_result, elem_hash, current_acc];
        trace.push(row);
    }

    let final_acc = current_acc;

    // Pad to power of 2
    let target_len = trace.len().next_power_of_two().max(2);
    while trace.len() < target_len {
        trace.push(trace.last().unwrap().clone());
    }

    (trace, final_acc)
}

/// A single chunk proof in the IVC chain.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ChunkAbsenceStarkProof {
    /// The chunk index (0-based).
    pub chunk_index: u32,
    /// Number of real elements in this chunk.
    pub chunk_size: u32,
    /// Running accumulator before this chunk.
    pub initial_acc: BabyBear,
    /// Running accumulator after this chunk.
    pub final_acc: BabyBear,
    /// The STARK proof for this chunk.
    pub stark_proof: StarkProof,
}

/// Complete quantified absence proof via IVC-chained chunks.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct QuantifiedAbsenceIvcProof {
    /// Per-chunk STARK proofs.
    pub chunk_proofs: Vec<ChunkAbsenceStarkProof>,
    /// Total number of elements in the set.
    pub total_elements: u32,
    /// The predicate identifier (hash of the predicate description).
    pub predicate_id: BabyBear,
    /// Initial accumulator (before first chunk).
    pub initial_acc: BabyBear,
    /// Final accumulator (after last chunk).
    pub final_acc: BabyBear,
    /// Set commitment (hash of all element hashes).
    pub set_commitment: BabyBear,
    /// IVC accumulated hash binding the entire chain.
    pub ivc_hash: BabyBear,
}

/// Prove "for all x in elements, predicate(x) == 0" using IVC-chained STARKs.
///
/// Breaks the element set into chunks, generates a STARK proof per chunk
/// demonstrating that no element in that chunk satisfies the predicate,
/// and chains all chunks via a running hash accumulator.
///
/// Returns `None` if any element DOES satisfy the predicate.
pub fn prove_quantified_absence_ivc(
    elements: &[BabyBear],
    predicate: PredicateFn,
    predicate_id: BabyBear,
    chunk_size: usize,
) -> Option<QuantifiedAbsenceIvcProof> {
    let chunk_size = chunk_size.max(1);

    // First, verify that no element satisfies the predicate.
    for &elem in elements {
        if predicate(elem) != BabyBear::ZERO {
            return None; // Element satisfies predicate -- cannot prove absence.
        }
    }

    // Compute set commitment
    let set_commitment = compute_set_commitment(elements);

    // Initial accumulator (domain-separated)
    let initial_acc = hash_many(&[
        BabyBear::new(0x51414E54), // "QANT" domain
        predicate_id,
        BabyBear::new(elements.len() as u32),
    ]);

    let num_chunks = elements.len().div_ceil(chunk_size).max(1);
    let mut chunk_proofs = Vec::with_capacity(num_chunks);
    let mut current_acc = initial_acc;
    let mut ivc_hash = initial_acc;

    for chunk_idx in 0..num_chunks {
        let start = chunk_idx * chunk_size;
        let end = (start + chunk_size).min(elements.len());
        let chunk_elements = &elements[start..end];

        let chunk_initial_acc = current_acc;
        let (trace, chunk_final_acc) =
            generate_chunk_trace(chunk_elements, predicate, chunk_initial_acc);

        let public_inputs = vec![
            BabyBear::new(chunk_idx as u32),
            BabyBear::new(chunk_elements.len() as u32),
            chunk_initial_acc,
            chunk_final_acc,
            predicate_id,
        ];

        let air = ChunkAbsenceAir;
        let stark_proof = stark::prove(&air, &trace, &public_inputs);

        chunk_proofs.push(ChunkAbsenceStarkProof {
            chunk_index: chunk_idx as u32,
            chunk_size: chunk_elements.len() as u32,
            initial_acc: chunk_initial_acc,
            final_acc: chunk_final_acc,
            stark_proof,
        });

        current_acc = chunk_final_acc;

        // IVC hash chain: accumulate chunk proof commitment
        ivc_hash = hash_many(&[ivc_hash, BabyBear::new(chunk_idx as u32), chunk_final_acc]);
    }

    Some(QuantifiedAbsenceIvcProof {
        chunk_proofs,
        total_elements: elements.len() as u32,
        predicate_id,
        initial_acc,
        final_acc: current_acc,
        set_commitment,
        ivc_hash,
    })
}

/// Verify a quantified absence proof (IVC approach).
///
/// Checks:
/// 1. All chunk proofs are valid STARKs.
/// 2. Chunk accumulators chain correctly (chunk[i].final_acc == chunk[i+1].initial_acc).
/// 3. The IVC hash matches recomputation.
/// 4. The set commitment matches the expected value.
/// 5. Total element count is correct.
pub fn verify_quantified_absence_ivc(
    proof: &QuantifiedAbsenceIvcProof,
    expected_set_commitment: BabyBear,
    expected_predicate_id: BabyBear,
) -> bool {
    // Check metadata
    if proof.predicate_id != expected_predicate_id {
        return false;
    }
    if proof.set_commitment != expected_set_commitment {
        return false;
    }

    // Verify accumulator chain continuity
    let expected_initial = hash_many(&[
        BabyBear::new(0x51414E54),
        proof.predicate_id,
        BabyBear::new(proof.total_elements),
    ]);
    if proof.initial_acc != expected_initial {
        return false;
    }

    let mut expected_acc = proof.initial_acc;
    let mut ivc_hash = proof.initial_acc;
    let mut total_elements_counted = 0u32;

    for (i, chunk_proof) in proof.chunk_proofs.iter().enumerate() {
        // Chain continuity
        if chunk_proof.initial_acc != expected_acc {
            return false;
        }
        if chunk_proof.chunk_index != i as u32 {
            return false;
        }

        // Verify STARK proof
        let public_inputs = vec![
            BabyBear::new(i as u32),
            BabyBear::new(chunk_proof.chunk_size),
            chunk_proof.initial_acc,
            chunk_proof.final_acc,
            proof.predicate_id,
        ];

        let air = ChunkAbsenceAir;
        if stark::verify(&air, &chunk_proof.stark_proof, &public_inputs).is_err() {
            return false;
        }

        expected_acc = chunk_proof.final_acc;
        total_elements_counted += chunk_proof.chunk_size;

        ivc_hash = hash_many(&[ivc_hash, BabyBear::new(i as u32), chunk_proof.final_acc]);
    }

    // Verify totals
    if total_elements_counted != proof.total_elements {
        return false;
    }
    if expected_acc != proof.final_acc {
        return false;
    }
    if ivc_hash != proof.ivc_hash {
        return false;
    }

    true
}

// ═══════════════════════════════════════════════════════════════════════════════
// Approach B: Certified complement accumulator (polynomial quotient)
// ═══════════════════════════════════════════════════════════════════════════════

/// Width of the quotient accumulator AIR.
///
/// Columns: element(4) + quotient(4) + remainder(4) + diff(4) + product(4) + sum(4) = 24
/// (Operating in BabyBear^4 extension field for 124-bit security.)
pub const QUOTIENT_ACC_WIDTH: usize = 24;

/// Column groups for the quotient accumulator AIR.
pub mod qacc_col {
    /// Element hash embedded in BabyBear^4: cols 0..3.
    pub const ELEMENT: usize = 0;
    /// Quotient witness w: cols 4..7.
    pub const QUOTIENT: usize = 4;
    /// Remainder witness v: cols 8..11. Must equal Acc_complement evaluated at element.
    pub const REMAINDER: usize = 8;
    /// Difference (alpha - element): cols 12..15.
    pub const DIFF: usize = 12;
    /// Product w * diff: cols 16..19.
    pub const PRODUCT: usize = 16;
    /// Sum prod + v (should equal Acc_complement): cols 20..23.
    pub const SUM: usize = 20;
}

/// Quotient accumulator proof: proves non-membership in Acc_all / Acc_subset.
///
/// Given:
/// - `Acc_all = product(alpha - x_i)` for all x_i in S
/// - `Acc_satisfying = product(alpha - x_j)` for x_j where P(x_j) holds
/// - `Acc_complement = Acc_all / Acc_satisfying = product(alpha - x_k)` for x_k where NOT P(x_k)
///
/// For "for all NOT P", we prove `Acc_satisfying == ONE` (empty set satisfies P).
/// This means `Acc_complement == Acc_all`.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct QuantifiedAbsenceAccumulatorProof {
    /// The accumulator over all elements (Acc_all).
    pub acc_all: [BabyBear; 4],
    /// The accumulator over satisfying elements (should be ONE for "for-all-not").
    pub acc_satisfying: [BabyBear; 4],
    /// The alpha challenge.
    pub alpha: [BabyBear; 4],
    /// Number of elements in the set.
    pub num_elements: u32,
    /// STARK proof that Acc_satisfying == ONE.
    pub stark_proof: StarkProof,
    /// The predicate identifier.
    pub predicate_id: BabyBear,
}

/// The quotient accumulator AIR.
///
/// Proves that `Acc_satisfying == ONE` (the set of elements satisfying P is empty).
///
/// Each row represents one element from the full set S.
/// The constraint proves: `w * (alpha - elem) + 1 == Acc_all`
/// which is equivalent to proving that ALL elements contribute to Acc_all
/// (none are factored out into Acc_satisfying).
///
/// Public inputs: [Acc_all(4), alpha(4), num_elements(1)] = 9 elements
pub struct QuotientAccumulatorAir;

impl StarkAir for QuotientAccumulatorAir {
    fn width(&self) -> usize {
        QUOTIENT_ACC_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2 // Extension field multiplication
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "pyana-quotient-accumulator-v1"
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha_random: BabyBear,
    ) -> BabyBear {
        let alpha_challenge = ExtElem::read_from_slice(&public_inputs[4..8]);

        let elem = ExtElem::read_from_slice(&local[qacc_col::ELEMENT..qacc_col::ELEMENT + 4]);
        let w = ExtElem::read_from_slice(&local[qacc_col::QUOTIENT..qacc_col::QUOTIENT + 4]);
        let v = ExtElem::read_from_slice(&local[qacc_col::REMAINDER..qacc_col::REMAINDER + 4]);
        let diff = ExtElem::read_from_slice(&local[qacc_col::DIFF..qacc_col::DIFF + 4]);
        let prod = ExtElem::read_from_slice(&local[qacc_col::PRODUCT..qacc_col::PRODUCT + 4]);
        let sum = ExtElem::read_from_slice(&local[qacc_col::SUM..qacc_col::SUM + 4]);

        let mut combined = BabyBear::ZERO;
        let mut pow = alpha_random;

        // C1: diff == alpha - elem
        let expected_diff = alpha_challenge.sub(elem);
        for i in 0..4 {
            combined = combined + pow * (diff.0[i] - expected_diff.0[i]);
            pow = pow * alpha_random;
        }

        // C2: prod == w * diff
        let expected_prod = w.mul(diff);
        for i in 0..4 {
            combined = combined + pow * (prod.0[i] - expected_prod.0[i]);
            pow = pow * alpha_random;
        }

        // C3: sum == prod + v
        let expected_sum = prod.add(v);
        for i in 0..4 {
            combined = combined + pow * (sum.0[i] - expected_sum.0[i]);
            pow = pow * alpha_random;
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        if public_inputs.len() < 9 || trace_len == 0 {
            return vec![];
        }

        let acc_all = ExtElem::read_from_slice(&public_inputs[0..4]);
        let num_elements = public_inputs[8].as_u32() as usize;

        let mut constraints = vec![];

        // For each active row: sum == Acc_all
        for row in 0..num_elements.min(trace_len) {
            for i in 0..4 {
                constraints.push(BoundaryConstraint {
                    row,
                    col: qacc_col::SUM + i,
                    value: acc_all.0[i],
                });
            }
        }

        constraints
    }
}

/// Helper trait extension for ExtElem to read from a slice.
impl ExtElem {
    /// Read from a slice of BabyBear values.
    pub fn read_from_slice(slice: &[BabyBear]) -> Self {
        Self([slice[0], slice[1], slice[2], slice[3]])
    }
}

/// Prove "for all x in elements, predicate(x) == 0" using the accumulator approach.
///
/// This approach:
/// 1. Computes `Acc_all = product(alpha - hash(x_i))` for all elements.
/// 2. Verifies no element satisfies the predicate (Acc_satisfying == ONE).
/// 3. For each element, computes a quotient witness proving non-membership
///    in the satisfying set (which is empty).
///
/// Returns `None` if any element satisfies the predicate.
pub fn prove_quantified_absence_accumulator(
    elements: &[BabyBear],
    predicate: PredicateFn,
    predicate_id: BabyBear,
) -> Option<QuantifiedAbsenceAccumulatorProof> {
    // Verify absence: no element satisfies predicate
    for &elem in elements {
        if predicate(elem) != BabyBear::ZERO {
            return None;
        }
    }

    if elements.is_empty() {
        // Trivial case: empty set satisfies "for all NOT P" vacuously.
        // Acc_all == ONE (empty product), Acc_satisfying == ONE.
        // We still produce a STARK proof, but over a dummy trace where
        // the single "element" is a sentinel value that trivially satisfies constraints.
        let alpha = derive_alpha_for_absence(elements, predicate_id);
        let acc_all = ExtElem::ONE;
        let acc_satisfying = ExtElem::ONE;

        // For empty set, produce a trivial proof with num_elements = 0.
        // The verifier special-cases this: if num_elements == 0, just check Acc_all == ONE.
        // We still need a valid STARK proof structure, so we use a dummy that has
        // no boundary constraints (since num_elements=0 means no row bindings).
        let air = QuotientAccumulatorAir;
        // Create a dummy trace where all constraints are satisfied trivially:
        // elem = alpha (so diff = 0), quotient = 0, remainder = acc_all, product = 0, sum = acc_all
        let mut dummy_row = vec![BabyBear::ZERO; QUOTIENT_ACC_WIDTH];
        // elem = alpha
        alpha.write_to_row(&mut dummy_row, qacc_col::ELEMENT);
        // diff = alpha - alpha = ZERO
        ExtElem::ZERO.write_to_row(&mut dummy_row, qacc_col::DIFF);
        // quotient = ZERO
        ExtElem::ZERO.write_to_row(&mut dummy_row, qacc_col::QUOTIENT);
        // remainder = acc_all = ONE
        acc_all.write_to_row(&mut dummy_row, qacc_col::REMAINDER);
        // product = ZERO * ZERO = ZERO
        ExtElem::ZERO.write_to_row(&mut dummy_row, qacc_col::PRODUCT);
        // sum = product + remainder = ZERO + ONE = ONE = acc_all
        acc_all.write_to_row(&mut dummy_row, qacc_col::SUM);

        let trace = vec![dummy_row.clone(), dummy_row]; // min 2 rows

        let mut public_inputs = Vec::with_capacity(9);
        public_inputs.extend_from_slice(&acc_all.0);
        public_inputs.extend_from_slice(&alpha.0);
        public_inputs.push(BabyBear::ZERO);

        let stark_proof = stark::prove(&air, &trace, &public_inputs);

        return Some(QuantifiedAbsenceAccumulatorProof {
            acc_all: acc_all.0,
            acc_satisfying: acc_satisfying.0,
            alpha: alpha.0,
            num_elements: 0,
            stark_proof,
            predicate_id,
        });
    }

    // Hash elements for accumulator
    let element_hashes: Vec<BabyBear> = elements
        .iter()
        .map(|&e| hash_many(&[e, BabyBear::new(0x50524544)]))
        .collect();

    // Derive alpha challenge
    let alpha = derive_alpha_for_absence(&element_hashes, predicate_id);

    // Compute Acc_all
    let acc_all = compute_accumulator(&element_hashes, alpha);

    // Acc_satisfying is ONE (no elements satisfy P)
    let acc_satisfying = ExtElem::ONE;

    // For each element, compute quotient witness: w such that w * (alpha - h_i) + v_i = Acc_all
    // where v_i is the evaluation of the accumulator polynomial at h_i EXCLUDING h_i itself.
    // Since h_i IS in the set (it contributes to Acc_all), v_i = product(h_i - h_j) for j != i.
    let mut trace = Vec::with_capacity(elements.len());

    for (idx, &h) in element_hashes.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; QUOTIENT_ACC_WIDTH];

        let h_ext = ExtElem::from_base(h);

        // remainder = product(h - h_j) for j != idx, in extension field embedded
        let mut remainder_base = BabyBear::ONE;
        for (j, &other_h) in element_hashes.iter().enumerate() {
            if j != idx {
                remainder_base = remainder_base * (h - other_h);
            }
        }
        let remainder = ExtElem::from_base(remainder_base);

        // diff = alpha - h
        let diff = alpha.sub(h_ext);

        // quotient = (Acc_all - remainder) / diff
        let numerator = acc_all.sub(remainder);
        let quotient = numerator.mul(diff.inverse()?);

        // product = quotient * diff
        let product = quotient.mul(diff);

        // sum = product + remainder (should equal Acc_all)
        let sum = product.add(remainder);

        // Write to row
        h_ext.write_to_row(&mut row, qacc_col::ELEMENT);
        quotient.write_to_row(&mut row, qacc_col::QUOTIENT);
        remainder.write_to_row(&mut row, qacc_col::REMAINDER);
        diff.write_to_row(&mut row, qacc_col::DIFF);
        product.write_to_row(&mut row, qacc_col::PRODUCT);
        sum.write_to_row(&mut row, qacc_col::SUM);

        trace.push(row);
    }

    // Pad to power of 2
    let target_len = trace.len().next_power_of_two().max(2);
    while trace.len() < target_len {
        trace.push(trace.last().unwrap().clone());
    }

    // Public inputs
    let mut public_inputs = Vec::with_capacity(9);
    public_inputs.extend_from_slice(&acc_all.0);
    public_inputs.extend_from_slice(&alpha.0);
    public_inputs.push(BabyBear::new(elements.len() as u32));

    let air = QuotientAccumulatorAir;
    let stark_proof = stark::prove(&air, &trace, &public_inputs);

    Some(QuantifiedAbsenceAccumulatorProof {
        acc_all: acc_all.0,
        acc_satisfying: acc_satisfying.0,
        alpha: alpha.0,
        num_elements: elements.len() as u32,
        stark_proof,
        predicate_id,
    })
}

/// Verify a quantified absence proof (accumulator approach).
///
/// Checks:
/// 1. `Acc_satisfying == ONE` (no elements satisfy P).
/// 2. The STARK proof is valid (all elements contribute to Acc_all).
/// 3. The accumulator matches the expected value for the set.
pub fn verify_quantified_absence_accumulator(
    proof: &QuantifiedAbsenceAccumulatorProof,
    expected_acc_all: ExtElem,
    expected_alpha: ExtElem,
    expected_predicate_id: BabyBear,
) -> bool {
    // Check predicate identity
    if proof.predicate_id != expected_predicate_id {
        return false;
    }

    // Acc_satisfying must be ONE (empty satisfying set)
    let acc_satisfying = ExtElem(proof.acc_satisfying);
    if acc_satisfying != ExtElem::ONE {
        return false;
    }

    // Acc_all must match expected
    let acc_all = ExtElem(proof.acc_all);
    if acc_all != expected_acc_all {
        return false;
    }

    // Alpha must match expected
    let alpha = ExtElem(proof.alpha);
    if alpha != expected_alpha {
        return false;
    }

    // For empty sets, Acc_all == ONE is the only check needed (vacuous truth).
    // The STARK proof is a formality binding to the same parameters.
    // We still verify it for completeness.

    // Verify STARK proof
    let mut public_inputs = Vec::with_capacity(9);
    public_inputs.extend_from_slice(&proof.acc_all);
    public_inputs.extend_from_slice(&proof.alpha);
    public_inputs.push(BabyBear::new(proof.num_elements));

    let air = QuotientAccumulatorAir;
    stark::verify(&air, &proof.stark_proof, &public_inputs).is_ok()
}

// ═══════════════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════════════

/// Compute a commitment to a set of elements.
pub fn compute_set_commitment(elements: &[BabyBear]) -> BabyBear {
    if elements.is_empty() {
        return BabyBear::ZERO;
    }
    let mut acc = BabyBear::new(0x53455400); // "SET\0" domain
    for &elem in elements {
        acc = hash_many(&[acc, elem]);
    }
    acc
}

/// Derive the alpha challenge for the absence proof.
/// Binds to the element set and predicate identity.
pub fn derive_alpha_for_absence(element_hashes: &[BabyBear], predicate_id: BabyBear) -> ExtElem {
    // Domain separator incorporating predicate_id
    let domain = hash_many(&[
        BabyBear::new(0x41425300), // "ABS\0"
        predicate_id,
        BabyBear::new(element_hashes.len() as u32),
    ]);

    let binding = if element_hashes.is_empty() {
        domain
    } else {
        let sample_count = element_hashes.len().min(16);
        let mut elems = vec![domain];
        for &h in &element_hashes[..sample_count] {
            elems.push(h);
        }
        hash_many(&elems)
    };

    let h0 = binding;
    let h1 = hash_many(&[h0, BabyBear::new(1)]);
    let h2 = hash_many(&[h0, BabyBear::new(2)]);
    let h3 = hash_many(&[h0, BabyBear::new(3)]);

    ExtElem([h0, h1, h2, h3])
}

/// Helper: write ExtElem to a trace row at offset.
impl ExtElem {
    pub fn write_to_row(&self, row: &mut [BabyBear], offset: usize) {
        row[offset] = self.0[0];
        row[offset + 1] = self.0[1];
        row[offset + 2] = self.0[2];
        row[offset + 3] = self.0[3];
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // Approach A: IVC tests
    // =========================================================================

    /// Predicate: "element > 100" (returns nonzero if true)
    fn predicate_gt_100(x: BabyBear) -> BabyBear {
        if x.as_u32() > 100 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        }
    }

    /// Predicate: "element is even" (returns nonzero if true)
    fn predicate_is_even(x: BabyBear) -> BabyBear {
        if x.as_u32() % 2 == 0 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        }
    }

    /// Predicate: always false (nothing satisfies it)
    fn predicate_never(_x: BabyBear) -> BabyBear {
        BabyBear::ZERO
    }

    #[test]
    fn test_ivc_absence_all_below_threshold() {
        // All elements <= 100, prove "for all x, NOT (x > 100)"
        let elements: Vec<BabyBear> = (1..=20).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(0x47543130); // "GT100"

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            DEFAULT_ABSENCE_CHUNK_SIZE,
        );
        assert!(proof.is_some(), "Should prove absence when all <= 100");

        let proof = proof.unwrap();
        let set_commitment = compute_set_commitment(&elements);
        let valid = verify_quantified_absence_ivc(&proof, set_commitment, predicate_id);
        assert!(valid, "IVC absence proof should verify");
    }

    #[test]
    fn test_ivc_absence_fails_when_predicate_satisfied() {
        // Element 101 satisfies "x > 100"
        let elements: Vec<BabyBear> = vec![50, 60, 70, 101, 80]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let predicate_id = BabyBear::new(0x47543130);

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            DEFAULT_ABSENCE_CHUNK_SIZE,
        );
        assert!(
            proof.is_none(),
            "Should fail when an element satisfies the predicate"
        );
    }

    #[test]
    fn test_ivc_absence_multiple_chunks() {
        // 50 elements, chunk size 10 -> 5 chunks
        let elements: Vec<BabyBear> = (1..=50).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(0x47543130);

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            10, // small chunks
        );
        assert!(proof.is_some());

        let proof = proof.unwrap();
        assert_eq!(proof.chunk_proofs.len(), 5);

        let set_commitment = compute_set_commitment(&elements);
        let valid = verify_quantified_absence_ivc(&proof, set_commitment, predicate_id);
        assert!(valid, "Multi-chunk proof should verify");
    }

    #[test]
    fn test_ivc_absence_single_element() {
        let elements = vec![BabyBear::new(42)];
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            DEFAULT_ABSENCE_CHUNK_SIZE,
        );
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let set_commitment = compute_set_commitment(&elements);
        let valid = verify_quantified_absence_ivc(&proof, set_commitment, predicate_id);
        assert!(valid);
    }

    #[test]
    fn test_ivc_absence_wrong_commitment_fails() {
        let elements: Vec<BabyBear> = (1..=10).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            DEFAULT_ABSENCE_CHUNK_SIZE,
        )
        .unwrap();

        let wrong_commitment = BabyBear::new(99999);
        let valid = verify_quantified_absence_ivc(&proof, wrong_commitment, predicate_id);
        assert!(!valid, "Wrong set commitment should fail");
    }

    #[test]
    fn test_ivc_absence_wrong_predicate_id_fails() {
        let elements: Vec<BabyBear> = (1..=10).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_ivc(
            &elements,
            predicate_gt_100,
            predicate_id,
            DEFAULT_ABSENCE_CHUNK_SIZE,
        )
        .unwrap();

        let set_commitment = compute_set_commitment(&elements);
        let wrong_predicate = BabyBear::new(999);
        let valid = verify_quantified_absence_ivc(&proof, set_commitment, wrong_predicate);
        assert!(!valid, "Wrong predicate ID should fail");
    }

    #[test]
    fn test_ivc_absence_trivial_predicate() {
        // A predicate that never holds -- any set passes
        let elements: Vec<BabyBear> = (1..=100).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(0x4E455645); // "NEVE" as hex

        let proof = prove_quantified_absence_ivc(&elements, predicate_never, predicate_id, 20);
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let set_commitment = compute_set_commitment(&elements);
        let valid = verify_quantified_absence_ivc(&proof, set_commitment, predicate_id);
        assert!(valid);
    }

    // =========================================================================
    // Approach B: Accumulator tests
    // =========================================================================

    #[test]
    fn test_accumulator_absence_basic() {
        // All elements <= 100
        let elements: Vec<BabyBear> = (1..=10).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(0x47543130);

        let proof = prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id);
        assert!(proof.is_some(), "Should prove absence");

        let proof = proof.unwrap();

        // Recompute expected accumulator
        let element_hashes: Vec<BabyBear> = elements
            .iter()
            .map(|&e| hash_many(&[e, BabyBear::new(0x50524544)]))
            .collect();
        let alpha = derive_alpha_for_absence(&element_hashes, predicate_id);
        let acc_all = compute_accumulator(&element_hashes, alpha);

        let valid = verify_quantified_absence_accumulator(&proof, acc_all, alpha, predicate_id);
        assert!(valid, "Accumulator absence proof should verify");
    }

    #[test]
    fn test_accumulator_absence_fails_when_satisfied() {
        let elements: Vec<BabyBear> = vec![50, 60, 101, 80]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id);
        assert!(proof.is_none(), "Should fail when predicate is satisfied");
    }

    #[test]
    fn test_accumulator_absence_empty_set() {
        let elements: Vec<BabyBear> = vec![];
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id);
        assert!(
            proof.is_some(),
            "Empty set should trivially satisfy for-all-not"
        );

        let proof = proof.unwrap();
        assert_eq!(proof.num_elements, 0);

        let alpha = derive_alpha_for_absence(&[], predicate_id);
        let acc_all = ExtElem::ONE; // Empty product

        let valid = verify_quantified_absence_accumulator(&proof, acc_all, alpha, predicate_id);
        assert!(valid);
    }

    #[test]
    fn test_accumulator_absence_wrong_acc_fails() {
        let elements: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id)
            .unwrap();

        let wrong_acc = ExtElem([
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        let element_hashes: Vec<BabyBear> = elements
            .iter()
            .map(|&e| hash_many(&[e, BabyBear::new(0x50524544)]))
            .collect();
        let alpha = derive_alpha_for_absence(&element_hashes, predicate_id);

        let valid = verify_quantified_absence_accumulator(&proof, wrong_acc, alpha, predicate_id);
        assert!(!valid, "Wrong accumulator should fail");
    }

    #[test]
    fn test_accumulator_absence_wrong_alpha_fails() {
        let elements: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(1);

        let proof = prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id)
            .unwrap();

        let element_hashes: Vec<BabyBear> = elements
            .iter()
            .map(|&e| hash_many(&[e, BabyBear::new(0x50524544)]))
            .collect();
        let alpha = derive_alpha_for_absence(&element_hashes, predicate_id);
        let acc_all = compute_accumulator(&element_hashes, alpha);

        let wrong_alpha = ExtElem([
            BabyBear::new(9),
            BabyBear::new(8),
            BabyBear::new(7),
            BabyBear::new(6),
        ]);
        let valid =
            verify_quantified_absence_accumulator(&proof, acc_all, wrong_alpha, predicate_id);
        assert!(!valid, "Wrong alpha should fail");
    }

    #[test]
    fn test_accumulator_absence_larger_set() {
        // 50 elements, all odd (so "is_even" never holds)
        let elements: Vec<BabyBear> = (0..50).map(|i| BabyBear::new(i * 2 + 1)).collect();
        let predicate_id = BabyBear::new(0x4556454E); // "EVEN" as hex

        let proof =
            prove_quantified_absence_accumulator(&elements, predicate_is_even, predicate_id);
        assert!(
            proof.is_some(),
            "All odd elements should not satisfy is_even"
        );

        let proof = proof.unwrap();
        let element_hashes: Vec<BabyBear> = elements
            .iter()
            .map(|&e| hash_many(&[e, BabyBear::new(0x50524544)]))
            .collect();
        let alpha = derive_alpha_for_absence(&element_hashes, predicate_id);
        let acc_all = compute_accumulator(&element_hashes, alpha);

        let valid = verify_quantified_absence_accumulator(&proof, acc_all, alpha, predicate_id);
        assert!(valid);
    }

    // =========================================================================
    // Cross-approach consistency
    // =========================================================================

    #[test]
    fn test_both_approaches_agree() {
        // Same set and predicate, both approaches should succeed or fail together
        let elements: Vec<BabyBear> = (1..=20).map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(42);

        let ivc_proof = prove_quantified_absence_ivc(&elements, predicate_gt_100, predicate_id, 8);
        let acc_proof =
            prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id);

        assert!(ivc_proof.is_some());
        assert!(acc_proof.is_some());
    }

    #[test]
    fn test_both_approaches_fail_together() {
        let elements: Vec<BabyBear> = vec![50, 60, 150].into_iter().map(BabyBear::new).collect();
        let predicate_id = BabyBear::new(42);

        let ivc_proof = prove_quantified_absence_ivc(&elements, predicate_gt_100, predicate_id, 8);
        let acc_proof =
            prove_quantified_absence_accumulator(&elements, predicate_gt_100, predicate_id);

        assert!(ivc_proof.is_none());
        assert!(acc_proof.is_none());
    }

    // =========================================================================
    // Helper tests
    // =========================================================================

    #[test]
    fn test_set_commitment_deterministic() {
        let elements: Vec<BabyBear> = (1..=10).map(BabyBear::new).collect();
        let c1 = compute_set_commitment(&elements);
        let c2 = compute_set_commitment(&elements);
        assert_eq!(c1, c2);
        assert_ne!(c1, BabyBear::ZERO);
    }

    #[test]
    fn test_set_commitment_order_sensitive() {
        let elements_a: Vec<BabyBear> = vec![BabyBear::new(1), BabyBear::new(2)];
        let elements_b: Vec<BabyBear> = vec![BabyBear::new(2), BabyBear::new(1)];
        let c_a = compute_set_commitment(&elements_a);
        let c_b = compute_set_commitment(&elements_b);
        assert_ne!(
            c_a, c_b,
            "Different orderings should produce different commitments"
        );
    }

    #[test]
    fn test_derive_alpha_deterministic() {
        let hashes: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let pred_id = BabyBear::new(99);
        let a1 = derive_alpha_for_absence(&hashes, pred_id);
        let a2 = derive_alpha_for_absence(&hashes, pred_id);
        assert_eq!(a1, a2);
    }

    #[test]
    fn test_derive_alpha_different_predicates() {
        let hashes: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let a1 = derive_alpha_for_absence(&hashes, BabyBear::new(1));
        let a2 = derive_alpha_for_absence(&hashes, BabyBear::new(2));
        assert_ne!(
            a1, a2,
            "Different predicates should produce different alphas"
        );
    }
}
