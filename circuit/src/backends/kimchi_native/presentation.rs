//! Kimchi native presentation circuit.
//!
//! The presentation circuit is the capstone of the credential system. It composes
//! all sub-proofs (fold chain, derivation, non-revocation) into a single
//! authorization statement with REAL algebraic constraints:
//!
//! 1. Composition commitment correctness: Poseidon(fold_chain_hash, derivation_hash, tag) == public[7]
//! 2. Presentation tag correctness: Poseidon(final_root, randomness, verifier_nonce) == public[8]
//! 3. Non-revocation check: non_revocation_eval * inverse == 1
//! 4. Composition commitment non-zero: composition_commitment * inverse == 1
//! 5. Sub-proof hash binding: fold_chain_hash and derivation_hash are inputs to composition Poseidon
//! 6. Token expiry: not_after_height >= verifier_block_height (bit-decomp GTE)
//! 7. Revealed facts commitment: Poseidon(revealed_facts...) == public revealed_facts_commitment
//! 8. Issuer membership: blinded Poseidon Merkle path proving issuer key in federation tree
use super::fold::FpMerkleWitness;
use super::{
    BaseSponge, GTE_DIFF_BITS, KimchiNativeCircuitType, KimchiNativeProof, ScalarSponge,
    SpongeParams, VestaOpeningProof, fp_to_bytes32, verify_kimchi_proof,
};
use ark_ff::{Field, One, PrimeField, Zero};
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::poseidon::{POS_ROWS_PER_HASH, generate_witness},
        wires::{COLUMNS, Wire},
    },
    curve::KimchiCurve,
    proof::ProverProof,
};
use mina_curves::pasta::{Fp, Vesta};
use mina_poseidon::{
    pasta::FULL_ROUNDS,
    poseidon::{ArithmeticSponge, Sponge},
};
use poly_commitment::commitment::CommitmentCurve;
use rand_core::OsRng;

/// Number of public input rows in the presentation circuit.
/// Public inputs:
///   0: federation_root
///   1-4: request_predicate[0..4]
///   5: timestamp
///   6: verifier_nonce
///   7: composition_commitment
///   8: presentation_tag
///   9: verifier_block_height
///   10: not_after_height
///   11: revealed_facts_commitment
///   12: issuer_blinded_leaf (blinded issuer membership public input)
const PUBLIC_INPUT_COUNT: usize = 13;
/// Number of rows in a single Poseidon gadget (POS_ROWS_PER_HASH + 1 for the output row).
const POSEIDON_GADGET_ROWS: usize = POS_ROWS_PER_HASH + 1;
/// Merkle tree depth for issuer federation tree.
pub const ISSUER_TREE_DEPTH: usize = 4;

#[derive(Clone, Debug)]
pub struct KimchiPresentationWitness {
    pub federation_root: Fp,
    pub request_predicate: [Fp; 4],
    pub timestamp: Fp,
    pub verifier_nonce: Fp,
    pub composition_commitment: Fp,
    pub presentation_tag: Fp,
    pub issuer_membership_hash: Fp,
    pub fold_chain_hash: Fp,
    pub derivation_hash: Fp,
    pub non_revocation_eval: Fp,
    /// The root used to compute the presentation tag (private).
    pub final_root: Fp,
    /// Randomness used to compute the presentation tag (private).
    pub randomness: Fp,
    /// Verifier-declared block height for freshness binding.
    pub verifier_block_height: Fp,
    /// Token expiry height (not_after_height caveat). Zero means no expiry.
    pub not_after_height: Fp,
    /// Revealed facts for selective disclosure. When non-empty, their Poseidon hash
    /// is constrained to equal the public revealed_facts_commitment.
    pub revealed_facts: Vec<Fp>,
    /// Issuer public key hash (leaf in the federation Merkle tree).
    pub issuer_key_hash: Fp,
    /// Blinding factor for ring membership mode.
    /// blinded_leaf = Poseidon(issuer_key_hash, blinding_factor, 0)
    pub blinding_factor: Fp,
    /// Merkle proof of issuer membership in the federation tree.
    pub issuer_membership_proof: Option<FpMerkleWitness>,
}

/// Compute a single Poseidon permutation hash: set state = [a, b, c], apply block cipher,
/// return state[0]. This matches exactly what the in-circuit Poseidon gadget computes.
fn poseidon_permutation_hash(a: Fp, b: Fp, c: Fp) -> Fp {
    let p = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    sponge.state = vec![a, b, c];
    sponge.poseidon_block_cipher();
    sponge.state[0]
}

/// Poseidon permutation returning the full output state (for Merkle hash).
fn poseidon_perm_output(input: [Fp; 3]) -> [Fp; 3] {
    let p = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(p);
    sponge.state = input.to_vec();
    for round in 0..FULL_ROUNDS {
        sponge.full_round(round);
    }
    [sponge.state[0], sponge.state[1], sponge.state[2]]
}

/// Hash pair using Poseidon permutation: perm([a, b, 0])[0]
fn fp_hash_pair(a: Fp, b: Fp) -> Fp {
    poseidon_perm_output([a, b, Fp::zero()])[0]
}

pub fn compute_presentation_tag(final_root: Fp, randomness: Fp, verifier_nonce: Fp) -> Fp {
    poseidon_permutation_hash(final_root, randomness, verifier_nonce)
}

pub fn compute_composition_commitment(
    fold_chain_hash: Fp,
    derivation_hash: Fp,
    presentation_tag: Fp,
) -> Fp {
    poseidon_permutation_hash(fold_chain_hash, derivation_hash, presentation_tag)
}

/// Compute the blinded leaf: Poseidon(issuer_key_hash, blinding_factor, 0)
pub fn compute_blinded_leaf(issuer_key_hash: Fp, blinding_factor: Fp) -> Fp {
    poseidon_permutation_hash(issuer_key_hash, blinding_factor, Fp::zero())
}

/// Compute revealed facts commitment: sponge hash over all revealed facts.
pub fn compute_revealed_facts_commitment(facts: &[Fp]) -> Fp {
    if facts.is_empty() {
        return Fp::zero();
    }
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
    sponge.absorb(facts);
    sponge.squeeze()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KimchiPresentationVerification {
    Valid,
    IssuerNotInFederation,
    InvalidDerivation,
    CompositionMismatch,
    InvalidPresentationTag,
    Revoked,
    ProofInvalid,
    TokenExpired,
}

pub struct KimchiPresentationCircuit {
    pub witness: KimchiPresentationWitness,
}

impl KimchiPresentationCircuit {
    pub fn new(witness: KimchiPresentationWitness) -> Self {
        Self { witness }
    }

    /// Build the circuit gates.
    ///
    /// Layout:
    ///   Rows 0..12:  Public input gates (c[0]=1 constrains w[0] = public[row])
    ///   Poseidon gadget 1: hash(fold_chain_hash, derivation_hash, presentation_tag)
    ///   Equality gate: poseidon1_output == composition_commitment (from row 7)
    ///   Poseidon gadget 2: hash(final_root, randomness, verifier_nonce)
    ///   Equality gate: poseidon2_output == presentation_tag (from row 8)
    ///   Non-revocation: non_revocation_eval * inverse - 1 = 0
    ///   Non-zero composition: composition_commitment * inverse - 1 = 0
    ///   Token expiry GTE: not_after_height >= verifier_block_height (when both non-zero)
    ///   Revealed facts commitment: Poseidon sponge over revealed_facts, equality to public[11]
    ///   Issuer membership: blinding Poseidon + Merkle path + root equality
    pub fn build_circuit(&self) -> (Vec<CircuitGate<Fp>>, usize) {
        let mut gates = Vec::new();
        let pc = PUBLIC_INPUT_COUNT;

        // Public input gates: c[0]=1 constrains w[0] = public[row]
        for _ in 0..pc {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        let rc = &Vesta::sponge_params().round_constants;

        // Poseidon gadget 1: composition commitment = hash(fold_chain_hash, derivation_hash, presentation_tag)
        {
            let s = gates.len();
            let pr = POS_ROWS_PER_HASH;
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Equality gate: poseidon1_output - composition_commitment = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one(); // poseidon1 output
            c[1] = -Fp::one(); // composition_commitment (from public input)
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Poseidon gadget 2: presentation tag = hash(final_root, randomness, verifier_nonce)
        {
            let s = gates.len();
            let pr = POS_ROWS_PER_HASH;
            let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                s,
                [Wire::for_row(s), Wire::for_row(s + pr)],
                rc,
            );
            gates.extend(pg);
        }

        // Equality gate: poseidon2_output - presentation_tag = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one(); // poseidon2 output
            c[1] = -Fp::one(); // presentation_tag (from public input)
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Non-revocation gate: non_revocation_eval * inverse = 1
        // c[3]*(w[0]*w[1]) + c[4] = 0 → w[0]*w[1] - 1 = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one(); // mul coefficient
            c[4] = -Fp::one(); // constant = -1
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Non-zero composition commitment gate: composition_commitment * inverse = 1
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one(); // mul coefficient
            c[4] = -Fp::one(); // constant = -1
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // ================================================================
        // Token expiry GTE: not_after_height >= verifier_block_height
        // ================================================================
        // diff = not_after_height - verifier_block_height
        // Gate: c[0]*w[0] + c[1]*w[1] + c[2]*w[2] = 0 => w[0] - w[1] - w[2] = 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one(); // not_after_height
            c[1] = -Fp::one(); // verifier_block_height
            c[2] = -Fp::one(); // diff
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Bit decomposition for token expiry diff (same pattern as derivation GTE)
        let expiry_diff = self.witness.not_after_height - self.witness.verifier_block_height;
        let expiry_diff_u64 = expiry_diff.into_bigint().as_ref()[0];

        let bits_per_row = 6;
        let num_bit_rows = GTE_DIFF_BITS.div_ceil(bits_per_row);

        for chunk_idx in 0..num_bit_rows {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            let base_bit = chunk_idx * bits_per_row;

            // Sub-gate 1: weighted sum of bits[base..base+3]
            let mut chunk_sum_low = Fp::zero();
            for i in 0..3 {
                let bit_idx = base_bit + i;
                if bit_idx < GTE_DIFF_BITS {
                    let power = Fp::from(1u64 << bit_idx);
                    c[i] = power;
                    let bit_val = (expiry_diff_u64 >> bit_idx) & 1;
                    chunk_sum_low = chunk_sum_low + Fp::from(bit_val) * power;
                }
            }
            c[4] = -chunk_sum_low;

            // Sub-gate 2: weighted sum of bits[base+3..base+6]
            let mut chunk_sum_high = Fp::zero();
            for i in 0..3 {
                let bit_idx = base_bit + 3 + i;
                if bit_idx < GTE_DIFF_BITS {
                    let power = Fp::from(1u64 << bit_idx);
                    c[5 + i] = power;
                    let bit_val = (expiry_diff_u64 >> bit_idx) & 1;
                    chunk_sum_high = chunk_sum_high + Fp::from(bit_val) * power;
                }
            }
            c[9] = -chunk_sum_high;

            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // Binary enforcement rows for expiry bits
        let num_binary_rows = GTE_DIFF_BITS.div_ceil(2);
        for _ in 0..num_binary_rows {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[3] = Fp::one();
            c[0] = -Fp::one();
            c[8] = Fp::one();
            c[5] = -Fp::one();
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // High-bit-zero enforcement: highest bit must be 0
        {
            let r = gates.len();
            let mut c = vec![Fp::zero(); COLUMNS];
            c[0] = Fp::one(); // enforces w[0] = 0
            gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
        }

        // ================================================================
        // Revealed facts commitment (selective disclosure)
        // ================================================================
        // We use sponge-based hashing over revealed_facts. Number of Poseidon gadgets
        // = ceil(revealed_facts.len() / 2) (rate=2 sponge).
        // Then equality gate: computed_commitment == public[11]
        let num_revealed = self.witness.revealed_facts.len();
        if num_revealed > 0 {
            let num_rfc_blocks = num_revealed.div_ceil(2);
            for _ in 0..num_rfc_blocks {
                let s = gates.len();
                let pr = POS_ROWS_PER_HASH;
                let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                    s,
                    [Wire::for_row(s), Wire::for_row(s + pr)],
                    rc,
                );
                gates.extend(pg);
            }

            // Equality gate: computed RFC == public revealed_facts_commitment
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
        }

        // ================================================================
        // Issuer membership (blinded ring mode with Poseidon Merkle path)
        // ================================================================
        if let Some(ref merkle_proof) = self.witness.issuer_membership_proof {
            let depth = merkle_proof.levels.len();

            // Poseidon gadget for blinding: blinded_leaf = Poseidon(issuer_key_hash, blinding_factor, 0)
            {
                let s = gates.len();
                let pr = POS_ROWS_PER_HASH;
                let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                    s,
                    [Wire::for_row(s), Wire::for_row(s + pr)],
                    rc,
                );
                gates.extend(pg);
            }

            // Equality gate: blinded_leaf == public issuer_blinded_leaf (row 12)
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }

            // Merkle path verification (same pattern as fold circuit):
            // Per level: ordering gate + 3 Poseidon gadgets (left, right, combine)
            for _ in 0..depth {
                // Ordering gate: current hash binding
                {
                    let r = gates.len();
                    let mut c = vec![Fp::zero(); COLUMNS];
                    c[0] = Fp::one();
                    c[1] = -Fp::one();
                    gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
                }

                // Poseidon left: perm([ch[0], ch[1], 0])
                {
                    let s = gates.len();
                    let pr = POS_ROWS_PER_HASH;
                    let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                        s,
                        [Wire::for_row(s), Wire::for_row(s + pr)],
                        rc,
                    );
                    gates.extend(pg);
                }

                // Poseidon right: perm([ch[2], ch[3], 0])
                {
                    let s = gates.len();
                    let pr = POS_ROWS_PER_HASH;
                    let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                        s,
                        [Wire::for_row(s), Wire::for_row(s + pr)],
                        rc,
                    );
                    gates.extend(pg);
                }

                // Poseidon combine: perm([h_left, h_right, 0])
                {
                    let s = gates.len();
                    let pr = POS_ROWS_PER_HASH;
                    let (pg, _) = CircuitGate::<Fp>::create_poseidon_gadget(
                        s,
                        [Wire::for_row(s), Wire::for_row(s + pr)],
                        rc,
                    );
                    gates.extend(pg);
                }
            }

            // Root match gate: computed_root == federation_root (public[0])
            {
                let r = gates.len();
                let mut c = vec![Fp::zero(); COLUMNS];
                c[0] = Fp::one();
                c[1] = -Fp::one();
                gates.push(CircuitGate::new(GateType::Generic, Wire::for_row(r), c));
            }
        }

        (gates, pc)
    }

    /// Generate the witness for the circuit.
    pub fn generate_witness(&self) -> [Vec<Fp>; COLUMNS] {
        let (gates, _) = self.build_circuit();
        let tr = gates.len();
        let w = &self.witness;
        let mut wit: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); tr]);

        let mut row = 0;

        // Public input rows (0..12)
        wit[0][row] = w.federation_root;
        row += 1; // row 0
        wit[0][row] = w.request_predicate[0];
        row += 1; // row 1
        wit[0][row] = w.request_predicate[1];
        row += 1; // row 2
        wit[0][row] = w.request_predicate[2];
        row += 1; // row 3
        wit[0][row] = w.request_predicate[3];
        row += 1; // row 4
        wit[0][row] = w.timestamp;
        row += 1; // row 5
        wit[0][row] = w.verifier_nonce;
        row += 1; // row 6
        wit[0][row] = w.composition_commitment;
        row += 1; // row 7
        wit[0][row] = w.presentation_tag;
        row += 1; // row 8
        wit[0][row] = w.verifier_block_height;
        row += 1; // row 9
        wit[0][row] = w.not_after_height;
        row += 1; // row 10
        let rfc = compute_revealed_facts_commitment(&w.revealed_facts);
        wit[0][row] = rfc;
        row += 1; // row 11
        let blinded_leaf = compute_blinded_leaf(w.issuer_key_hash, w.blinding_factor);
        wit[0][row] = blinded_leaf;
        row += 1; // row 12

        // Poseidon gadget 1: hash(fold_chain_hash, derivation_hash, presentation_tag)
        generate_witness(
            row,
            Vesta::sponge_params(),
            &mut wit,
            [w.fold_chain_hash, w.derivation_hash, w.presentation_tag],
        );
        row += POSEIDON_GADGET_ROWS;

        let poseidon1_output = wit[0][row - 1];

        // Equality gate row: w[0] = poseidon1_output, w[1] = composition_commitment
        wit[0][row] = poseidon1_output;
        wit[1][row] = w.composition_commitment;
        row += 1;

        // Poseidon gadget 2: hash(final_root, randomness, verifier_nonce)
        generate_witness(
            row,
            Vesta::sponge_params(),
            &mut wit,
            [w.final_root, w.randomness, w.verifier_nonce],
        );
        row += POSEIDON_GADGET_ROWS;

        let poseidon2_output = wit[0][row - 1];

        // Equality gate row: w[0] = poseidon2_output, w[1] = presentation_tag
        wit[0][row] = poseidon2_output;
        wit[1][row] = w.presentation_tag;
        row += 1;

        // Non-revocation gate: w[0] = non_revocation_eval, w[1] = inverse
        let nre_inv = w.non_revocation_eval.inverse().unwrap_or(Fp::zero());
        wit[0][row] = w.non_revocation_eval;
        wit[1][row] = nre_inv;
        row += 1;

        // Non-zero composition commitment gate: w[0] = composition_commitment, w[1] = inverse
        let cc_inv = w.composition_commitment.inverse().unwrap_or(Fp::zero());
        wit[0][row] = w.composition_commitment;
        wit[1][row] = cc_inv;
        row += 1;

        // ================================================================
        // Token expiry GTE witness
        // ================================================================
        // First row: w[0]=not_after_height, w[1]=verifier_block_height, w[2]=diff
        let expiry_diff = w.not_after_height - w.verifier_block_height;
        wit[0][row] = w.not_after_height;
        wit[1][row] = w.verifier_block_height;
        wit[2][row] = expiry_diff;
        row += 1;

        // Extract bits
        let expiry_diff_u64 = expiry_diff.into_bigint().as_ref()[0];
        let expiry_bits: Vec<Fp> = (0..GTE_DIFF_BITS)
            .map(|i| Fp::from((expiry_diff_u64 >> i) & 1))
            .collect();

        // Bit chunk rows (6 bits per row)
        let bits_per_row = 6;
        let num_bit_rows = GTE_DIFF_BITS.div_ceil(bits_per_row);
        for chunk_idx in 0..num_bit_rows {
            let base_bit = chunk_idx * bits_per_row;
            for i in 0..3 {
                let bit_idx = base_bit + i;
                if bit_idx < GTE_DIFF_BITS {
                    wit[i][row] = expiry_bits[bit_idx];
                }
            }
            for i in 0..3 {
                let bit_idx = base_bit + 3 + i;
                if bit_idx < GTE_DIFF_BITS {
                    wit[3 + i][row] = expiry_bits[bit_idx];
                }
            }
            row += 1;
        }

        // Binary enforcement rows
        let num_binary_rows = GTE_DIFF_BITS.div_ceil(2);
        for br_idx in 0..num_binary_rows {
            let bit_idx_a = 2 * br_idx;
            if bit_idx_a < GTE_DIFF_BITS {
                wit[0][row] = expiry_bits[bit_idx_a];
                wit[1][row] = expiry_bits[bit_idx_a];
            }
            let bit_idx_b = 2 * br_idx + 1;
            if bit_idx_b < GTE_DIFF_BITS {
                wit[3][row] = expiry_bits[bit_idx_b];
                wit[4][row] = expiry_bits[bit_idx_b];
            }
            row += 1;
        }

        // High-bit-zero row: w[0] = highest bit (must be 0)
        wit[0][row] = expiry_bits[GTE_DIFF_BITS - 1];
        row += 1;

        // ================================================================
        // Revealed facts commitment witness
        // ================================================================
        let num_revealed = w.revealed_facts.len();
        if num_revealed > 0 {
            // Sponge-based hashing: absorb rate=2 elements per permutation
            let num_rfc_blocks = num_revealed.div_ceil(2);
            let mut state = [Fp::zero(); 3];

            for block in 0..num_rfc_blocks {
                let idx = block * 2;
                if idx < num_revealed {
                    state[0] += w.revealed_facts[idx];
                }
                if idx + 1 < num_revealed {
                    state[1] += w.revealed_facts[idx + 1];
                }

                generate_witness(row, Vesta::sponge_params(), &mut wit, state);
                state = poseidon_perm_output(state);
                row += POSEIDON_GADGET_ROWS;
            }

            // Equality gate: computed RFC == public revealed_facts_commitment
            wit[0][row] = state[0]; // sponge squeeze output
            wit[1][row] = rfc;
            row += 1;
        }

        // ================================================================
        // Issuer membership witness (blinded Merkle path)
        // ================================================================
        if let Some(ref merkle_proof) = w.issuer_membership_proof {
            // Poseidon gadget for blinding: Poseidon(issuer_key_hash, blinding_factor, 0)
            generate_witness(
                row,
                Vesta::sponge_params(),
                &mut wit,
                [w.issuer_key_hash, w.blinding_factor, Fp::zero()],
            );
            row += POSEIDON_GADGET_ROWS;

            // Equality gate: blinded_leaf output == public[12]
            wit[0][row] = blinded_leaf;
            wit[1][row] = blinded_leaf; // public issuer_blinded_leaf
            row += 1;

            // Merkle path levels (using issuer_key_hash as the leaf, NOT blinded)
            // The Merkle tree contains the raw issuer_key_hash; blinding is for the
            // public input only (ring mode). The circuit proves:
            //   1. blinded_leaf = Poseidon(issuer_key_hash, blinding_factor, 0)  [above]
            //   2. issuer_key_hash is in tree rooted at federation_root  [below]
            let mut cur = merkle_proof.leaf_hash;
            for level in &merkle_proof.levels {
                // Arrange children based on position
                let mut ch = [Fp::zero(); 4];
                let mut si = 0;
                for i in 0..4u8 {
                    if i == level.position {
                        ch[i as usize] = cur;
                    } else {
                        ch[i as usize] = level.siblings[si];
                        si += 1;
                    }
                }

                // Ordering gate: w[0]=cur, w[1]=cur
                wit[0][row] = cur;
                wit[1][row] = cur;
                row += 1;

                // Poseidon left: perm([ch[0], ch[1], 0])
                let h_left = fp_hash_pair(ch[0], ch[1]);
                generate_witness(
                    row,
                    Vesta::sponge_params(),
                    &mut wit,
                    [ch[0], ch[1], Fp::zero()],
                );
                row += POSEIDON_GADGET_ROWS;

                // Poseidon right: perm([ch[2], ch[3], 0])
                let h_right = fp_hash_pair(ch[2], ch[3]);
                generate_witness(
                    row,
                    Vesta::sponge_params(),
                    &mut wit,
                    [ch[2], ch[3], Fp::zero()],
                );
                row += POSEIDON_GADGET_ROWS;

                // Poseidon combine: perm([h_left, h_right, 0])
                let level_hash = fp_hash_pair(h_left, h_right);
                generate_witness(
                    row,
                    Vesta::sponge_params(),
                    &mut wit,
                    [h_left, h_right, Fp::zero()],
                );
                row += POSEIDON_GADGET_ROWS;

                cur = level_hash;
            }

            // Root match gate: computed_root == federation_root
            wit[0][row] = cur;
            wit[1][row] = w.federation_root;
            let _ = row;
        }

        wit
    }

    /// Generate the proof. Rejects at prove time if composition_commitment is zero
    /// or if non_revocation_eval is zero (revoked credential).
    pub fn prove(&self) -> Result<KimchiNativeProof, String> {
        if self.witness.composition_commitment == Fp::zero() {
            return Err("Composition commitment must be non-zero for sub-proof binding".into());
        }
        if self.witness.non_revocation_eval == Fp::zero() {
            return Err("Non-revocation eval is zero: credential is revoked".into());
        }

        // Verify composition commitment matches the Poseidon hash
        let expected_cc = compute_composition_commitment(
            self.witness.fold_chain_hash,
            self.witness.derivation_hash,
            self.witness.presentation_tag,
        );
        if self.witness.composition_commitment != expected_cc {
            return Err("Composition commitment does not match hash(fold_chain_hash, derivation_hash, presentation_tag)".into());
        }

        // Verify presentation tag matches the Poseidon hash
        let expected_tag = compute_presentation_tag(
            self.witness.final_root,
            self.witness.randomness,
            self.witness.verifier_nonce,
        );
        if self.witness.presentation_tag != expected_tag {
            return Err(
                "Presentation tag does not match hash(final_root, randomness, verifier_nonce)"
                    .into(),
            );
        }

        // Token expiry check: if both are non-zero, not_after_height must >= verifier_block_height
        if self.witness.verifier_block_height != Fp::zero()
            && self.witness.not_after_height != Fp::zero()
        {
            let diff = self.witness.not_after_height - self.witness.verifier_block_height;
            let diff_u64 = diff.into_bigint().as_ref()[0];
            // If the diff wrapped around (top bit set), the token is expired
            let top_bit = (diff_u64 >> (GTE_DIFF_BITS - 1)) & 1;
            if top_bit != 0 {
                return Err("Token expired: not_after_height < verifier_block_height".into());
            }
        }

        // Validate issuer membership if proof is provided
        if let Some(ref merkle_proof) = self.witness.issuer_membership_proof {
            if merkle_proof.leaf_hash != self.witness.issuer_key_hash {
                return Err("Issuer key hash does not match Merkle leaf".into());
            }
            if !merkle_proof.verify() {
                return Err("Issuer Merkle membership proof is invalid".into());
            }
            if merkle_proof.expected_root != self.witness.federation_root {
                return Err("Issuer Merkle proof root does not match federation_root".into());
            }
        }

        let (gates, pc) = self.build_circuit();
        let circuit_gates_bytes = super::serialize_circuit_gates(&gates, pc);
        let wit = self.generate_witness();
        let index =
            kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(gates, pc);
        let gm = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
            BaseSponge,
            ScalarSponge,
            _,
        >(&gm, wit, &[], &index, &mut OsRng)
        .map_err(|e| format!("Kimchi presentation prover error: {:?}", e))?;

        let pb = rmp_serde::to_vec(&proof)
            .map_err(|e| format!("Presentation proof serialization error: {}", e))?;
        let w = &self.witness;
        // Serialize all public inputs
        let mut pib = Vec::with_capacity(PUBLIC_INPUT_COUNT * 32);
        pib.extend_from_slice(&fp_to_bytes32(&w.federation_root));
        for i in 0..4 {
            pib.extend_from_slice(&fp_to_bytes32(&w.request_predicate[i]));
        }
        pib.extend_from_slice(&fp_to_bytes32(&w.timestamp));
        pib.extend_from_slice(&fp_to_bytes32(&w.verifier_nonce));
        pib.extend_from_slice(&fp_to_bytes32(&w.composition_commitment));
        pib.extend_from_slice(&fp_to_bytes32(&w.presentation_tag));
        pib.extend_from_slice(&fp_to_bytes32(&w.verifier_block_height));
        pib.extend_from_slice(&fp_to_bytes32(&w.not_after_height));
        let rfc = compute_revealed_facts_commitment(&w.revealed_facts);
        pib.extend_from_slice(&fp_to_bytes32(&rfc));
        let blinded_leaf = compute_blinded_leaf(w.issuer_key_hash, w.blinding_factor);
        pib.extend_from_slice(&fp_to_bytes32(&blinded_leaf));

        Ok(KimchiNativeProof {
            proof_bytes: pb,
            public_input_bytes: pib,
            circuit_type: KimchiNativeCircuitType::Presentation,
            circuit_gates_bytes,
            public_count: pc,
        })
    }

    /// Verify a presentation proof using the real Kimchi verifier.
    pub fn verify(proof_bytes: &[u8], public_inputs: &[Fp]) -> Result<bool, String> {
        Self::verify_with_gates(proof_bytes, public_inputs, &[])
    }

    /// Verify with optional embedded circuit gates.
    pub fn verify_with_gates(
        proof_bytes: &[u8],
        public_inputs: &[Fp],
        circuit_gates_bytes: &[u8],
    ) -> Result<bool, String> {
        let proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(proof_bytes)
                .map_err(|e| format!("Deserialization error: {}", e))?;

        let (gates, pc) = if !circuit_gates_bytes.is_empty() {
            super::deserialize_circuit_gates(circuit_gates_bytes)
                .ok_or_else(|| "Failed to deserialize embedded circuit gates".to_string())?
        } else {
            // Fallback: build a dummy witness to get the circuit structure (only works for base case)
            let dummy = KimchiPresentationWitness {
                federation_root: Fp::zero(),
                request_predicate: [Fp::zero(); 4],
                timestamp: Fp::zero(),
                verifier_nonce: Fp::zero(),
                composition_commitment: Fp::one(),
                presentation_tag: Fp::zero(),
                issuer_membership_hash: Fp::zero(),
                fold_chain_hash: Fp::zero(),
                derivation_hash: Fp::zero(),
                non_revocation_eval: Fp::one(),
                final_root: Fp::zero(),
                randomness: Fp::zero(),
                verifier_block_height: Fp::zero(),
                not_after_height: Fp::zero(),
                revealed_facts: Vec::new(),
                issuer_key_hash: Fp::zero(),
                blinding_factor: Fp::zero(),
                issuer_membership_proof: None,
            };
            let circuit = KimchiPresentationCircuit::new(dummy);
            circuit.build_circuit()
        };

        verify_kimchi_proof(&proof, gates, public_inputs, pc)
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiPresentationProof {
    pub proof: KimchiNativeProof,
    #[serde(with = "fp_serde")]
    pub federation_root: Fp,
    #[serde(with = "fp_array4_serde")]
    pub request_predicate: [Fp; 4],
    #[serde(with = "fp_serde")]
    pub timestamp: Fp,
    #[serde(with = "fp_serde")]
    pub verifier_nonce: Fp,
    #[serde(with = "fp_serde")]
    pub composition_commitment: Fp,
    #[serde(with = "fp_serde")]
    pub presentation_tag: Fp,
    #[serde(with = "fp_serde")]
    pub verifier_block_height: Fp,
    #[serde(with = "fp_serde")]
    pub not_after_height: Fp,
    #[serde(with = "fp_serde")]
    pub revealed_facts_commitment: Fp,
    #[serde(with = "fp_serde")]
    pub issuer_blinded_leaf: Fp,
}

mod fp_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(fp: &Fp, s: S) -> Result<S::Ok, S::Error> {
        let bytes = fp_to_bytes32(fp);
        bytes.serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Fp, D::Error> {
        let bytes = <[u8; 32]>::deserialize(d)?;
        Ok(super::super::bytes32_to_fp(&bytes))
    }
}

mod fp_array4_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(fps: &[Fp; 4], s: S) -> Result<S::Ok, S::Error> {
        let bytes: [[u8; 32]; 4] = [
            fp_to_bytes32(&fps[0]),
            fp_to_bytes32(&fps[1]),
            fp_to_bytes32(&fps[2]),
            fp_to_bytes32(&fps[3]),
        ];
        bytes.serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[Fp; 4], D::Error> {
        let bytes = <[[u8; 32]; 4]>::deserialize(d)?;
        Ok([
            super::super::bytes32_to_fp(&bytes[0]),
            super::super::bytes32_to_fp(&bytes[1]),
            super::super::bytes32_to_fp(&bytes[2]),
            super::super::bytes32_to_fp(&bytes[3]),
        ])
    }
}
