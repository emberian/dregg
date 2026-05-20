//! SP1 Guest Program: Verifies a pyana STARK proof inside the zkVM.
//!
//! This program runs inside SP1's RISC-V zkVM. It:
//! 1. Reads a serialized pyana STARK proof from the host
//! 2. Reads the public inputs (leaf hash + Merkle root)
//! 3. Runs the full STARK verifier (Merkle commitments, FRI, Fiat-Shamir)
//! 4. Commits the verification result and public inputs as public outputs
//!
//! SP1 then wraps this execution in a Groth16 proof (~200k gas to verify on EVM).

#![no_main]
sp1_zkvm::entrypoint!(main);

use serde::{Deserialize, Serialize};

// ============================================================================
// Minimal STARK verifier types (mirrored from circuit crate for zkVM compat)
// ============================================================================

/// BabyBear field element (p = 2^31 - 2^27 + 1 = 2013265921)
const BABYBEAR_P: u32 = 2013265921;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct BabyBear(u32);

impl BabyBear {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);

    fn new(v: u32) -> Self {
        Self(v % BABYBEAR_P)
    }

    fn inverse(self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        // Fermat's little theorem: a^(p-2) mod p
        Some(self.pow(BABYBEAR_P - 2))
    }

    fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                result = result * base;
            }
            base = base * base;
            exp >>= 1;
        }
        result
    }
}

impl core::ops::Add for BabyBear {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let sum = (self.0 as u64) + (rhs.0 as u64);
        Self((sum % BABYBEAR_P as u64) as u32)
    }
}

impl core::ops::Sub for BabyBear {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let diff = (self.0 as u64) + (BABYBEAR_P as u64) - (rhs.0 as u64);
        Self((diff % BABYBEAR_P as u64) as u32)
    }
}

impl core::ops::Mul for BabyBear {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let prod = (self.0 as u64) * (rhs.0 as u64);
        Self((prod % BABYBEAR_P as u64) as u32)
    }
}

// ============================================================================
// STARK proof structure (wire-compatible with circuit crate)
// ============================================================================

#[derive(Clone, Debug, Serialize, Deserialize)]
struct StarkProof {
    trace_commitment: [u8; 32],
    constraint_commitment: [u8; 32],
    fri_commitments: Vec<[u8; 32]>,
    fri_final_poly: Vec<u32>,
    query_proofs: Vec<QueryProof>,
    public_inputs: Vec<u32>,
    trace_len: usize,
    num_cols: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct QueryProof {
    index: usize,
    trace_values: Vec<u32>,
    trace_path: Vec<[u8; 32]>,
    next_trace_values: Vec<u32>,
    next_trace_path: Vec<[u8; 32]>,
    constraint_value: u32,
    constraint_path: Vec<[u8; 32]>,
    constraint_sibling_value: u32,
    constraint_sibling_pos: usize,
    constraint_sibling_path: Vec<[u8; 32]>,
    fri_layers: Vec<FriLayerQuery>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct FriLayerQuery {
    query_pos: usize,
    query_value: u32,
    query_path: Vec<[u8; 32]>,
    sibling_pos: usize,
    sibling_value: u32,
    sibling_path: Vec<[u8; 32]>,
}

// ============================================================================
// Fiat-Shamir transcript (must match prover exactly)
// ============================================================================

struct Transcript {
    hasher: blake3::Hasher,
    counter: u64,
}

impl Transcript {
    fn new(domain_sep: &[u8]) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-stark-v1:");
        hasher.update(domain_sep);
        Self { hasher, counter: 0 }
    }

    fn absorb_field(&mut self, val: BabyBear) {
        self.hasher.update(&val.0.to_le_bytes());
    }

    fn absorb_hash(&mut self, h: &[u8; 32]) {
        self.hasher.update(h);
    }

    fn squeeze_field(&mut self) -> BabyBear {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        BabyBear::new(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn squeeze_index(&mut self, bound: usize) -> usize {
        self.counter += 1;
        let mut sh = self.hasher.clone();
        sh.update(b"squeeze-idx:");
        sh.update(&self.counter.to_le_bytes());
        let hash = sh.finalize();
        let bytes = hash.as_bytes();
        let val = u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        (val as usize) % bound
    }
}

// ============================================================================
// Merkle tree verification
// ============================================================================

fn hash_leaf(value: BabyBear) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"stark-leaf:");
    hasher.update(&value.0.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn hash_leaf_multi(values: &[BabyBear]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"stark-leaf:");
    for v in values {
        hasher.update(&v.0.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"stark-node:");
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

fn verify_merkle_proof(root: &[u8; 32], leaf_hash: &[u8; 32], index: usize, path: &[[u8; 32]]) -> bool {
    let mut current = *leaf_hash;
    let mut idx = index;
    for sibling in path {
        current = if idx & 1 == 0 {
            hash_node(&current, sibling)
        } else {
            hash_node(sibling, &current)
        };
        idx >>= 1;
    }
    &current == root
}

// ============================================================================
// STARK Verifier (runs inside zkVM)
// ============================================================================

const BLOWUP: usize = 4;

fn verify_stark(proof: &StarkProof, public_inputs: &[BabyBear]) -> Result<(), &'static str> {
    let num_cols = proof.num_cols;
    let trace_len = proof.trace_len;
    let domain_size = trace_len * BLOWUP;

    // Check public inputs match
    let proof_pis: Vec<BabyBear> = proof.public_inputs.iter().map(|&v| BabyBear(v)).collect();
    if proof_pis != public_inputs {
        return Err("public inputs mismatch");
    }

    // Rebuild Fiat-Shamir transcript
    let mut transcript = Transcript::new(b"merkle-stark");
    transcript.absorb_hash(&proof.trace_commitment);
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    let alpha = transcript.squeeze_field();
    transcript.absorb_hash(&proof.constraint_commitment);

    // Extract FRI betas
    let mut fri_betas = Vec::new();
    for commitment in &proof.fri_commitments {
        fri_betas.push(transcript.squeeze_field());
        transcript.absorb_hash(commitment);
    }

    let trace_points: Vec<BabyBear> = (1..=trace_len as u32).map(BabyBear::new).collect();
    let eval_points: Vec<BabyBear> = (1..=domain_size as u32).map(BabyBear::new).collect();

    // Verify each query
    for query in &proof.query_proofs {
        let idx = transcript.squeeze_index(domain_size);
        if query.index != idx {
            return Err("query index mismatch");
        }

        // Verify trace Merkle proof
        let trace_vals: Vec<BabyBear> = query.trace_values.iter().map(|&v| BabyBear(v)).collect();
        if trace_vals.len() != num_cols {
            return Err("wrong number of trace values");
        }
        if !verify_merkle_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&trace_vals),
            idx,
            &query.trace_path,
        ) {
            return Err("trace merkle proof failed");
        }

        // Verify constraint Merkle proof
        let constraint_val = BabyBear(query.constraint_value);
        if !verify_merkle_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_val),
            idx,
            &query.constraint_path,
        ) {
            return Err("constraint merkle proof failed");
        }

        // Verify next trace
        let next_idx = if idx + 1 < domain_size { idx + 1 } else { 0 };
        let next_trace_vals: Vec<BabyBear> =
            query.next_trace_values.iter().map(|&v| BabyBear(v)).collect();
        if next_trace_vals.len() != num_cols {
            return Err("wrong number of next trace values");
        }
        if !verify_merkle_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&next_trace_vals),
            next_idx,
            &query.next_trace_path,
        ) {
            return Err("next trace merkle proof failed");
        }

        // Evaluate constraint at query point (MerkleStarkAir)
        let x = eval_points[idx];
        let mut z = BabyBear::ONE;
        for &tp in &trace_points {
            z = z * (x - tp);
        }

        // MerkleStarkAir constraint evaluation
        let (current, sib0, sib1, sib2, position, parent) = (
            trace_vals[0],
            trace_vals[1],
            trace_vals[2],
            trace_vals[3],
            trace_vals[4],
            trace_vals[5],
        );
        let c1 = parent - (current + sib0 + sib1 + sib2 + position);
        let c2 = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));
        let constraint_at_x = c1 + alpha * c2;

        if constraint_val * z != constraint_at_x {
            return Err("constraint consistency check failed");
        }

        // FRI verification
        let first_half = domain_size / 2;
        let constraint_sib_val = BabyBear(query.constraint_sibling_value);
        if !verify_merkle_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_sib_val),
            query.constraint_sibling_pos,
            &query.constraint_sibling_path,
        ) {
            return Err("FRI constraint sibling merkle proof failed");
        }

        let (even_val, odd_val) = if idx < first_half {
            (constraint_val, constraint_sib_val)
        } else {
            (constraint_sib_val, constraint_val)
        };

        if !fri_betas.is_empty() {
            let expected_folded = even_val + fri_betas[0] * odd_val;
            if !proof.fri_commitments.is_empty() {
                if query.fri_layers.is_empty() {
                    return Err("FRI missing layer 0");
                }
                let layer0 = &query.fri_layers[0];
                if layer0.query_pos != idx % first_half {
                    return Err("FRI layer 0 position mismatch");
                }
                if BabyBear(layer0.query_value) != expected_folded {
                    return Err("FRI folding check failed at layer 0");
                }
                if !verify_merkle_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear(layer0.query_value)),
                    layer0.query_pos,
                    &layer0.query_path,
                ) {
                    return Err("FRI layer 0 merkle proof failed");
                }
                if !verify_merkle_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear(layer0.sibling_value)),
                    layer0.sibling_pos,
                    &layer0.sibling_path,
                ) {
                    return Err("FRI layer 0 sibling merkle proof failed");
                }
            }
        }

        // Verify subsequent FRI layers
        for k in 0..query.fri_layers.len().saturating_sub(1) {
            let cl = &query.fri_layers[k];
            let nl = &query.fri_layers[k + 1];
            let (even_k, odd_k) = if cl.query_pos < cl.sibling_pos {
                (BabyBear(cl.query_value), BabyBear(cl.sibling_value))
            } else {
                (BabyBear(cl.sibling_value), BabyBear(cl.query_value))
            };
            let beta_idx = k + 1;
            if beta_idx >= fri_betas.len() {
                return Err("FRI not enough betas");
            }
            let expected_next = even_k + fri_betas[beta_idx] * odd_k;
            if nl.query_pos != cl.query_pos.min(cl.sibling_pos) {
                return Err("FRI layer position mismatch");
            }
            if BabyBear(nl.query_value) != expected_next {
                return Err("FRI folding check failed");
            }
            if beta_idx < proof.fri_commitments.len() {
                if !verify_merkle_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear(nl.query_value)),
                    nl.query_pos,
                    &nl.query_path,
                ) {
                    return Err("FRI layer merkle proof failed");
                }
                if !verify_merkle_proof(
                    &proof.fri_commitments[beta_idx],
                    &hash_leaf(BabyBear(nl.sibling_value)),
                    nl.sibling_pos,
                    &nl.sibling_path,
                ) {
                    return Err("FRI layer sibling merkle proof failed");
                }
            }
        }

        // Check final polynomial
        if let Some(last) = query.fri_layers.last() {
            if last.query_pos < proof.fri_final_poly.len()
                && last.query_value != proof.fri_final_poly[last.query_pos]
            {
                return Err("FRI final poly mismatch");
            }
            if last.sibling_pos < proof.fri_final_poly.len()
                && last.sibling_value != proof.fri_final_poly[last.sibling_pos]
            {
                return Err("FRI final poly sibling mismatch");
            }
        }
    }

    if proof.fri_final_poly.len() > 4 {
        return Err("FRI final polynomial too large");
    }

    Ok(())
}

// ============================================================================
// SP1 Guest Entry Point
// ============================================================================

/// Public output committed by the guest program.
#[derive(Serialize, Deserialize)]
struct VerificationOutput {
    /// Whether the STARK proof verified successfully.
    valid: bool,
    /// The public inputs from the verified proof (leaf hash + Merkle root).
    public_inputs: Vec<u32>,
}

fn main() {
    // Read the serialized STARK proof from SP1 stdin
    let proof: StarkProof = sp1_zkvm::io::read();

    // Read the expected public inputs
    let public_input_values: Vec<u32> = sp1_zkvm::io::read();
    let public_inputs: Vec<BabyBear> = public_input_values.iter().map(|&v| BabyBear(v)).collect();

    // Verify the STARK proof
    let valid = verify_stark(&proof, &public_inputs).is_ok();

    // Commit the verification result as public output.
    // On-chain, the verifier contract checks these committed values.
    let output = VerificationOutput {
        valid,
        public_inputs: public_input_values,
    };
    sp1_zkvm::io::commit(&output);
}
