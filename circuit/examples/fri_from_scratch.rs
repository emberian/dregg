//! # FRI From Scratch
//!
//! A self-contained reference implementation of a STARK prover/verifier using FRI
//! (Fast Reed-Solomon IOP of Proximity) over the BabyBear field.
//!
//! This is pedagogical code — the production system uses Plonky3.
//! Kept as a readable, annotated example of how FRI works from first principles.

use pyana_circuit::field::{BabyBear, BABYBEAR_P};
use serde::{Deserialize, Serialize};

// ============================================================================
// Polynomial operations over BabyBear
// ============================================================================

fn poly_eval(coeffs: &[BabyBear], x: BabyBear) -> BabyBear {
    let mut result = BabyBear::ZERO;
    for &c in coeffs.iter().rev() {
        result = result * x + c;
    }
    result
}

/// Primitive root of the BabyBear multiplicative group.
/// 31 is a generator of Z_p^* where p = 2013265921.
/// The group order is p-1 = 2013265920 = 2^27 * 3 * 5.
/// Verified: 31^((p-1)/2) != 1, 31^((p-1)/3) != 1, 31^((p-1)/5) != 1.
const BABYBEAR_PRIMITIVE_ROOT: u32 = 31;

/// Get a principal n-th root of unity where n = 2^log_n.
/// BabyBear supports up to 2^27-th roots of unity.
fn get_root_of_unity(log_n: u32) -> BabyBear {
    assert!(
        log_n <= 27,
        "BabyBear only supports roots of unity up to 2^27"
    );
    // omega = g^((p-1) / 2^log_n) where g = 31 (primitive root)
    let exp = (BABYBEAR_P - 1) / (1u32 << log_n);
    BabyBear::new(BABYBEAR_PRIMITIVE_ROOT).pow(exp)
}

/// Build a multiplicative evaluation domain of size 2^log_n using roots of unity.
/// Returns the domain {1, omega, omega^2, ..., omega^(n-1)} where omega^n = 1.
fn build_evaluation_domain(num_points: usize) -> Vec<BabyBear> {
    assert!(
        num_points.is_power_of_two(),
        "Domain size must be a power of two"
    );
    let log_n = num_points.trailing_zeros();
    let omega = get_root_of_unity(log_n);
    let mut domain = Vec::with_capacity(num_points);
    let mut x = BabyBear::ONE;
    for _ in 0..num_points {
        domain.push(x);
        x = x * omega;
    }
    domain
}

fn interpolate(xs: &[BabyBear], ys: &[BabyBear]) -> Vec<BabyBear> {
    let n = xs.len();
    assert_eq!(n, ys.len());
    if n == 0 {
        return vec![];
    }
    let mut result = vec![BabyBear::ZERO; n];
    for i in 0..n {
        let mut basis = vec![BabyBear::ONE];
        let mut denom = BabyBear::ONE;
        for j in 0..n {
            if i == j {
                continue;
            }
            let mut new_basis = vec![BabyBear::ZERO; basis.len() + 1];
            for k in 0..basis.len() {
                new_basis[k + 1] = new_basis[k + 1] + basis[k];
                new_basis[k] = new_basis[k] - basis[k] * xs[j];
            }
            basis = new_basis;
            denom = denom * (xs[i] - xs[j]);
        }
        let scale = ys[i] * denom.inverse().unwrap();
        for k in 0..basis.len() {
            if k < result.len() {
                result[k] = result[k] + basis[k] * scale;
            }
        }
    }
    result
}

// ============================================================================
// Merkle tree (BLAKE3-based)
// ============================================================================

/// Domain separator for leaf hashing.
const STARK_LEAF_DOMAIN: &[u8] = b"stark-leaf:";
/// Domain separator for node hashing.
const STARK_NODE_DOMAIN: &[u8] = b"stark-node:";

fn hash_leaf(value: BabyBear) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    hasher.update(&value.0.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn hash_leaf_multi(values: &[BabyBear]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_LEAF_DOMAIN);
    for v in values {
        hasher.update(&v.0.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STARK_NODE_DOMAIN);
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

#[derive(Clone, Debug)]
struct MerkleTree {
    nodes: Vec<[u8; 32]>,
    num_leaves: usize,
}

impl MerkleTree {
    fn new(leaf_hashes: Vec<[u8; 32]>) -> Self {
        let n = leaf_hashes.len();
        assert!(n.is_power_of_two() && n >= 2);
        let mut nodes = Vec::with_capacity(2 * n);
        nodes.extend_from_slice(&leaf_hashes);
        let mut level_start = 0;
        let mut level_size = n;
        while level_size > 1 {
            for i in (0..level_size).step_by(2) {
                let left = &nodes[level_start + i];
                let right = &nodes[level_start + i + 1];
                nodes.push(hash_node(left, right));
            }
            level_start += level_size;
            level_size /= 2;
        }
        Self {
            nodes,
            num_leaves: n,
        }
    }

    fn root(&self) -> [u8; 32] {
        *self.nodes.last().unwrap()
    }

    fn prove(&self, index: usize) -> Vec<[u8; 32]> {
        assert!(index < self.num_leaves);
        let mut path = Vec::new();
        let mut idx = index;
        let mut level_start = 0;
        let mut level_size = self.num_leaves;
        while level_size > 1 {
            path.push(self.nodes[level_start + (idx ^ 1)]);
            idx /= 2;
            level_start += level_size;
            level_size /= 2;
        }
        path
    }

    fn verify_proof(
        root: &[u8; 32],
        leaf_hash: &[u8; 32],
        index: usize,
        path: &[[u8; 32]],
    ) -> bool {
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
}

// ============================================================================
// Fiat-Shamir transcript
// ============================================================================

#[derive(Clone)]
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
    fn absorb_bytes(&mut self, data: &[u8]) {
        self.hasher.update(data);
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
        let result = BabyBear::new(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
        self.hasher.update(bytes);
        result
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
        self.hasher.update(bytes);
        (val as usize) % bound
    }
}

// ============================================================================
// STARK Proof structure
// ============================================================================

/// FRI security: NUM_QUERIES * log2(BLOWUP) = 80 * 2 = 160 bits
const NUM_QUERIES: usize = 80;
const BLOWUP: usize = 4;

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
    air_name: String,
    nonce: Option<[u8; 32]>,
    #[serde(default)]
    boundary_commitment: Option<[u8; 32]>,
    #[serde(default)]
    boundary_query_values: Vec<Vec<u32>>,
    #[serde(default)]
    boundary_query_paths: Vec<Vec<[u8; 32]>>,
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
// AIR trait
// ============================================================================

trait StarkAir {
    fn width(&self) -> usize;
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear;
    fn constraint_degree(&self) -> usize;
    fn has_chain_continuity(&self) -> bool {
        true
    }
    fn air_name(&self) -> &'static str;
    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        vec![]
    }
}

#[derive(Clone, Debug)]
struct BoundaryConstraint {
    row: usize,
    col: usize,
    value: BabyBear,
}

struct MerkleStarkAir;

impl StarkAir for MerkleStarkAir {
    fn width(&self) -> usize {
        6
    }
    fn constraint_degree(&self) -> usize {
        4
    }
    fn air_name(&self) -> &'static str {
        "pyana-merkle-v1"
    }
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let (current, sib0, sib1, sib2, position, parent) =
            (local[0], local[1], local[2], local[3], local[4], local[5]);
        let c1 = parent - (current + sib0 + sib1 + sib2 + position);
        let c2 = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));
        let c3 = next[0] - parent;
        c1 + alpha * c2 + alpha * alpha * c3
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 3 {
            constraints.push(BoundaryConstraint {
                row: 0,
                col: 0,
                value: public_inputs[0],
            });
            let depth = public_inputs[2].0 as usize;
            constraints.push(BoundaryConstraint {
                row: depth - 1,
                col: 5,
                value: public_inputs[1],
            });
        }
        constraints
    }
}

// ============================================================================
// STARK Prover
// ============================================================================

fn prove(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> StarkProof {
    let num_rows = trace.len();
    let num_cols = air.width();
    assert!(num_rows >= 2 && num_rows.is_power_of_two());
    let domain_size = num_rows * BLOWUP;
    let trace_points: Vec<BabyBear> = build_evaluation_domain(num_rows);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    let mut trace_polys = Vec::with_capacity(num_cols);
    for col in 0..num_cols {
        let col_values: Vec<BabyBear> = trace.iter().map(|row| row[col]).collect();
        trace_polys.push(interpolate(&trace_points, &col_values));
    }

    let mut trace_evals = Vec::with_capacity(num_cols);
    for poly in &trace_polys {
        trace_evals.push(
            eval_points
                .iter()
                .map(|&x| poly_eval(poly, x))
                .collect::<Vec<_>>(),
        );
    }

    let trace_leaves: Vec<[u8; 32]> = (0..domain_size)
        .map(|i| hash_leaf_multi(&trace_evals.iter().map(|col| col[i]).collect::<Vec<_>>()))
        .collect();
    let trace_tree = MerkleTree::new(trace_leaves);

    let mut transcript = Transcript::new(b"merkle-stark");
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(num_rows as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(BLOWUP as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    transcript.absorb_hash(&trace_tree.root());
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    let alpha = transcript.squeeze_field();

    let boundary_cs = air.boundary_constraints(public_inputs, num_rows);

    let mut constraint_evals = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let local: Vec<BabyBear> = trace_evals.iter().map(|col| col[i]).collect();
        let next_idx = (i + BLOWUP) % domain_size;
        let next: Vec<BabyBear> = trace_evals.iter().map(|col| col[next_idx]).collect();
        constraint_evals.push(air.eval_constraints(&local, &next, public_inputs, alpha));
    }

    let mut quotient_evals = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let x = eval_points[i];
        let mut z = BabyBear::ONE;
        for &tp in &trace_points {
            z = z * (x - tp);
        }
        quotient_evals.push(if z == BabyBear::ZERO {
            BabyBear::ZERO
        } else {
            constraint_evals[i] * z.inverse().unwrap()
        });
    }

    let constraint_leaves: Vec<[u8; 32]> = quotient_evals.iter().map(|&v| hash_leaf(v)).collect();
    let constraint_tree = MerkleTree::new(constraint_leaves);
    transcript.absorb_hash(&constraint_tree.root());

    let (fri_commitments, fri_trees, fri_layer_evals, fri_final_poly) =
        fri_commit(&quotient_evals, &eval_points, &mut transcript);

    let mut query_proofs = Vec::with_capacity(NUM_QUERIES);
    for _ in 0..NUM_QUERIES {
        let idx = transcript.squeeze_index(domain_size);
        let trace_values: Vec<u32> = trace_evals.iter().map(|col| col[idx].0).collect();
        let trace_path = trace_tree.prove(idx);
        let next_idx = (idx + BLOWUP) % domain_size;
        let next_trace_values: Vec<u32> = trace_evals.iter().map(|col| col[next_idx].0).collect();
        let next_trace_path = trace_tree.prove(next_idx);
        let constraint_value = quotient_evals[idx].0;
        let constraint_path = constraint_tree.prove(idx);

        let first_half = domain_size / 2;
        let constraint_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        let constraint_sibling_value = quotient_evals[constraint_sibling_pos].0;
        let constraint_sibling_path = constraint_tree.prove(constraint_sibling_pos);

        let mut fri_layers = Vec::new();
        let mut qpos_in_layer = idx % first_half;
        for (li, tree) in fri_trees.iter().enumerate() {
            let half = tree.num_leaves / 2;
            let qpos = qpos_in_layer % tree.num_leaves;
            let spos = if qpos < half {
                qpos + half
            } else {
                qpos - half
            };
            fri_layers.push(FriLayerQuery {
                query_pos: qpos,
                query_value: fri_layer_evals[li][qpos].0,
                query_path: tree.prove(qpos),
                sibling_pos: spos,
                sibling_value: fri_layer_evals[li][spos].0,
                sibling_path: tree.prove(spos),
            });
            qpos_in_layer = qpos.min(spos);
        }

        query_proofs.push(QueryProof {
            index: idx,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }

    // Boundary constraint direct proofs
    let mut boundary_query_values = Vec::new();
    let mut boundary_query_paths = Vec::new();
    for bc in &boundary_cs {
        let eval_idx = bc.row * BLOWUP;
        let values: Vec<u32> = trace_evals.iter().map(|col| col[eval_idx].0).collect();
        let path = trace_tree.prove(eval_idx);
        boundary_query_values.push(values);
        boundary_query_paths.push(path);
    }

    StarkProof {
        trace_commitment: trace_tree.root(),
        constraint_commitment: constraint_tree.root(),
        fri_commitments,
        fri_final_poly: fri_final_poly.iter().map(|v| v.0).collect(),
        query_proofs,
        public_inputs: public_inputs.iter().map(|v| v.0).collect(),
        trace_len: num_rows,
        num_cols,
        air_name: air.air_name().to_string(),
        nonce: None,
        boundary_commitment: None,
        boundary_query_values,
        boundary_query_paths,
    }
}

fn fri_commit(
    evals: &[BabyBear],
    points: &[BabyBear],
    transcript: &mut Transcript,
) -> (
    Vec<[u8; 32]>,
    Vec<MerkleTree>,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    let mut current_evals = evals.to_vec();
    let mut current_points = points.to_vec();
    let mut commitments = Vec::new();
    let mut trees = Vec::new();
    let mut layer_evals = Vec::new();
    let two_inv = BabyBear::new(2).inverse().unwrap();
    while current_evals.len() > 4 {
        let beta = transcript.squeeze_field();
        let half = current_evals.len() / 2;
        let mut folded = Vec::with_capacity(half);
        for i in 0..half {
            let f_x = current_evals[i];
            let f_neg_x = current_evals[i + half];
            let x = current_points[i];
            let f_even = (f_x + f_neg_x) * two_inv;
            let f_odd = (f_x - f_neg_x) * two_inv * x.inverse().unwrap();
            folded.push(f_even + beta * f_odd);
        }
        let mut next_points = Vec::with_capacity(half);
        for i in 0..half {
            next_points.push(current_points[i] * current_points[i]);
        }
        while !folded.len().is_power_of_two() || folded.len() < 2 {
            folded.push(BabyBear::ZERO);
            next_points.push(BabyBear::ONE);
        }
        let leaves: Vec<[u8; 32]> = folded.iter().map(|&v| hash_leaf(v)).collect();
        let tree = MerkleTree::new(leaves);
        transcript.absorb_hash(&tree.root());
        commitments.push(tree.root());
        trees.push(tree);
        layer_evals.push(folded.clone());
        current_evals = folded;
        current_points = next_points;
    }
    (commitments, trees, layer_evals, current_evals)
}

// ============================================================================
// STARK Verifier
// ============================================================================

fn verify(
    air: &dyn StarkAir,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    if proof.air_name != air.air_name() {
        return Err(format!(
            "AIR identity mismatch: proof was generated for '{}', but verifying with '{}'",
            proof.air_name,
            air.air_name()
        ));
    }

    let num_cols = proof.num_cols;
    if num_cols != air.width() {
        return Err(format!(
            "Proof num_cols ({}) does not match AIR width ({})",
            num_cols,
            air.width()
        ));
    }
    let trace_len = proof.trace_len;
    if trace_len < 2 || !trace_len.is_power_of_two() {
        return Err(format!(
            "Invalid trace_len: {} (must be power of two >= 2)",
            trace_len
        ));
    }
    let domain_size = trace_len * BLOWUP;

    let proof_pis: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    if proof_pis != public_inputs {
        return Err("Public inputs mismatch".to_string());
    }

    let mut transcript = Transcript::new(b"merkle-stark");
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_bytes(&(trace_len as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.width() as u32).to_le_bytes());
    transcript.absorb_bytes(&(air.constraint_degree() as u32).to_le_bytes());
    transcript.absorb_bytes(&(BLOWUP as u32).to_le_bytes());
    transcript.absorb_bytes(&(NUM_QUERIES as u32).to_le_bytes());

    transcript.absorb_hash(&proof.trace_commitment);
    for pi in public_inputs {
        transcript.absorb_field(*pi);
    }
    let alpha = transcript.squeeze_field();

    let boundary_cs = air.boundary_constraints(public_inputs, trace_len);

    transcript.absorb_hash(&proof.constraint_commitment);

    let mut fri_betas = Vec::new();
    for commitment in &proof.fri_commitments {
        fri_betas.push(transcript.squeeze_field());
        transcript.absorb_hash(commitment);
    }

    // Boundary constraint verification
    if !boundary_cs.is_empty() {
        if proof.boundary_query_values.len() != boundary_cs.len() {
            return Err(format!(
                "Boundary proof data missing: expected {} openings, got {}",
                boundary_cs.len(),
                proof.boundary_query_values.len()
            ));
        }
        if proof.boundary_query_paths.len() != boundary_cs.len() {
            return Err("Boundary proof paths missing".to_string());
        }

        for (i, bc) in boundary_cs.iter().enumerate() {
            let eval_idx = bc.row * BLOWUP;
            let boundary_vals: Vec<BabyBear> = proof.boundary_query_values[i]
                .iter()
                .map(|&v| BabyBear::new_canonical(v))
                .collect();

            if boundary_vals.len() != num_cols {
                return Err(format!(
                    "Boundary opening {i} has wrong width: expected {num_cols}, got {}",
                    boundary_vals.len()
                ));
            }

            if !MerkleTree::verify_proof(
                &proof.trace_commitment,
                &hash_leaf_multi(&boundary_vals),
                eval_idx,
                &proof.boundary_query_paths[i],
            ) {
                return Err(format!(
                    "Boundary constraint {i}: Merkle proof failed at eval index {eval_idx}"
                ));
            }

            if bc.col >= boundary_vals.len() {
                return Err(format!(
                    "Boundary constraint {i}: column {} out of range",
                    bc.col
                ));
            }
            if boundary_vals[bc.col] != bc.value {
                return Err(format!(
                    "Boundary constraint {i} violated: trace[{}][{}] = {}, expected {}",
                    bc.row, bc.col, boundary_vals[bc.col].0, bc.value.0
                ));
            }
        }
    }

    let trace_points: Vec<BabyBear> = build_evaluation_domain(trace_len);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    for query in &proof.query_proofs {
        let idx = transcript.squeeze_index(domain_size);
        if query.index != idx {
            return Err(format!(
                "Query index mismatch: expected {idx}, got {}",
                query.index
            ));
        }

        let trace_vals: Vec<BabyBear> = query
            .trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if trace_vals.len() != num_cols {
            return Err("Wrong number of trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&trace_vals),
            idx,
            &query.trace_path,
        ) {
            return Err(format!("Trace Merkle proof failed at index {idx}"));
        }

        let constraint_val = BabyBear::new_canonical(query.constraint_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_val),
            idx,
            &query.constraint_path,
        ) {
            return Err(format!("Constraint Merkle proof failed at index {idx}"));
        }

        let next_idx = (idx + BLOWUP) % domain_size;
        let next_trace_vals: Vec<BabyBear> = query
            .next_trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if next_trace_vals.len() != num_cols {
            return Err("Wrong number of next trace values".to_string());
        }
        if !MerkleTree::verify_proof(
            &proof.trace_commitment,
            &hash_leaf_multi(&next_trace_vals),
            next_idx,
            &query.next_trace_path,
        ) {
            return Err(format!(
                "Next trace Merkle proof failed at index {next_idx}"
            ));
        }

        let x = eval_points[idx];
        let mut z = BabyBear::ONE;
        for &tp in &trace_points {
            z = z * (x - tp);
        }
        let constraint_at_x =
            air.eval_constraints(&trace_vals, &next_trace_vals, public_inputs, alpha);
        if constraint_val * z != constraint_at_x {
            return Err(format!(
                "Constraint consistency check failed at query index {idx}"
            ));
        }

        // FRI verification (simplified for the example -- checks first fold only)
        let first_half = domain_size / 2;
        let constraint_sib_val = BabyBear::new_canonical(query.constraint_sibling_value);
        if !MerkleTree::verify_proof(
            &proof.constraint_commitment,
            &hash_leaf(constraint_sib_val),
            query.constraint_sibling_pos,
            &query.constraint_sibling_path,
        ) {
            return Err(format!(
                "FRI: constraint sibling Merkle proof failed at pos {}",
                query.constraint_sibling_pos
            ));
        }

        let two_inv = BabyBear::new(2).inverse().unwrap();

        let (f_x_val, f_neg_x_val, even_pos) = if idx < first_half {
            (constraint_val, constraint_sib_val, idx)
        } else {
            (constraint_sib_val, constraint_val, idx - first_half)
        };

        let x_point = eval_points[even_pos];

        if !fri_betas.is_empty() {
            let f_even = (f_x_val + f_neg_x_val) * two_inv;
            let f_odd = (f_x_val - f_neg_x_val) * two_inv * x_point.inverse().unwrap();
            let expected_folded = f_even + fri_betas[0] * f_odd;
            if !proof.fri_commitments.is_empty() {
                if query.fri_layers.is_empty() {
                    return Err("FRI: missing layer 0 opening".to_string());
                }
                let layer0 = &query.fri_layers[0];
                if BabyBear::new_canonical(layer0.query_value) != expected_folded {
                    return Err(format!("FRI folding check failed at layer 0"));
                }
                if !MerkleTree::verify_proof(
                    &proof.fri_commitments[0],
                    &hash_leaf(BabyBear::new_canonical(layer0.query_value)),
                    layer0.query_pos,
                    &layer0.query_path,
                ) {
                    return Err(format!("FRI layer 0: Merkle proof failed"));
                }
            }
        }
    }

    if proof.fri_final_poly.len() > 4 {
        return Err("FRI final polynomial too large".to_string());
    }

    Ok(())
}

// ============================================================================
// Trace generation
// ============================================================================

fn generate_merkle_trace(
    leaf_hash: u32,
    siblings: &[[u32; 3]],
    positions: &[u32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2);
    let min_padded = if depth.is_power_of_two() {
        depth * 2
    } else {
        depth.next_power_of_two()
    };
    let padded = min_padded;
    let mut trace = Vec::with_capacity(padded);
    let mut current = BabyBear::new(leaf_hash);
    let leaf_elem = current;
    for i in 0..depth {
        let (sib0, sib1, sib2) = (
            BabyBear::new(siblings[i][0]),
            BabyBear::new(siblings[i][1]),
            BabyBear::new(siblings[i][2]),
        );
        let pos = BabyBear::new(positions[i]);
        let parent = current + sib0 + sib1 + sib2 + pos;
        trace.push(vec![current, sib0, sib1, sib2, pos, parent]);
        current = parent;
    }
    let root = current;
    let num_padding = padded - depth;
    for p in 0..num_padding {
        if p == num_padding - 1 {
            let wrap_sib0 = leaf_elem - root;
            trace.push(vec![
                root,
                wrap_sib0,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                leaf_elem,
            ]);
        } else {
            trace.push(vec![
                root,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                root,
            ]);
        }
    }
    (trace, vec![leaf_elem, root, BabyBear::new(depth as u32)])
}

// ============================================================================
// Main: demonstrates basic usage
// ============================================================================

fn main() {
    println!("=== FRI From Scratch: Pedagogical STARK Implementation ===");
    println!();

    // Generate a Merkle membership trace for a 4-level tree
    let leaf_hash = 12345u32;
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];

    println!("Generating Merkle membership trace...");
    println!("  Leaf hash: {leaf_hash}");
    println!("  Tree depth: {}", siblings.len());

    let (trace, public_inputs) = generate_merkle_trace(leaf_hash, &siblings, &positions);
    println!("  Trace rows: {} (padded to power of 2)", trace.len());
    println!("  Root (computed): {}", public_inputs[1].0);
    println!();

    // Prove
    println!("Generating STARK proof (FRI-based, 80 queries, 4x blowup)...");
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);
    println!("  Proof generated successfully!");
    println!("  FRI layers: {}", proof.fri_commitments.len());
    println!("  Query proofs: {}", proof.query_proofs.len());
    println!();

    // Verify
    println!("Verifying proof...");
    match verify(&air, &proof, &public_inputs) {
        Ok(()) => println!("  VERIFICATION PASSED"),
        Err(e) => println!("  VERIFICATION FAILED: {e}"),
    }
    println!();

    // Demonstrate that tampering is detected
    println!("Tampering with proof (flipping trace commitment bit)...");
    let mut tampered = proof.clone();
    tampered.trace_commitment[0] ^= 0xFF;
    match verify(&air, &tampered, &public_inputs) {
        Ok(()) => println!("  ERROR: tampered proof passed (should not happen!)"),
        Err(e) => println!("  Tampered proof correctly rejected: {e}"),
    }
    println!();

    // Demonstrate wrong public inputs
    println!("Verifying with wrong public inputs (different leaf)...");
    let wrong_pi = vec![BabyBear::new(99999), public_inputs[1], public_inputs[2]];
    match verify(&air, &proof, &wrong_pi) {
        Ok(()) => println!("  ERROR: wrong inputs passed (should not happen!)"),
        Err(e) => println!("  Wrong inputs correctly rejected: {e}"),
    }

    println!();
    println!("=== Done. This implementation is for educational purposes. ===");
    println!("=== Production pyana uses Plonky3 for real STARK proofs.   ===");
}
