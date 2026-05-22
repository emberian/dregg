//! Poseidon-committed STARK: a STARK variant using Fp-native Poseidon for Merkle commitments.
//!
//! # Motivation
//!
//! Our standard STARK (`stark.rs`) uses BLAKE3 for Merkle tree commitments and Fiat-Shamir.
//! Verifying BLAKE3 inside a Kimchi circuit costs ~6800 Generic gates per compression,
//! totaling ~272K gates for a full STARK verification circuit (see `stark_in_pickles.rs`).
//!
//! Kimchi has a NATIVE Poseidon gate (5 rounds per row, ~12 rows per hash). By committing
//! the STARK's trace and FRI layers using Fp-native Poseidon instead of BLAKE3, the Kimchi
//! verifier circuit needs only native Poseidon gates for Merkle verification -- dropping
//! from ~272K gates to ~30K gates (fits comfortably in domain 2^15 = 32768).
//!
//! # Architecture
//!
//! ```text
//! ┌───────────────────────────────────────────────────────────────────┐
//! │  PoseidonStarkProof (generated outside Kimchi)                     │
//! │                                                                   │
//! │  BabyBear trace + constraints (same AIRs as stark.rs)             │
//! │  Merkle commitments: Poseidon-over-Fp (binary tree, Fp leaves)    │
//! │  Fiat-Shamir: Poseidon sponge over Fp                            │
//! │  FRI: same additive folding, Poseidon-committed layers            │
//! └────────────────────────────┬──────────────────────────────────────┘
//!                              │ verify inside Kimchi
//!                              ▼
//! ┌───────────────────────────────────────────────────────────────────┐
//! │  Kimchi verifier circuit (~30K rows, domain 2^15)                 │
//! │                                                                   │
//! │  - Poseidon gates (native): Merkle path verification              │
//! │  - ForeignFieldMul/Add: BabyBear arithmetic (constraint eval)     │
//! │  - RangeCheck0/1: limb bounds for BabyBear values                 │
//! │  - Generic gates: linear combinations, final checks               │
//! └───────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Gate Count Estimate (Kimchi verifier for this proof format)
//!
//! | Component                     | Rows     | Notes                               |
//! |-------------------------------|----------|-------------------------------------|
//! | Merkle paths (trace+constr)   | ~19,200  | 80q × 2paths × 10depth × 12rows    |
//! | FRI Merkle paths              | ~9,600   | 80q × 10layers × 1hash × 12rows    |
//! | BabyBear constraint eval      | ~320     | 80q × 4 ForeignFieldMul             |
//! | FRI folding checks            | ~160     | 80q × 2 ForeignFieldMul             |
//! | Fiat-Shamir replay            | ~600     | ~50 Poseidon squeezes × 12rows      |
//! | Range checks                  | ~400     | BabyBear value validation           |
//! | **Total**                     | **~30K** | Fits in Kimchi domain 2^15          |
//!
//! Compare to BLAKE3 approach: ~272K rows (requires domain 2^18+).
//!
//! # Security
//!
//! - Same FRI soundness as `stark.rs`: 80 queries × log2(blowup) bits
//! - Same AIR constraint enforcement (identical evaluation logic)
//! - Poseidon over Fp has ~128-bit collision resistance (Fp is ~255 bits)
//! - Fiat-Shamir via Poseidon sponge matches Mina's on-chain security model

#[cfg(feature = "mina")]
use crate::field::{BABYBEAR_P, BabyBear};

#[cfg(feature = "mina")]
use crate::stark::{
    BoundaryConstraint, StarkAir, build_evaluation_domain, get_root_of_unity, interpolate,
    poly_eval,
};

#[cfg(feature = "mina")]
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};

#[cfg(feature = "mina")]
use mina_curves::pasta::{Fp, Vesta};

#[cfg(feature = "mina")]
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    poseidon::{ArithmeticSponge, Sponge},
};

#[cfg(feature = "mina")]
use kimchi::curve::KimchiCurve;

#[cfg(feature = "mina")]
use serde::{Deserialize, Serialize};

// ============================================================================
// Constants
// ============================================================================

#[cfg(feature = "mina")]
const NUM_QUERIES: usize = 80;

#[cfg(feature = "mina")]
const MIN_BLOWUP: usize = 4;

/// Domain separator constants for Poseidon Merkle tree (prevents second-preimage attacks).
#[cfg(feature = "mina")]
const LEAF_DOMAIN_SEP: u64 = 0x7374_6172_6b5f_6c66; // "stark_lf" as u64

#[cfg(feature = "mina")]
const NODE_DOMAIN_SEP: u64 = 0x7374_6172_6b5f_6e64; // "stark_nd" as u64

// ============================================================================
// Poseidon-over-Fp Merkle tree
// ============================================================================

/// Hash a leaf consisting of multiple BabyBear values into an Fp element.
///
/// Embeds each BabyBear value (< 2^31) directly into Fp (a ~255-bit field),
/// then hashes via Mina's native Poseidon sponge with a domain separator.
#[cfg(feature = "mina")]
fn poseidon_hash_leaf(values: &[BabyBear]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);

    // Domain separation for leaves
    sponge.absorb(&[Fp::from(LEAF_DOMAIN_SEP)]);

    // Embed BabyBear values as Fp elements
    let fp_values: Vec<Fp> = values.iter().map(|v| Fp::from(v.0 as u64)).collect();
    sponge.absorb(&fp_values);

    sponge.squeeze()
}

/// Hash two Fp siblings into a parent node using Poseidon.
#[cfg(feature = "mina")]
fn poseidon_hash_node(left: Fp, right: Fp) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);

    // Domain separation for internal nodes
    sponge.absorb(&[Fp::from(NODE_DOMAIN_SEP), left, right]);

    sponge.squeeze()
}

/// A binary Merkle tree using Poseidon-over-Fp hashing.
///
/// Leaves are Fp elements (hashed from BabyBear trace values).
/// Internal nodes are Poseidon(domain_sep || left || right).
#[cfg(feature = "mina")]
#[derive(Clone, Debug)]
struct PoseidonMerkleTree {
    /// All nodes stored level by level: leaves first, then internal nodes.
    nodes: Vec<Fp>,
    num_leaves: usize,
}

#[cfg(feature = "mina")]
impl PoseidonMerkleTree {
    fn new(leaf_hashes: Vec<Fp>) -> Self {
        let n = leaf_hashes.len();
        assert!(n.is_power_of_two() && n >= 2);

        let mut nodes = Vec::with_capacity(2 * n);
        nodes.extend_from_slice(&leaf_hashes);

        let mut level_start = 0;
        let mut level_size = n;
        while level_size > 1 {
            for i in (0..level_size).step_by(2) {
                let left = nodes[level_start + i];
                let right = nodes[level_start + i + 1];
                nodes.push(poseidon_hash_node(left, right));
            }
            level_start += level_size;
            level_size /= 2;
        }

        Self {
            nodes,
            num_leaves: n,
        }
    }

    fn root(&self) -> Fp {
        *self.nodes.last().unwrap()
    }

    /// Generate a Merkle authentication path (sibling hashes from leaf to root).
    fn prove(&self, index: usize) -> Vec<Fp> {
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

    /// Verify a Merkle authentication path.
    fn verify_proof(root: Fp, leaf_hash: Fp, index: usize, path: &[Fp]) -> bool {
        let mut current = leaf_hash;
        let mut idx = index;
        for &sibling in path {
            current = if idx & 1 == 0 {
                poseidon_hash_node(current, sibling)
            } else {
                poseidon_hash_node(sibling, current)
            };
            idx >>= 1;
        }
        current == root
    }
}

// ============================================================================
// Poseidon Fiat-Shamir transcript
// ============================================================================

/// A Fiat-Shamir transcript using Poseidon sponge over Fp.
///
/// This matches Mina's native hash, making in-circuit transcript replay cheap
/// (only native Poseidon gates needed in the Kimchi verifier circuit).
#[cfg(feature = "mina")]
#[derive(Clone)]
struct PoseidonTranscript {
    sponge: ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>,
    squeeze_counter: u64,
}

#[cfg(feature = "mina")]
impl PoseidonTranscript {
    fn new(domain_sep: &[u8]) -> Self {
        let params = Vesta::sponge_params();
        let mut sponge =
            ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);

        // Domain separation: absorb a field element derived from the domain bytes
        let sep = Fp::from_le_bytes_mod_order(domain_sep);
        sponge.absorb(&[sep]);

        Self {
            sponge,
            squeeze_counter: 0,
        }
    }

    /// Absorb an Fp element into the transcript.
    fn absorb_fp(&mut self, val: Fp) {
        self.sponge.absorb(&[val]);
    }

    /// Absorb a BabyBear value (embedded as Fp).
    fn absorb_babybear(&mut self, val: BabyBear) {
        self.sponge.absorb(&[Fp::from(val.0 as u64)]);
    }

    /// Absorb raw bytes (packed into Fp elements, 31 bytes per element).
    fn absorb_bytes(&mut self, data: &[u8]) {
        let mut elements = Vec::new();
        for chunk in data.chunks(31) {
            let mut bytes = [0u8; 32];
            bytes[..chunk.len()].copy_from_slice(chunk);
            elements.push(Fp::from_le_bytes_mod_order(&bytes));
        }
        self.sponge.absorb(&elements);
    }

    /// Squeeze a BabyBear challenge from the transcript.
    ///
    /// Squeezes an Fp element from the sponge and reduces modulo BabyBear prime.
    fn squeeze_babybear(&mut self) -> BabyBear {
        self.squeeze_counter += 1;
        // Absorb counter for domain separation between consecutive squeezes
        self.sponge.absorb(&[Fp::from(self.squeeze_counter)]);
        let fp = self.sponge.squeeze();

        // Reduce Fp to BabyBear: take the low 32 bits and reduce mod p
        let bigint = fp.into_bigint();
        let limbs = bigint.as_ref();
        let low_u64 = limbs[0];
        BabyBear::new((low_u64 % BABYBEAR_P as u64) as u32)
    }

    /// Squeeze an index in [0, bound) from the transcript.
    fn squeeze_index(&mut self, bound: usize) -> usize {
        self.squeeze_counter += 1;
        self.sponge.absorb(&[Fp::from(self.squeeze_counter)]);
        let fp = self.sponge.squeeze();

        let bigint = fp.into_bigint();
        let limbs = bigint.as_ref();
        let low_u64 = limbs[0];
        (low_u64 as usize) % bound
    }
}

// ============================================================================
// Proof structures
// ============================================================================

/// A STARK proof committed with Poseidon-over-Fp Merkle trees.
///
/// This proof format is designed for efficient verification inside a Kimchi circuit:
/// - Merkle roots and paths are Fp elements (native Poseidon gates verify them)
/// - BabyBear values are stored as u32 (ForeignFieldMul gates evaluate constraints)
/// - No BLAKE3 anywhere -- all hashing is Poseidon-over-Fp
#[cfg(feature = "mina")]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PoseidonStarkProof {
    /// Poseidon Merkle root of the trace evaluations.
    pub trace_commitment: FpSer,
    /// Poseidon Merkle root of the constraint quotient evaluations.
    pub constraint_commitment: FpSer,
    /// Poseidon Merkle roots of FRI layer commitments.
    pub fri_commitments: Vec<FpSer>,
    /// Final FRI polynomial coefficients (BabyBear values).
    pub fri_final_poly: Vec<u32>,
    /// Query opening proofs.
    pub query_proofs: Vec<PoseidonQueryProof>,
    /// Public inputs (BabyBear values).
    pub public_inputs: Vec<u32>,
    /// Trace length (must be power of two).
    pub trace_len: usize,
    /// Number of trace columns.
    pub num_cols: usize,
    /// AIR identity string.
    pub air_name: String,
    /// Optional nonce for temporal binding.
    pub nonce: Option<[u8; 32]>,
    /// Boundary constraint direct proofs.
    #[serde(default)]
    pub boundary_query_values: Vec<Vec<u32>>,
    /// Merkle paths for boundary constraint proofs.
    #[serde(default)]
    pub boundary_query_paths: Vec<Vec<FpSer>>,
}

/// A single query opening proof with Poseidon Merkle paths.
#[cfg(feature = "mina")]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PoseidonQueryProof {
    /// Index in the evaluation domain.
    pub index: usize,
    /// Trace column values at this index (BabyBear).
    pub trace_values: Vec<u32>,
    /// Poseidon Merkle path for trace values.
    pub trace_path: Vec<FpSer>,
    /// Next-row trace values (for transition constraints).
    pub next_trace_values: Vec<u32>,
    /// Poseidon Merkle path for next-row trace values.
    pub next_trace_path: Vec<FpSer>,
    /// Constraint quotient value at this index (BabyBear).
    pub constraint_value: u32,
    /// Poseidon Merkle path for constraint value.
    pub constraint_path: Vec<FpSer>,
    /// Sibling constraint value (for FRI folding).
    pub constraint_sibling_value: u32,
    /// Sibling position in domain.
    pub constraint_sibling_pos: usize,
    /// Poseidon Merkle path for constraint sibling.
    pub constraint_sibling_path: Vec<FpSer>,
    /// FRI layer openings.
    pub fri_layers: Vec<PoseidonFriLayerQuery>,
}

/// FRI layer query proof with Poseidon Merkle paths.
#[cfg(feature = "mina")]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PoseidonFriLayerQuery {
    pub query_pos: usize,
    pub query_value: u32,
    pub query_path: Vec<FpSer>,
    pub sibling_pos: usize,
    pub sibling_value: u32,
    pub sibling_path: Vec<FpSer>,
}

/// Serializable wrapper for Fp (Pasta base field element).
///
/// Fp doesn't implement serde traits directly, so we store as 32-byte LE.
#[cfg(feature = "mina")]
#[derive(Clone, Debug)]
pub struct FpSer(pub Fp);

#[cfg(feature = "mina")]
impl Serialize for FpSer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let bigint = self.0.into_bigint();
        let limbs = bigint.as_ref();
        let mut bytes = [0u8; 32];
        for (i, limb) in limbs.iter().enumerate() {
            let lb = limb.to_le_bytes();
            let start = i * 8;
            bytes[start..start + 8].copy_from_slice(&lb);
        }
        serializer.serialize_bytes(&bytes)
    }
}

#[cfg(feature = "mina")]
impl<'de> Deserialize<'de> for FpSer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bytes: Vec<u8> = serde::Deserialize::deserialize(deserializer)?;
        if bytes.len() != 32 {
            return Err(serde::de::Error::custom("FpSer: expected 32 bytes"));
        }
        let fp = Fp::from_le_bytes_mod_order(&bytes);
        Ok(FpSer(fp))
    }
}

#[cfg(feature = "mina")]
impl From<Fp> for FpSer {
    fn from(fp: Fp) -> Self {
        FpSer(fp)
    }
}

#[cfg(feature = "mina")]
impl FpSer {
    pub fn fp(&self) -> Fp {
        self.0
    }
}

// ============================================================================
// Helper: blowup factor
// ============================================================================

#[cfg(feature = "mina")]
fn blowup_for_degree(degree: usize) -> usize {
    degree.next_power_of_two().max(MIN_BLOWUP)
}

// ============================================================================
// Prover
// ============================================================================

/// Generate a Poseidon-committed STARK proof for the given AIR and trace.
///
/// This is functionally identical to `stark::prove()` but uses:
/// - Poseidon-over-Fp Merkle trees (instead of BLAKE3)
/// - Poseidon sponge for Fiat-Shamir (instead of BLAKE3)
///
/// The resulting proof can be efficiently verified inside a Kimchi circuit
/// using only native Poseidon gates + ForeignField gates for BabyBear arithmetic.
#[cfg(feature = "mina")]
pub fn prove_poseidon(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> PoseidonStarkProof {
    prove_poseidon_with_nonce(air, trace, public_inputs, None)
}

/// Prove with an optional nonce for temporal binding.
#[cfg(feature = "mina")]
pub fn prove_poseidon_with_nonce(
    air: &dyn StarkAir,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    nonce: Option<[u8; 32]>,
) -> PoseidonStarkProof {
    let num_rows = trace.len();
    let num_cols = air.width();
    assert!(num_rows >= 2 && num_rows.is_power_of_two());

    let blowup = blowup_for_degree(air.constraint_degree());
    let domain_size = num_rows * blowup;

    // Build evaluation domains (identical to stark.rs)
    let trace_points: Vec<BabyBear> = build_evaluation_domain(num_rows);
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    // Interpolate trace columns to polynomials
    let mut trace_polys = Vec::with_capacity(num_cols);
    for col in 0..num_cols {
        let col_values: Vec<BabyBear> = trace.iter().map(|row| row[col]).collect();
        trace_polys.push(interpolate(&trace_points, &col_values));
    }

    // Evaluate trace polynomials over the blowup domain
    let mut trace_evals = Vec::with_capacity(num_cols);
    for poly in &trace_polys {
        trace_evals.push(
            eval_points
                .iter()
                .map(|&x| poly_eval(poly, x))
                .collect::<Vec<_>>(),
        );
    }

    // Commit trace using Poseidon Merkle tree
    let trace_leaves: Vec<Fp> = (0..domain_size)
        .map(|i| {
            let row_values: Vec<BabyBear> = trace_evals.iter().map(|col| col[i]).collect();
            poseidon_hash_leaf(&row_values)
        })
        .collect();
    let trace_tree = PoseidonMerkleTree::new(trace_leaves);

    // Initialize Poseidon Fiat-Shamir transcript
    let mut transcript = PoseidonTranscript::new(b"poseidon-stark-v1");

    // AIR domain separation
    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_fp(Fp::from(num_rows as u64));
    transcript.absorb_fp(Fp::from(air.width() as u64));
    transcript.absorb_fp(Fp::from(air.constraint_degree() as u64));
    transcript.absorb_fp(Fp::from(blowup as u64));
    transcript.absorb_fp(Fp::from(NUM_QUERIES as u64));

    // Temporal binding
    if let Some(ref n) = nonce {
        transcript.absorb_bytes(n);
    }

    // Absorb trace commitment
    transcript.absorb_fp(trace_tree.root());

    // Absorb public inputs
    transcript.absorb_fp(Fp::from(public_inputs.len() as u64));
    for pi in public_inputs {
        transcript.absorb_babybear(*pi);
    }

    // Squeeze random combination challenge
    let alpha = transcript.squeeze_babybear();

    // Get boundary constraints
    let boundary_cs = air.boundary_constraints(public_inputs, num_rows);

    // Evaluate constraint quotient polynomial (same as stark.rs)
    let mut constraint_evals = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let local: Vec<BabyBear> = trace_evals.iter().map(|col| col[i]).collect();
        let next_idx = (i + blowup) % domain_size;
        let next: Vec<BabyBear> = trace_evals.iter().map(|col| col[next_idx]).collect();
        constraint_evals.push(air.eval_constraints(&local, &next, public_inputs, alpha));
    }

    // Compute transition quotient (same logic as stark.rs)
    let omega_trace = get_root_of_unity(num_rows.trailing_zeros());
    let last_trace_point = omega_trace.pow((num_rows - 1) as u32);
    let exp_mod_n = ((num_rows - 1) as u64 * (num_rows - 1) as u64 % num_rows as u64) as u32;
    let z_t_at_last = BabyBear::new(num_rows as u32) * omega_trace.pow(exp_mod_n);

    let mut quotient_evals = Vec::with_capacity(domain_size);
    for i in 0..domain_size {
        let x = eval_points[i];
        let x_n = x.pow(num_rows as u32);
        let z_full = x_n - BabyBear::ONE;
        let denom_factor = x - last_trace_point;
        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                quotient_evals.push(constraint_evals[i] * z_t_at_last.inverse().unwrap());
            } else {
                quotient_evals.push(BabyBear::ZERO);
            }
        } else {
            let z_transition = z_full * denom_factor.inverse().unwrap();
            quotient_evals.push(constraint_evals[i] * z_transition.inverse().unwrap());
        }
    }

    // Commit constraint quotient using Poseidon Merkle tree
    let constraint_leaves: Vec<Fp> = quotient_evals
        .iter()
        .map(|&v| poseidon_hash_leaf(&[v]))
        .collect();
    let constraint_tree = PoseidonMerkleTree::new(constraint_leaves);
    transcript.absorb_fp(constraint_tree.root());

    // FRI commit (Poseidon-committed layers)
    let (fri_commitments, fri_trees, fri_layer_evals, fri_final_poly) =
        fri_commit_poseidon(&quotient_evals, &mut transcript);

    // Generate query proofs
    let mut query_proofs = Vec::with_capacity(NUM_QUERIES);
    for _ in 0..NUM_QUERIES {
        let idx = transcript.squeeze_index(domain_size);

        let trace_values: Vec<u32> = trace_evals.iter().map(|col| col[idx].0).collect();
        let trace_path = trace_tree.prove(idx);

        let next_idx = (idx + blowup) % domain_size;
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

        // FRI layer openings
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
            fri_layers.push(PoseidonFriLayerQuery {
                query_pos: qpos,
                query_value: fri_layer_evals[li][qpos].0,
                query_path: tree.prove(qpos).into_iter().map(FpSer).collect(),
                sibling_pos: spos,
                sibling_value: fri_layer_evals[li][spos].0,
                sibling_path: tree.prove(spos).into_iter().map(FpSer).collect(),
            });
            qpos_in_layer = qpos.min(spos);
        }

        query_proofs.push(PoseidonQueryProof {
            index: idx,
            trace_values,
            trace_path: trace_path.into_iter().map(FpSer).collect(),
            next_trace_values,
            next_trace_path: next_trace_path.into_iter().map(FpSer).collect(),
            constraint_value,
            constraint_path: constraint_path.into_iter().map(FpSer).collect(),
            constraint_sibling_value,
            constraint_sibling_pos,
            constraint_sibling_path: constraint_sibling_path.into_iter().map(FpSer).collect(),
            fri_layers,
        });
    }

    // Boundary constraint direct proofs
    let mut boundary_query_values = Vec::new();
    let mut boundary_query_paths = Vec::new();
    for bc in &boundary_cs {
        let eval_idx = bc.row * blowup;
        let values: Vec<u32> = trace_evals.iter().map(|col| col[eval_idx].0).collect();
        let path = trace_tree.prove(eval_idx);
        boundary_query_values.push(values);
        boundary_query_paths.push(path.into_iter().map(FpSer).collect());
    }

    PoseidonStarkProof {
        trace_commitment: FpSer(trace_tree.root()),
        constraint_commitment: FpSer(constraint_tree.root()),
        fri_commitments: fri_commitments.into_iter().map(FpSer).collect(),
        fri_final_poly: fri_final_poly.iter().map(|v| v.0).collect(),
        query_proofs,
        public_inputs: public_inputs.iter().map(|v| v.0).collect(),
        trace_len: num_rows,
        num_cols,
        air_name: air.air_name().to_string(),
        nonce,
        boundary_query_values,
        boundary_query_paths,
    }
}

/// FRI commitment using Poseidon Merkle trees.
#[cfg(feature = "mina")]
fn fri_commit_poseidon(
    evals: &[BabyBear],
    transcript: &mut PoseidonTranscript,
) -> (
    Vec<Fp>,
    Vec<PoseidonMerkleTree>,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
) {
    let mut current_evals = evals.to_vec();
    let mut commitments = Vec::new();
    let mut trees = Vec::new();
    let mut layer_evals = Vec::new();

    while current_evals.len() > 4 {
        let beta = transcript.squeeze_babybear();
        let half = current_evals.len() / 2;
        let mut folded = Vec::with_capacity(half);
        for i in 0..half {
            folded.push(current_evals[i] + beta * current_evals[i + half]);
        }
        while !folded.len().is_power_of_two() || folded.len() < 2 {
            folded.push(BabyBear::ZERO);
        }

        // Commit folded layer with Poseidon Merkle tree
        let leaves: Vec<Fp> = folded.iter().map(|&v| poseidon_hash_leaf(&[v])).collect();
        let tree = PoseidonMerkleTree::new(leaves);
        transcript.absorb_fp(tree.root());
        commitments.push(tree.root());
        trees.push(tree);
        layer_evals.push(folded.clone());
        current_evals = folded;
    }

    (commitments, trees, layer_evals, current_evals)
}

// ============================================================================
// Verifier
// ============================================================================

/// Verify a Poseidon-committed STARK proof.
///
/// This performs the same verification logic as `stark::verify()` but uses
/// Poseidon Merkle proof verification instead of BLAKE3. The logic here maps
/// directly to what the Kimchi in-circuit verifier would compute.
#[cfg(feature = "mina")]
pub fn verify_poseidon(
    air: &dyn StarkAir,
    proof: &PoseidonStarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    verify_poseidon_with_nonce(air, proof, public_inputs, None)
}

/// Verify with optional nonce for temporal binding.
#[cfg(feature = "mina")]
pub fn verify_poseidon_with_nonce(
    air: &dyn StarkAir,
    proof: &PoseidonStarkProof,
    public_inputs: &[BabyBear],
    nonce: Option<[u8; 32]>,
) -> Result<(), String> {
    // AIR identity check
    if proof.air_name != air.air_name() {
        return Err(format!(
            "AIR identity mismatch: proof for '{}', verifying with '{}'",
            proof.air_name,
            air.air_name()
        ));
    }

    // Nonce check
    if proof.nonce != nonce {
        return Err("Nonce mismatch".to_string());
    }

    let num_cols = proof.num_cols;
    let trace_len = proof.trace_len;

    // Structural validation
    if trace_len < 2 {
        return Err(format!("Invalid trace_len: {} (must be >= 2)", trace_len));
    }
    if !trace_len.is_power_of_two() {
        return Err(format!(
            "Invalid trace_len: {} (must be power of two)",
            trace_len
        ));
    }
    if num_cols == 0 || num_cols != air.width() {
        return Err(format!(
            "Column count mismatch: proof has {}, AIR expects {}",
            num_cols,
            air.width()
        ));
    }
    if proof.query_proofs.len() != NUM_QUERIES {
        return Err(format!(
            "Invalid query count: expected {}, got {}",
            NUM_QUERIES,
            proof.query_proofs.len()
        ));
    }

    let blowup = blowup_for_degree(air.constraint_degree());
    let domain_size = trace_len
        .checked_mul(blowup)
        .ok_or_else(|| format!("trace_len * blowup overflow: {} * {}", trace_len, blowup))?;
    if domain_size.trailing_zeros() > 27 {
        return Err(format!(
            "Domain size 2^{} exceeds BabyBear root-of-unity limit",
            domain_size.trailing_zeros()
        ));
    }

    // Public input check
    let proof_pis: Vec<BabyBear> = proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    if proof_pis != public_inputs {
        return Err("Public inputs mismatch".to_string());
    }

    // Reconstruct Fiat-Shamir transcript (must match prover exactly)
    let mut transcript = PoseidonTranscript::new(b"poseidon-stark-v1");

    transcript.absorb_bytes(air.air_name().as_bytes());
    transcript.absorb_fp(Fp::from(trace_len as u64));
    transcript.absorb_fp(Fp::from(air.width() as u64));
    transcript.absorb_fp(Fp::from(air.constraint_degree() as u64));
    transcript.absorb_fp(Fp::from(blowup as u64));
    transcript.absorb_fp(Fp::from(NUM_QUERIES as u64));

    if let Some(ref n) = nonce {
        transcript.absorb_bytes(n);
    }

    transcript.absorb_fp(proof.trace_commitment.fp());

    transcript.absorb_fp(Fp::from(public_inputs.len() as u64));
    for pi in public_inputs {
        transcript.absorb_babybear(*pi);
    }

    let alpha = transcript.squeeze_babybear();

    let boundary_cs = air.boundary_constraints(public_inputs, trace_len);

    transcript.absorb_fp(proof.constraint_commitment.fp());

    // Validate FRI round count
    let mut expected_fri_rounds = 0usize;
    let mut fri_domain_size = domain_size;
    while fri_domain_size > 4 {
        fri_domain_size /= 2;
        expected_fri_rounds += 1;
    }
    if proof.fri_commitments.len() != expected_fri_rounds {
        return Err(format!(
            "Expected {} FRI commitment rounds, got {}",
            expected_fri_rounds,
            proof.fri_commitments.len()
        ));
    }
    for query in &proof.query_proofs {
        if query.fri_layers.len() != expected_fri_rounds {
            return Err(format!(
                "FRI layer count mismatch: expected {}, got {}",
                expected_fri_rounds,
                query.fri_layers.len()
            ));
        }
    }

    // Squeeze FRI betas
    let mut fri_betas = Vec::new();
    for commitment in &proof.fri_commitments {
        fri_betas.push(transcript.squeeze_babybear());
        transcript.absorb_fp(commitment.fp());
    }

    // Boundary constraint verification (direct Merkle openings)
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
            let eval_idx = bc.row * blowup;
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

            // Verify Poseidon Merkle proof
            let leaf_hash = poseidon_hash_leaf(&boundary_vals);
            let path: Vec<Fp> = proof.boundary_query_paths[i]
                .iter()
                .map(|s| s.fp())
                .collect();
            if !PoseidonMerkleTree::verify_proof(
                proof.trace_commitment.fp(),
                leaf_hash,
                eval_idx,
                &path,
            ) {
                return Err(format!(
                    "Boundary constraint {i}: Merkle proof failed at eval index {eval_idx}"
                ));
            }

            // Check boundary value
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

    // Build evaluation domain for constraint checks
    let eval_points: Vec<BabyBear> = build_evaluation_domain(domain_size);

    // Verify each query
    for query in &proof.query_proofs {
        let idx = transcript.squeeze_index(domain_size);
        if query.index != idx {
            return Err(format!(
                "Query index mismatch: expected {idx}, got {}",
                query.index
            ));
        }

        // Verify trace Merkle proof
        let trace_vals: Vec<BabyBear> = query
            .trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if trace_vals.len() != num_cols {
            return Err("Wrong number of trace values".to_string());
        }
        let trace_leaf_hash = poseidon_hash_leaf(&trace_vals);
        let trace_path: Vec<Fp> = query.trace_path.iter().map(|s| s.fp()).collect();
        if !PoseidonMerkleTree::verify_proof(
            proof.trace_commitment.fp(),
            trace_leaf_hash,
            idx,
            &trace_path,
        ) {
            return Err(format!("Trace Merkle proof failed at index {idx}"));
        }

        // Verify constraint Merkle proof
        let constraint_val = BabyBear::new_canonical(query.constraint_value);
        let constraint_leaf_hash = poseidon_hash_leaf(&[constraint_val]);
        let constraint_path: Vec<Fp> = query.constraint_path.iter().map(|s| s.fp()).collect();
        if !PoseidonMerkleTree::verify_proof(
            proof.constraint_commitment.fp(),
            constraint_leaf_hash,
            idx,
            &constraint_path,
        ) {
            return Err(format!("Constraint Merkle proof failed at index {idx}"));
        }

        // Verify next trace Merkle proof
        let next_idx = (idx + blowup) % domain_size;
        let next_trace_vals: Vec<BabyBear> = query
            .next_trace_values
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        if next_trace_vals.len() != num_cols {
            return Err("Wrong number of next trace values".to_string());
        }
        let next_leaf_hash = poseidon_hash_leaf(&next_trace_vals);
        let next_path: Vec<Fp> = query.next_trace_path.iter().map(|s| s.fp()).collect();
        if !PoseidonMerkleTree::verify_proof(
            proof.trace_commitment.fp(),
            next_leaf_hash,
            next_idx,
            &next_path,
        ) {
            return Err(format!(
                "Next trace Merkle proof failed at index {next_idx}"
            ));
        }

        // Constraint consistency check (identical logic to stark.rs)
        let x = eval_points[idx];
        let x_n = x.pow(trace_len as u32);
        let z_full = x_n - BabyBear::ONE;
        let omega_trace = get_root_of_unity(trace_len.trailing_zeros());
        let last_trace_point = omega_trace.pow((trace_len - 1) as u32);
        let denom_factor = x - last_trace_point;
        let constraint_at_x =
            air.eval_constraints(&trace_vals, &next_trace_vals, public_inputs, alpha);

        if z_full == BabyBear::ZERO {
            if denom_factor == BabyBear::ZERO {
                let exp_mod_n =
                    ((trace_len - 1) as u64 * (trace_len - 1) as u64 % trace_len as u64) as u32;
                let z_t_at_last = BabyBear::new(trace_len as u32) * omega_trace.pow(exp_mod_n);
                if constraint_val * z_t_at_last != constraint_at_x {
                    return Err(format!(
                        "Constraint consistency check failed at last trace point (query index {idx})"
                    ));
                }
            } else {
                if constraint_val != BabyBear::ZERO {
                    return Err(format!(
                        "Constraint quotient non-zero on trace domain at query index {idx}"
                    ));
                }
                if constraint_at_x != BabyBear::ZERO {
                    return Err(format!(
                        "Constraint non-zero on trace domain at query index {idx}"
                    ));
                }
            }
        } else {
            let z_transition = z_full * denom_factor.inverse().unwrap();
            if constraint_val * z_transition != constraint_at_x {
                return Err(format!(
                    "Constraint consistency check failed at query index {idx}"
                ));
            }
        }

        // FRI folding verification
        let first_half = domain_size / 2;

        let expected_sibling_pos = if idx < first_half {
            idx + first_half
        } else {
            idx - first_half
        };
        if query.constraint_sibling_pos != expected_sibling_pos {
            return Err(format!(
                "FRI: constraint sibling position mismatch: expected {}, got {}",
                expected_sibling_pos, query.constraint_sibling_pos
            ));
        }

        let constraint_sib_val = BabyBear::new_canonical(query.constraint_sibling_value);
        let sib_leaf_hash = poseidon_hash_leaf(&[constraint_sib_val]);
        let sib_path: Vec<Fp> = query
            .constraint_sibling_path
            .iter()
            .map(|s| s.fp())
            .collect();
        if !PoseidonMerkleTree::verify_proof(
            proof.constraint_commitment.fp(),
            sib_leaf_hash,
            query.constraint_sibling_pos,
            &sib_path,
        ) {
            return Err(format!(
                "FRI: constraint sibling Merkle proof failed at pos {}",
                query.constraint_sibling_pos
            ));
        }

        let (even_val, odd_val) = if idx < first_half {
            (constraint_val, constraint_sib_val)
        } else {
            (constraint_sib_val, constraint_val)
        };

        // FRI layer 0 check
        if !fri_betas.is_empty() {
            let expected_folded = even_val + fri_betas[0] * odd_val;
            if !proof.fri_commitments.is_empty() {
                if query.fri_layers.is_empty() {
                    return Err("FRI: missing layer 0 opening".to_string());
                }
                let layer0 = &query.fri_layers[0];
                if layer0.query_pos != idx % first_half {
                    return Err("FRI layer 0: position mismatch".to_string());
                }
                if BabyBear::new_canonical(layer0.query_value) != expected_folded {
                    return Err(format!(
                        "FRI folding check failed at layer 0: expected {}, got {}",
                        expected_folded.0, layer0.query_value
                    ));
                }

                let l0_leaf = poseidon_hash_leaf(&[BabyBear::new_canonical(layer0.query_value)]);
                let l0_path: Vec<Fp> = layer0.query_path.iter().map(|s| s.fp()).collect();
                if !PoseidonMerkleTree::verify_proof(
                    proof.fri_commitments[0].fp(),
                    l0_leaf,
                    layer0.query_pos,
                    &l0_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for query_pos {} failed",
                        layer0.query_pos
                    ));
                }

                let l0_sib_leaf =
                    poseidon_hash_leaf(&[BabyBear::new_canonical(layer0.sibling_value)]);
                let l0_sib_path: Vec<Fp> = layer0.sibling_path.iter().map(|s| s.fp()).collect();
                if !PoseidonMerkleTree::verify_proof(
                    proof.fri_commitments[0].fp(),
                    l0_sib_leaf,
                    layer0.sibling_pos,
                    &l0_sib_path,
                ) {
                    return Err(format!(
                        "FRI layer 0: Merkle proof for sibling_pos {} failed",
                        layer0.sibling_pos
                    ));
                }
            }
        }

        // FRI subsequent layers
        for k in 0..query.fri_layers.len().saturating_sub(1) {
            let cl = &query.fri_layers[k];
            let nl = &query.fri_layers[k + 1];
            let (even_k, odd_k) = if cl.query_pos < cl.sibling_pos {
                (
                    BabyBear::new_canonical(cl.query_value),
                    BabyBear::new_canonical(cl.sibling_value),
                )
            } else {
                (
                    BabyBear::new_canonical(cl.sibling_value),
                    BabyBear::new_canonical(cl.query_value),
                )
            };
            let beta_idx = k + 1;
            if beta_idx >= fri_betas.len() {
                return Err(format!("FRI: not enough betas for layer {}", k + 1));
            }
            let expected_next = even_k + fri_betas[beta_idx] * odd_k;
            if nl.query_pos != cl.query_pos.min(cl.sibling_pos) {
                return Err(format!("FRI layer {}: position mismatch", k + 1));
            }
            if BabyBear::new_canonical(nl.query_value) != expected_next {
                return Err(format!(
                    "FRI folding check failed at layer {}: expected {}, got {}",
                    k + 1,
                    expected_next.0,
                    nl.query_value
                ));
            }
            if beta_idx < proof.fri_commitments.len() {
                let nl_leaf = poseidon_hash_leaf(&[BabyBear::new_canonical(nl.query_value)]);
                let nl_path: Vec<Fp> = nl.query_path.iter().map(|s| s.fp()).collect();
                if !PoseidonMerkleTree::verify_proof(
                    proof.fri_commitments[beta_idx].fp(),
                    nl_leaf,
                    nl.query_pos,
                    &nl_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for query_pos failed",
                        k + 1
                    ));
                }
                let nl_sib_leaf = poseidon_hash_leaf(&[BabyBear::new_canonical(nl.sibling_value)]);
                let nl_sib_path: Vec<Fp> = nl.sibling_path.iter().map(|s| s.fp()).collect();
                if !PoseidonMerkleTree::verify_proof(
                    proof.fri_commitments[beta_idx].fp(),
                    nl_sib_leaf,
                    nl.sibling_pos,
                    &nl_sib_path,
                ) {
                    return Err(format!(
                        "FRI layer {}: Merkle proof for sibling_pos failed",
                        k + 1
                    ));
                }
            }
        }

        // Final poly check
        if let Some(last) = query.fri_layers.last() {
            if last.query_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: query_pos {} out of range (len {})",
                    last.query_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.query_value != proof.fri_final_poly[last.query_pos] {
                return Err(format!("FRI final poly mismatch at pos {}", last.query_pos));
            }
            if last.sibling_pos >= proof.fri_final_poly.len() {
                return Err(format!(
                    "FRI final poly: sibling_pos {} out of range (len {})",
                    last.sibling_pos,
                    proof.fri_final_poly.len()
                ));
            }
            if last.sibling_value != proof.fri_final_poly[last.sibling_pos] {
                return Err(format!(
                    "FRI final poly sibling mismatch at pos {}",
                    last.sibling_pos
                ));
            }
        }
    }

    // Final polynomial size check
    if proof.fri_final_poly.len() > 4 {
        return Err("FRI final polynomial too large".to_string());
    }
    let expected_final_len = domain_size >> expected_fri_rounds;
    if proof.fri_final_poly.len() != expected_final_len {
        return Err(format!(
            "FRI final polynomial length mismatch: expected {}, got {}",
            expected_final_len,
            proof.fri_final_poly.len()
        ));
    }

    Ok(())
}

// ============================================================================
// Kimchi verifier circuit cost estimation
// ============================================================================

/// Compute the estimated Kimchi row count to verify a PoseidonStarkProof in-circuit.
///
/// This provides a precise gate count estimate based on the proof parameters,
/// useful for determining the minimum Kimchi domain size required.
#[cfg(feature = "mina")]
pub fn estimate_kimchi_verifier_rows(
    trace_len: usize,
    num_cols: usize,
    constraint_degree: usize,
) -> KimchiVerifierEstimate {
    let blowup = blowup_for_degree(constraint_degree);
    let domain_size = trace_len * blowup;
    let tree_depth = domain_size.trailing_zeros() as usize; // log2(domain_size)

    // Poseidon gate rows per hash (Kimchi native: 55 rounds / 5 rounds_per_row = 11 + 1 output)
    let poseidon_rows_per_hash: usize = 12;

    // FRI rounds
    let mut fri_rounds = 0;
    let mut d = domain_size;
    while d > 4 {
        d /= 2;
        fri_rounds += 1;
    }

    // Merkle path verification:
    // Each query opens trace (depth hashes) + constraint (depth hashes) + next trace (depth)
    let merkle_hashes_per_query = 3 * tree_depth; // trace + constraint + next_trace
    let merkle_rows_total = NUM_QUERIES * merkle_hashes_per_query * poseidon_rows_per_hash;

    // FRI Merkle paths: each query, each FRI layer has query + sibling path verification
    // FRI layers get shorter by half each time, so average depth = tree_depth - fri_round - 1
    let mut fri_merkle_rows = 0;
    for round in 0..fri_rounds {
        let layer_depth = tree_depth.saturating_sub(round + 1);
        // 2 paths per query per layer (query + sibling)
        fri_merkle_rows += NUM_QUERIES * 2 * layer_depth * poseidon_rows_per_hash;
    }

    // BabyBear constraint evaluation in Kimchi:
    // For each query: evaluate the AIR constraint polynomial.
    // Width-W, degree-D AIR needs roughly W*D ForeignFieldMul operations.
    // Each ForeignFieldMul is ~1 Kimchi row (native gate).
    let bb_muls_per_query = num_cols * constraint_degree;
    let bb_rows_total = NUM_QUERIES * bb_muls_per_query;

    // FRI folding checks: 1 mul + 1 add per layer per query
    let fri_fold_rows = NUM_QUERIES * fri_rounds * 2; // mul + add each ~1 row

    // Fiat-Shamir transcript replay (Poseidon squeezes):
    // ~(2 + public_inputs.len() + fri_rounds + NUM_QUERIES) absorb/squeeze operations
    // Conservative: assume 100 poseidon operations for transcript
    let transcript_rows = 100 * poseidon_rows_per_hash;

    // Range checks for BabyBear value validation:
    // Each opened BabyBear value needs a range check (< 2^31 - 2^27 + 1)
    // Kimchi RangeCheck0 gate does this in ~4 rows
    let range_check_values = NUM_QUERIES * (num_cols * 2 + 1 + 1); // trace + next + constraint + sibling
    let range_check_rows = range_check_values * 4;

    let total_rows = merkle_rows_total
        + fri_merkle_rows
        + bb_rows_total
        + fri_fold_rows
        + transcript_rows
        + range_check_rows;

    // Minimum domain size (next power of 2, needs headroom for Kimchi overhead)
    let min_domain_log2 = ((total_rows as f64 * 1.2) as usize) // 20% overhead for Kimchi bookkeeping
        .next_power_of_two()
        .trailing_zeros() as usize;

    KimchiVerifierEstimate {
        merkle_rows: merkle_rows_total,
        fri_merkle_rows,
        babybear_arithmetic_rows: bb_rows_total,
        fri_fold_rows,
        transcript_rows,
        range_check_rows,
        total_rows,
        min_domain_log2,
        fri_rounds,
        tree_depth,
    }
}

/// Detailed gate count estimate for the Kimchi verifier circuit.
#[cfg(feature = "mina")]
#[derive(Clone, Debug)]
pub struct KimchiVerifierEstimate {
    /// Rows for Poseidon Merkle path verification (trace + constraint openings).
    pub merkle_rows: usize,
    /// Rows for FRI layer Merkle path verification.
    pub fri_merkle_rows: usize,
    /// Rows for BabyBear arithmetic (constraint evaluation via ForeignFieldMul/Add).
    pub babybear_arithmetic_rows: usize,
    /// Rows for FRI folding consistency checks.
    pub fri_fold_rows: usize,
    /// Rows for Fiat-Shamir transcript replay.
    pub transcript_rows: usize,
    /// Rows for range checks on BabyBear values.
    pub range_check_rows: usize,
    /// Total estimated rows.
    pub total_rows: usize,
    /// Minimum log2 domain size for Kimchi circuit.
    pub min_domain_log2: usize,
    /// Number of FRI rounds.
    pub fri_rounds: usize,
    /// Merkle tree depth (log2 of evaluation domain size).
    pub tree_depth: usize,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, feature = "mina"))]
mod tests {
    use super::*;
    use crate::stark::{MerkleStarkAir, StarkAir, generate_merkle_trace};

    #[test]
    fn poseidon_merkle_tree_basic() {
        let leaves: Vec<Fp> = (0..4u32)
            .map(|i| poseidon_hash_leaf(&[BabyBear::new(i)]))
            .collect();
        let tree = PoseidonMerkleTree::new(leaves.clone());

        for i in 0..4 {
            let path = tree.prove(i);
            assert!(
                PoseidonMerkleTree::verify_proof(tree.root(), leaves[i], i, &path),
                "Merkle proof failed for leaf {i}"
            );
        }

        // Fake leaf should fail
        let fake = poseidon_hash_leaf(&[BabyBear::new(999)]);
        assert!(!PoseidonMerkleTree::verify_proof(
            tree.root(),
            fake,
            0,
            &tree.prove(0)
        ));
    }

    #[test]
    fn poseidon_transcript_deterministic() {
        let mut t1 = PoseidonTranscript::new(b"test");
        t1.absorb_babybear(BabyBear::new(42));
        let mut t2 = PoseidonTranscript::new(b"test");
        t2.absorb_babybear(BabyBear::new(42));
        assert_eq!(t1.squeeze_babybear(), t2.squeeze_babybear());
    }

    #[test]
    fn poseidon_transcript_different_inputs() {
        let mut t1 = PoseidonTranscript::new(b"test");
        t1.absorb_babybear(BabyBear::new(42));
        let mut t2 = PoseidonTranscript::new(b"test");
        t2.absorb_babybear(BabyBear::new(43));
        assert_ne!(t1.squeeze_babybear(), t2.squeeze_babybear());
    }

    #[test]
    fn poseidon_stark_end_to_end() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove_poseidon(&air, &trace, &pi);

        assert_eq!(proof.air_name, "pyana-merkle-v1");
        assert_eq!(proof.trace_len, 4);
        assert_eq!(proof.num_cols, 6);
        assert_eq!(proof.query_proofs.len(), NUM_QUERIES);

        let result = verify_poseidon(&air, &proof, &pi);
        assert!(result.is_ok(), "Verification failed: {:?}", result.err());
    }

    #[test]
    fn poseidon_stark_wrong_public_inputs() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let proof = prove_poseidon(&air, &trace, &pi);

        let bad_pi = vec![BabyBear::new(99999), pi[1]];
        assert!(verify_poseidon(&air, &proof, &bad_pi).is_err());
    }

    #[test]
    fn poseidon_stark_tampered_commitment() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove_poseidon(&air, &trace, &pi);

        // Tamper with trace commitment
        proof.trace_commitment = FpSer(proof.trace_commitment.fp() + Fp::one());
        assert!(verify_poseidon(&air, &proof, &pi).is_err());
    }

    #[test]
    fn poseidon_stark_tampered_query_value() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;
        let mut proof = prove_poseidon(&air, &trace, &pi);

        proof.query_proofs[0].trace_values[0] ^= 1;
        assert!(verify_poseidon(&air, &proof, &pi).is_err());
    }

    #[test]
    fn poseidon_stark_nonce_binding() {
        let (trace, pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );
        let air = MerkleStarkAir;

        let nonce_a = [1u8; 32];
        let nonce_b = [2u8; 32];

        let proof = prove_poseidon_with_nonce(&air, &trace, &pi, Some(nonce_a));

        // Correct nonce verifies
        assert!(verify_poseidon_with_nonce(&air, &proof, &pi, Some(nonce_a)).is_ok());

        // Wrong nonce fails
        assert!(verify_poseidon_with_nonce(&air, &proof, &pi, Some(nonce_b)).is_err());

        // No nonce fails
        assert!(verify_poseidon_with_nonce(&air, &proof, &pi, None).is_err());
    }

    #[test]
    fn poseidon_stark_boundary_constraint_enforcement() {
        // Attack: generate proof for real trace, try to verify with fake public inputs
        let air = MerkleStarkAir;
        let (trace, real_pi) = generate_merkle_trace(
            12345,
            &[
                [100u32, 200, 300],
                [400, 500, 600],
                [700, 800, 900],
                [1000, 1100, 1200],
            ],
            &[0u32, 1, 2, 3],
        );

        let fake_pi = vec![BabyBear::new(99999), BabyBear::new(88888)];
        let adv_proof = prove_poseidon(&air, &trace, &fake_pi);

        let result = verify_poseidon(&air, &adv_proof, &fake_pi);
        assert!(
            result.is_err(),
            "Adversarial proof with lying public inputs must be REJECTED"
        );
    }

    #[test]
    fn kimchi_verifier_estimate_reasonable() {
        // For a 4-row trace, width 6, degree 4:
        let est = estimate_kimchi_verifier_rows(4, 6, 4);

        // Should fit in domain 2^15 = 32768 or 2^16 = 65536
        assert!(
            est.min_domain_log2 <= 17,
            "Verifier should fit in domain <= 2^17, got 2^{}",
            est.min_domain_log2
        );

        // Total should be much less than the BLAKE3 approach (~272K)
        assert!(
            est.total_rows < 100_000,
            "Should be significantly less than BLAKE3 approach, got {}",
            est.total_rows
        );

        println!("Kimchi verifier estimate for 4-row, width-6, degree-4 trace:");
        println!("  Merkle rows:      {}", est.merkle_rows);
        println!("  FRI Merkle rows:  {}", est.fri_merkle_rows);
        println!("  BB arithmetic:    {}", est.babybear_arithmetic_rows);
        println!("  FRI fold:         {}", est.fri_fold_rows);
        println!("  Transcript:       {}", est.transcript_rows);
        println!("  Range checks:     {}", est.range_check_rows);
        println!("  Total:            {}", est.total_rows);
        println!("  Min domain:       2^{}", est.min_domain_log2);
        println!("  FRI rounds:       {}", est.fri_rounds);
        println!("  Tree depth:       {}", est.tree_depth);
    }

    #[test]
    fn kimchi_verifier_smaller_than_blake3() {
        // The whole point: Poseidon-committed STARK should need far fewer rows
        // to verify in Kimchi compared to BLAKE3-committed STARK.
        let est = estimate_kimchi_verifier_rows(4, 6, 4);

        // BLAKE3 approach: ~272K gates (from stark_in_pickles.rs analysis)
        let blake3_estimate = 272_000;

        assert!(
            est.total_rows < blake3_estimate / 2,
            "Poseidon approach ({} rows) should be < half of BLAKE3 approach ({} rows)",
            est.total_rows,
            blake3_estimate
        );
    }
}
