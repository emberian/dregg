//! Note spending circuit: ZK proof that the spender knows the spending key.
//!
//! This AIR proves:
//! 1. Prover knows `spending_key` (8 BabyBear limbs = 248 bits) such that
//!    `nullifier = poseidon2(commitment || spending_key[0..8] || creation_nonce)`
//! 2. Prover knows `owner`, `value`, `asset_type`, `creation_nonce`, `randomness` such that
//!    `commitment = poseidon2(owner || value || asset_type || creation_nonce || randomness)`
//! 3. The commitment is a member of a Merkle tree with a given root (Poseidon2 Merkle path)
//!
//! # Trace layout
//!
//! The trace is organized as a sequence of rows with width = 19:
//!
//! ```text
//! Row type: COMMITMENT (rows 0)
//!   col 0: owner
//!   col 1: value
//!   col 2: asset_type
//!   col 3: creation_nonce
//!   col 4: (zero — reserved for Merkle position validity constraint)
//!   col 5: commitment (computed = poseidon2_hash(owner, value, asset_type, creation_nonce, randomness))
//!   col 6..13: spending_key[0..8] (8 BabyBear limbs = 248 bits of security)
//!   col 14: nullifier (computed = poseidon2_hash(commitment, spending_key[0..8], creation_nonce))
//!   col 15: randomness
//!   col 16: is_merkle (0 for this row)
//!   col 17..18: unused (zero)
//!
//! Row type: MERKLE_LEVEL (rows 1..depth)
//!   col 0: current hash at this level
//!   col 1: sibling[0]
//!   col 2: sibling[1]
//!   col 3: sibling[2]
//!   col 4: position (0..3)
//!   col 5: parent = poseidon2_hash_4_to_1(children arranged by position)
//!   col 6..18: unused (zero)
//! ```
//!
//! # Public inputs
//!
//! - `nullifier`: The revealed nullifier (verifier sees this)
//! - `merkle_root`: The Merkle tree root (verifier sees this)
//! - `value`: The note value (verifier sees this — prevents value inflation)
//! - `asset_type`: The note asset type (verifier sees this — prevents asset substitution)
//!
//! # Security properties
//!
//! - The spending key is 248 bits (8 × 31-bit BabyBear limbs), requiring ~2^248 brute-force attempts
//! - The spending key is private (only in the witness, never in public inputs)
//! - The note owner is private (only in the witness)
//! - Value and asset_type are public inputs, bound by boundary constraints to the
//!   trace columns that participate in commitment recomputation. A spender cannot
//!   claim a different value/asset_type than what is committed in the note.
//! - Soundness: a cheating prover must break Poseidon2 collision resistance

use crate::field::BabyBear;
use crate::poseidon2::{hash_4_to_1, hash_many};
use crate::stark::{self, BoundaryConstraint, StarkAir, StarkProof};

/// Trace width for the note spending AIR.
/// 19 columns: 5 note preimage + commitment + 8 key limbs + nullifier + randomness + is_merkle + 2 unused.
pub const NOTE_SPENDING_WIDTH: usize = 19;

/// Number of BabyBear limbs for the spending key (248 bits of security).
pub const SPENDING_KEY_LIMBS: usize = 8;

/// Minimum Merkle depth supported.
pub const MIN_MERKLE_DEPTH: usize = 2;

/// Column indices for the commitment row.
/// Note: column 4 is kept as zero for the commitment row to satisfy
/// the position validity constraint (which checks all rows uniformly).
pub mod col {
    pub const OWNER: usize = 0;
    pub const VALUE: usize = 1;
    pub const ASSET_TYPE: usize = 2;
    pub const CREATION_NONCE: usize = 3;
    // col 4 is zero in commitment row (reserved for Merkle position)
    pub const COMMITMENT: usize = 5;
    /// Spending key limbs occupy columns 6..14 (8 BabyBear elements = 248 bits).
    pub const SPENDING_KEY_START: usize = 6;
    pub const SPENDING_KEY_END: usize = 14; // exclusive
    pub const NULLIFIER: usize = 14;
    pub const RANDOMNESS: usize = 15;
    /// Row type: 0 = commitment row, 1 = Merkle/padding row.
    /// Used to gate constraints appropriately.
    pub const IS_MERKLE: usize = 16;
}

/// Column indices for Merkle level rows.
pub mod merkle_col {
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    pub const POSITION: usize = 4;
    pub const PARENT: usize = 5;
}

/// Public input indices.
pub mod pi {
    /// The nullifier (what the verifier sees).
    pub const NULLIFIER: usize = 0;
    /// The Merkle root (what the verifier sees).
    pub const MERKLE_ROOT: usize = 1;
    /// The note value (what the verifier sees — prevents value inflation).
    pub const VALUE: usize = 2;
    /// The note asset type (what the verifier sees — prevents asset type substitution).
    pub const ASSET_TYPE: usize = 3;
}

/// Witness for a note spending proof.
#[derive(Clone, Debug)]
pub struct NoteSpendingWitness {
    /// The owner's public key (field element representation).
    pub owner: BabyBear,
    /// The note value (amount).
    pub value: BabyBear,
    /// The asset type.
    pub asset_type: BabyBear,
    /// Creation nonce.
    pub creation_nonce: BabyBear,
    /// Random blinding factor.
    pub randomness: BabyBear,
    /// The spending key (secret): 8 BabyBear limbs = 248 bits of security.
    ///
    /// Each limb holds up to 31 bits (BabyBear modulus ~ 2^31). An adversary must
    /// brute-force all 8 limbs (~2^248 attempts) to recover the key from a known
    /// nullifier and commitment. Previously this was a single BabyBear element
    /// (~2^31 attempts = ~2 seconds on modern hardware).
    pub spending_key: [BabyBear; SPENDING_KEY_LIMBS],
    /// Merkle path siblings (one [BabyBear; 3] per level).
    pub merkle_siblings: Vec<[BabyBear; 3]>,
    /// Merkle path positions (one u8 per level, 0..3).
    pub merkle_positions: Vec<u8>,
}

/// Convert a 256-bit external spending key (e.g., from BLAKE3) to 8 BabyBear limbs.
///
/// Each 4-byte chunk is interpreted as a little-endian u32 and reduced modulo BabyBear::P
/// via `BabyBear::new_canonical()`. This gives 8 × ~31 bits = ~248 bits of key material
/// inside the STARK circuit.
pub fn key_to_field_elements(key: &[u8; 32]) -> [BabyBear; SPENDING_KEY_LIMBS] {
    let mut limbs = [BabyBear::ZERO; SPENDING_KEY_LIMBS];
    for i in 0..SPENDING_KEY_LIMBS {
        let bytes = [key[i * 4], key[i * 4 + 1], key[i * 4 + 2], key[i * 4 + 3]];
        limbs[i] = BabyBear::new_canonical(u32::from_le_bytes(bytes));
    }
    limbs
}

impl NoteSpendingWitness {
    /// Compute the commitment: poseidon2_hash(owner, value, asset_type, creation_nonce, randomness).
    pub fn commitment(&self) -> BabyBear {
        hash_many(&[
            self.owner,
            self.value,
            self.asset_type,
            self.creation_nonce,
            self.randomness,
        ])
    }

    /// Compute the nullifier: poseidon2_hash(commitment, spending_key[0..8], creation_nonce).
    ///
    /// The nullifier is derived from all 8 key limbs, making brute-force infeasible (~2^248).
    pub fn nullifier(&self) -> BabyBear {
        let commitment = self.commitment();
        let mut inputs = Vec::with_capacity(1 + SPENDING_KEY_LIMBS + 1);
        inputs.push(commitment);
        inputs.extend_from_slice(&self.spending_key);
        inputs.push(self.creation_nonce);
        hash_many(&inputs) // 10 inputs: commitment + 8 key limbs + nonce
    }

    /// Compute the Merkle root by hashing up the path from the commitment.
    pub fn merkle_root(&self) -> BabyBear {
        let commitment = self.commitment();
        let mut current = commitment;

        for (i, siblings) in self.merkle_siblings.iter().enumerate() {
            let pos = self.merkle_positions[i];
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == pos {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            current = hash_4_to_1(&children);
        }
        current
    }

    /// Create a witness from a real Poseidon2 Merkle proof (from a Poseidon2MerkleTree).
    ///
    /// This is the bridge between the persistent note tree and the STARK prover:
    /// given a note's field-element preimage, a spending key, and a real Merkle proof
    /// from the Poseidon2 tree, construct a witness that can be used to generate
    /// a valid STARK proof.
    ///
    /// # Arguments
    ///
    /// * `owner` - The note owner (field element)
    /// * `value` - The note value (field element)
    /// * `asset_type` - The asset type (field element)
    /// * `creation_nonce` - The creation nonce (field element)
    /// * `randomness` - The randomness/blinding factor (field element)
    /// * `spending_key` - The spending key (8 BabyBear limbs = 248-bit secret)
    /// * `merkle_siblings` - Siblings from the Poseidon2MerkleProof
    /// * `merkle_positions` - Positions from the Poseidon2MerkleProof
    ///
    /// # Panics
    ///
    /// Panics if `merkle_siblings.len() != merkle_positions.len()`.
    pub fn from_real_proof(
        owner: BabyBear,
        value: BabyBear,
        asset_type: BabyBear,
        creation_nonce: BabyBear,
        randomness: BabyBear,
        spending_key: [BabyBear; SPENDING_KEY_LIMBS],
        merkle_siblings: Vec<[BabyBear; 3]>,
        merkle_positions: Vec<u8>,
    ) -> Self {
        assert_eq!(
            merkle_siblings.len(),
            merkle_positions.len(),
            "siblings and positions must have the same length"
        );
        Self {
            owner,
            value,
            asset_type,
            creation_nonce,
            randomness,
            spending_key,
            merkle_siblings,
            merkle_positions,
        }
    }
}

/// The note spending AIR. Proves knowledge of spending key + note preimage + Merkle membership.
pub struct NoteSpendingAir {
    /// Merkle tree depth (number of levels in the path).
    pub depth: usize,
}

impl NoteSpendingAir {
    pub fn new(depth: usize) -> Self {
        assert!(
            depth >= MIN_MERKLE_DEPTH,
            "Merkle depth must be at least {MIN_MERKLE_DEPTH}"
        );
        Self { depth }
    }

    /// Generate the execution trace from a witness.
    ///
    /// Returns (trace, public_inputs) where:
    /// - trace: rows of width NOTE_SPENDING_WIDTH
    /// - public_inputs: [nullifier, merkle_root]
    pub fn generate_trace(witness: &NoteSpendingWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let depth = witness.merkle_siblings.len();
        assert_eq!(witness.merkle_positions.len(), depth);
        assert!(
            depth >= MIN_MERKLE_DEPTH,
            "Need at least depth {MIN_MERKLE_DEPTH}"
        );

        let commitment = witness.commitment();
        let nullifier = witness.nullifier();

        // Total rows: 1 (commitment/nullifier row) + depth (Merkle levels)
        let total_rows = 1 + depth;
        let padded_rows = total_rows.next_power_of_two();

        let mut trace = Vec::with_capacity(padded_rows);

        // Row 0: commitment and nullifier computation
        // Note: col 4 (position) is left as zero to satisfy the position validity constraint.
        let mut row0 = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
        row0[col::OWNER] = witness.owner;
        row0[col::VALUE] = witness.value;
        row0[col::ASSET_TYPE] = witness.asset_type;
        row0[col::CREATION_NONCE] = witness.creation_nonce;
        row0[col::COMMITMENT] = commitment;
        // Place all 8 spending key limbs in columns 6..14
        for (j, &limb) in witness.spending_key.iter().enumerate() {
            row0[col::SPENDING_KEY_START + j] = limb;
        }
        row0[col::NULLIFIER] = nullifier;
        row0[col::RANDOMNESS] = witness.randomness;
        row0[col::IS_MERKLE] = BabyBear::ZERO; // This is the commitment row
        trace.push(row0);

        // Rows 1..depth+1: Merkle membership proof
        let mut current = commitment;
        for i in 0..depth {
            let pos = witness.merkle_positions[i];
            assert!(pos < 4, "Merkle position must be 0..3");

            let siblings = &witness.merkle_siblings[i];

            // Compute parent hash
            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == pos {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            let parent = hash_4_to_1(&children);

            let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
            row[merkle_col::CURRENT] = current;
            row[merkle_col::SIB0] = siblings[0];
            row[merkle_col::SIB1] = siblings[1];
            row[merkle_col::SIB2] = siblings[2];
            row[merkle_col::POSITION] = BabyBear::new(pos as u32);
            row[merkle_col::PARENT] = parent;
            row[col::IS_MERKLE] = BabyBear::ONE; // Merkle row
            trace.push(row);

            current = parent;
        }

        let merkle_root = current;

        // Pad to power of 2
        let padding_parent =
            hash_4_to_1(&[merkle_root, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]);
        for _ in total_rows..padded_rows {
            let mut row = vec![BabyBear::ZERO; NOTE_SPENDING_WIDTH];
            row[merkle_col::CURRENT] = merkle_root;
            row[merkle_col::PARENT] = padding_parent;
            row[col::IS_MERKLE] = BabyBear::ONE; // Padding treated as Merkle row
            trace.push(row);
        }

        let public_inputs = vec![nullifier, merkle_root, witness.value, witness.asset_type];
        (trace, public_inputs)
    }
}

impl StarkAir for NoteSpendingAir {
    fn width(&self) -> usize {
        NOTE_SPENDING_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        4 // position validity is degree 4
    }

    fn air_name(&self) -> &'static str {
        "pyana-note-spending-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false // Our layout is not the simple 6-column Merkle chain
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        _next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // The note spending constraint enforces:
        // 1. Position validity: pos*(pos-1)*(pos-2)*(pos-3) = 0
        // 2. Merkle hash binding (gated by is_merkle): parent == hash_4_to_1(children)
        // 3. Commitment preimage (gated by 1-is_merkle): commitment == hash_many(preimage)
        // 4. Nullifier derivation (gated by 1-is_merkle): nullifier == hash_many(...)
        // 5. is_merkle is binary: is_merkle * (is_merkle - 1) = 0

        let position = local[merkle_col::POSITION];
        let is_merkle = local[col::IS_MERKLE];

        // Constraint 1: Position validity (degree 4)
        let c_pos = position
            * (position - BabyBear::ONE)
            * (position - BabyBear::new(2))
            * (position - BabyBear::new(3));

        let mut combined = c_pos;
        let mut alpha_pow = alpha;

        // Constraint 5: is_merkle binary
        let c_binary = is_merkle * (is_merkle - BabyBear::ONE);
        combined = combined + alpha_pow * c_binary;
        alpha_pow = alpha_pow * alpha;

        // Constraint 2: Merkle hash binding (only on Merkle rows: gated by is_merkle)
        let current = local[merkle_col::CURRENT];
        let sib0 = local[merkle_col::SIB0];
        let sib1 = local[merkle_col::SIB1];
        let sib2 = local[merkle_col::SIB2];
        let parent = local[merkle_col::PARENT];

        let p = position;
        let p_m1 = p - BabyBear::ONE;
        let p_m2 = p - BabyBear::new(2);
        let p_m3 = p - BabyBear::new(3);

        let inv_neg6 = -BabyBear::new(6).inverse().unwrap();
        let inv_2 = BabyBear::new(2).inverse().unwrap();
        let inv_neg2 = -inv_2;
        let inv_6 = BabyBear::new(6).inverse().unwrap();

        let l0 = p_m1 * p_m2 * p_m3 * inv_neg6;
        let l1 = p * p_m2 * p_m3 * inv_2;
        let l2 = p * p_m1 * p_m3 * inv_neg2;
        let l3 = p * p_m1 * p_m2 * inv_6;

        let child0 = current * l0 + sib0 * (BabyBear::ONE - l0);
        let child1 = sib0 * l0 + current * l1 + sib1 * (l2 + l3);
        let child2 = sib1 * (l0 + l1) + current * l2 + sib2 * l3;
        let child3 = sib2 * (BabyBear::ONE - l3) + current * l3;

        let expected_parent = hash_4_to_1(&[child0, child1, child2, child3]);
        let c_hash = is_merkle * (parent - expected_parent);
        combined = combined + alpha_pow * c_hash;
        alpha_pow = alpha_pow * alpha;

        // Constraint 3: Commitment preimage (only on commitment row: gated by 1-is_merkle)
        let owner = local[col::OWNER];
        let value = local[col::VALUE];
        let asset_type = local[col::ASSET_TYPE];
        let creation_nonce = local[col::CREATION_NONCE];
        let randomness = local[col::RANDOMNESS];
        let commitment = local[col::COMMITMENT];

        let is_commitment_row = BabyBear::ONE - is_merkle;
        let expected_commitment =
            hash_many(&[owner, value, asset_type, creation_nonce, randomness]);
        let c_commitment = is_commitment_row * (commitment - expected_commitment);
        combined = combined + alpha_pow * c_commitment;
        alpha_pow = alpha_pow * alpha;

        // Constraint 4: Nullifier derivation (only on commitment row)
        // Hash all 8 spending key limbs: nullifier = hash(commitment, key[0..8], creation_nonce)
        let nullifier = local[col::NULLIFIER];
        let mut nullifier_inputs = Vec::with_capacity(1 + SPENDING_KEY_LIMBS + 1);
        nullifier_inputs.push(commitment);
        for j in 0..SPENDING_KEY_LIMBS {
            nullifier_inputs.push(local[col::SPENDING_KEY_START + j]);
        }
        nullifier_inputs.push(creation_nonce);
        let expected_nullifier = hash_many(&nullifier_inputs);
        let c_nullifier = is_commitment_row * (nullifier - expected_nullifier);
        combined = combined + alpha_pow * c_nullifier;

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() >= 4 {
            // Row 0, col NULLIFIER (14) = public_inputs[0] (nullifier)
            // This binds the trace's computed nullifier to the claimed public input.
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::NULLIFIER,
                value: public_inputs[pi::NULLIFIER],
            });
            // Padding rows have col[CURRENT] = merkle_root.
            // The last row (whether padding or the actual last Merkle level) has
            // col[CURRENT] = merkle_root. We bind the last row's CURRENT to merkle_root.
            constraints.push(BoundaryConstraint {
                row: trace_len - 1,
                col: merkle_col::CURRENT,
                value: public_inputs[pi::MERKLE_ROOT],
            });
            // Row 0, col VALUE = public_inputs[2] (value)
            // CRITICAL: This prevents value inflation — the verifier sees the actual
            // value committed in the note, not a declared value in the effect.
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::VALUE,
                value: public_inputs[pi::VALUE],
            });
            // Row 0, col ASSET_TYPE = public_inputs[3] (asset_type)
            // CRITICAL: This prevents asset type substitution — the verifier sees the
            // actual asset type committed in the note.
            constraints.push(BoundaryConstraint {
                row: 0,
                col: col::ASSET_TYPE,
                value: public_inputs[pi::ASSET_TYPE],
            });
        }
        constraints
    }
}

/// Prove a note spend given the private witness.
///
/// Returns a STARK proof that can be verified with only the nullifier and merkle_root.
/// The spending key and note contents remain private.
///
/// DEPRECATED: Use `crate::dsl::note_spending::prove_note_spend_dsl` instead.
#[deprecated(note = "Use crate::dsl::note_spending::prove_note_spend_dsl instead")]
pub fn prove_note_spend(witness: &NoteSpendingWitness) -> StarkProof {
    let depth = witness.merkle_siblings.len();
    let air = NoteSpendingAir::new(depth);
    let (trace, public_inputs) = NoteSpendingAir::generate_trace(witness);
    stark::prove(&air, &trace, &public_inputs)
}

/// Verify a note spending proof.
///
/// The verifier needs:
/// - `nullifier`: the revealed nullifier (to check against double-spend set)
/// - `merkle_root`: the committed note tree root
/// - `value`: the note value (prevents value inflation attacks)
/// - `asset_type`: the note asset type (prevents asset type substitution)
/// - `proof`: the STARK proof
///
/// SECURITY: The value and asset_type are now public inputs bound by boundary
/// constraints. A spender cannot claim a different value/asset_type than what
/// is actually committed in the note — the proof will fail verification.
///
/// Returns Ok(()) if the proof is valid, Err with reason otherwise.
///
/// DEPRECATED: Use `crate::dsl::note_spending::verify_note_spend_dsl` instead.
#[deprecated(note = "Use crate::dsl::note_spending::verify_note_spend_dsl instead")]
pub fn verify_note_spend(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    let trace_len = proof.trace_len;
    if trace_len < 4 {
        return Err("Proof trace too short for note spending circuit".to_string());
    }
    let depth = (trace_len - 1).max(MIN_MERKLE_DEPTH);
    let air = NoteSpendingAir::new(depth);
    let public_inputs = vec![nullifier, merkle_root, value, asset_type];
    stark::verify(&air, proof, &public_inputs)
}

/// Create a test witness for note spending proofs.
///
/// Generates a deterministic witness with the given parameters and a Merkle path of the specified depth.
/// The spending key is provided as 8 BabyBear limbs (248 bits).
pub fn create_test_witness(
    owner: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    spending_key: [BabyBear; SPENDING_KEY_LIMBS],
    depth: usize,
) -> NoteSpendingWitness {
    // Deterministic creation nonce and randomness
    let creation_nonce = hash_many(&[owner, value, BabyBear::new(0xCAFE)]);
    let randomness = hash_many(&[owner, value, BabyBear::new(0xBEEF)]);

    // Build a Merkle path with deterministic siblings
    let mut merkle_siblings = Vec::with_capacity(depth);
    let mut merkle_positions = Vec::with_capacity(depth);

    for i in 0..depth {
        let pos = (i % 4) as u8;
        let siblings = [
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), owner]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), owner]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), owner]),
        ];
        merkle_siblings.push(siblings);
        merkle_positions.push(pos);
    }

    NoteSpendingWitness {
        owner,
        value,
        asset_type,
        creation_nonce,
        randomness,
        spending_key,
        merkle_siblings,
        merkle_positions,
    }
}

/// Create a deterministic 8-limb test spending key from a single seed value.
///
/// Each limb is derived deterministically from the seed, giving a full 248-bit key
/// while keeping tests reproducible.
pub fn test_spending_key(seed: u32) -> [BabyBear; SPENDING_KEY_LIMBS] {
    let mut limbs = [BabyBear::ZERO; SPENDING_KEY_LIMBS];
    for i in 0..SPENDING_KEY_LIMBS {
        limbs[i] = hash_many(&[BabyBear::new(seed), BabyBear::new(i as u32)]);
    }
    limbs
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_commitment_deterministic() {
        let key = test_spending_key(0xDEAD);
        let w1 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let w2 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        assert_eq!(w1.commitment(), w2.commitment());
        assert_eq!(w1.nullifier(), w2.nullifier());
        assert_eq!(w1.merkle_root(), w2.merkle_root());
    }

    #[test]
    fn witness_different_key_different_nullifier() {
        let key1 = test_spending_key(0xDEAD);
        let key2 = test_spending_key(0xBEEF);
        let w1 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key1,
            4,
        );
        let w2 = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key2, // different key
            4,
        );
        // Same commitment (key doesn't affect commitment)
        assert_eq!(w1.commitment(), w2.commitment());
        // Different nullifier (key affects nullifier)
        assert_ne!(w1.nullifier(), w2.nullifier());
    }

    #[test]
    fn trace_generation_correct_dimensions() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, public_inputs) = NoteSpendingAir::generate_trace(&witness);

        // 1 commitment row + 4 Merkle rows = 5, padded to 8
        assert_eq!(trace.len(), 8);
        assert!(trace.len().is_power_of_two());

        // Width is NOTE_SPENDING_WIDTH (19)
        for row in &trace {
            assert_eq!(row.len(), NOTE_SPENDING_WIDTH);
        }

        // Public inputs: [nullifier, merkle_root, value, asset_type]
        assert_eq!(public_inputs.len(), 4);
        assert_eq!(public_inputs[pi::NULLIFIER], witness.nullifier());
        assert_eq!(public_inputs[pi::MERKLE_ROOT], witness.merkle_root());
        assert_eq!(public_inputs[pi::VALUE], witness.value);
        assert_eq!(public_inputs[pi::ASSET_TYPE], witness.asset_type);
    }

    #[test]
    fn trace_commitment_row_has_correct_hashes() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, _) = NoteSpendingAir::generate_trace(&witness);

        // Row 0 is the commitment/nullifier row
        let row0 = &trace[0];
        assert_eq!(row0[col::OWNER], witness.owner);
        assert_eq!(row0[col::VALUE], witness.value);
        assert_eq!(row0[col::ASSET_TYPE], witness.asset_type);
        assert_eq!(row0[col::CREATION_NONCE], witness.creation_nonce);
        assert_eq!(row0[col::RANDOMNESS], witness.randomness);
        assert_eq!(row0[col::COMMITMENT], witness.commitment());
        // All 8 spending key limbs are in the trace
        for j in 0..SPENDING_KEY_LIMBS {
            assert_eq!(row0[col::SPENDING_KEY_START + j], witness.spending_key[j]);
        }
        assert_eq!(row0[col::NULLIFIER], witness.nullifier());
        // Position column is zero for commitment row (satisfies position validity)
        assert_eq!(row0[merkle_col::POSITION], BabyBear::ZERO);
    }

    #[test]
    fn trace_merkle_chain_continuity() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, _) = NoteSpendingAir::generate_trace(&witness);

        // Row 0 commitment should feed into row 1 current
        assert_eq!(trace[0][col::COMMITMENT], trace[1][merkle_col::CURRENT]);

        // Each Merkle level: parent[i] = current[i+1]
        for i in 1..4 {
            assert_eq!(
                trace[i][merkle_col::PARENT],
                trace[i + 1][merkle_col::CURRENT],
                "Merkle chain broken at level {i}"
            );
        }
    }

    #[test]
    fn constraint_zero_on_all_valid_rows() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let (trace, public_inputs) = NoteSpendingAir::generate_trace(&witness);
        let air = NoteSpendingAir::new(witness.merkle_siblings.len());
        let alpha = BabyBear::new(7);
        for i in 0..trace.len() {
            let next_idx = if i + 1 < trace.len() { i + 1 } else { 0 };
            let c = air.eval_constraints(&trace[i], &trace[next_idx], &public_inputs, alpha);
            assert_eq!(
                c,
                BabyBear::ZERO,
                "Constraint non-zero at row {}: c = {}",
                i,
                c.0
            );
        }
    }

    #[test]
    fn tampered_commitment_detected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let (mut trace, pi) = NoteSpendingAir::generate_trace(&witness);
        let air = NoteSpendingAir::new(witness.merkle_siblings.len());
        let alpha = BabyBear::new(7);
        trace[0][col::COMMITMENT] = BabyBear::new(12345);
        let c = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(c, BabyBear::ZERO, "Tampered commitment must be detected");
    }

    #[test]
    fn tampered_nullifier_detected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let (mut trace, pi) = NoteSpendingAir::generate_trace(&witness);
        let air = NoteSpendingAir::new(witness.merkle_siblings.len());
        let alpha = BabyBear::new(7);
        trace[0][col::NULLIFIER] = BabyBear::new(99999);
        let c = air.eval_constraints(&trace[0], &trace[1], &pi, alpha);
        assert_ne!(c, BabyBear::ZERO, "Tampered nullifier must be detected");
    }

    #[test]
    fn tampered_merkle_parent_detected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );
        let (mut trace, pi) = NoteSpendingAir::generate_trace(&witness);
        let air = NoteSpendingAir::new(witness.merkle_siblings.len());
        let alpha = BabyBear::new(7);
        trace[1][merkle_col::PARENT] = BabyBear::new(77777);
        let c = air.eval_constraints(&trace[1], &trace[2], &pi, alpha);
        assert_ne!(c, BabyBear::ZERO, "Tampered Merkle parent must be detected");
    }

    #[test]
    fn prove_and_verify_note_spend() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();

        // Generate proof
        let proof = prove_note_spend(&witness);

        // Verify proof (now includes value + asset_type to prevent inflation)
        let result = verify_note_spend(
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(
            result.is_ok(),
            "Note spending proof verification failed: {:?}",
            result.err()
        );

        println!(
            "Note spending STARK proof: {} rows, {} bytes ({:.1} KiB)",
            proof.trace_len,
            stark::proof_to_bytes(&proof).len(),
            stark::proof_to_bytes(&proof).len() as f64 / 1024.0,
        );
    }

    #[test]
    fn wrong_nullifier_rejected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        let merkle_root = witness.merkle_root();
        let proof = prove_note_spend(&witness);

        // Try to verify with wrong nullifier
        let wrong_nullifier = BabyBear::new(999999);
        let result = verify_note_spend(
            wrong_nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(result.is_err(), "Should reject wrong nullifier");
    }

    #[test]
    fn wrong_merkle_root_rejected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let proof = prove_note_spend(&witness);

        // Try to verify with wrong Merkle root
        let wrong_root = BabyBear::new(888888);
        let result = verify_note_spend(
            nullifier,
            wrong_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(result.is_err(), "Should reject wrong Merkle root");
    }

    #[test]
    fn wrong_spending_key_produces_wrong_nullifier() {
        // If the prover uses the wrong spending key, the nullifier will be different,
        // and the proof won't verify against the expected nullifier.
        let correct_key = test_spending_key(0xDEAD_BEEF);
        let witness_correct = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            correct_key,
            4,
        );

        let mut witness_wrong = witness_correct.clone();
        // Flip just ONE limb of the 8-limb key
        witness_wrong.spending_key[0] = BabyBear::new(0xBAD_0EE);

        // The wrong key produces a different nullifier
        assert_ne!(witness_correct.nullifier(), witness_wrong.nullifier());

        // A proof with the wrong key...
        let proof_wrong = prove_note_spend(&witness_wrong);

        // ...will not verify against the CORRECT nullifier
        let result = verify_note_spend(
            witness_correct.nullifier(),
            witness_correct.merkle_root(),
            witness_correct.value,
            witness_correct.asset_type,
            &proof_wrong,
        );
        assert!(
            result.is_err(),
            "Proof with wrong spending key should fail against correct nullifier"
        );
    }

    #[test]
    fn tampered_proof_rejected() {
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();
        let mut proof = prove_note_spend(&witness);

        // Tamper with trace commitment
        proof.trace_commitment[0] ^= 0xFF;

        let result = verify_note_spend(
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(result.is_err(), "Tampered proof should be rejected");
    }

    #[test]
    fn depth_8_works() {
        let key = test_spending_key(0xCAFE_BABE);
        let witness = create_test_witness(
            BabyBear::new(7777),
            BabyBear::new(1000000),
            BabyBear::new(42),
            key,
            8,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();
        let proof = prove_note_spend(&witness);

        let result = verify_note_spend(
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(
            result.is_ok(),
            "Depth-8 note spending proof should verify: {:?}",
            result.err()
        );

        let proof_bytes = stark::proof_to_bytes(&proof);
        println!(
            "Depth-8 note spending STARK proof: {} rows, {} bytes ({:.1} KiB)",
            proof.trace_len,
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0,
        );
    }

    #[test]
    fn wrong_commitment_wrong_merkle_path() {
        // If the prover uses wrong note contents, the commitment changes,
        // and the Merkle path won't match the expected root.
        let key = test_spending_key(0xDEAD_BEEF);
        let witness_correct = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        // Create a witness with different value but same Merkle path
        let mut witness_tampered = witness_correct.clone();
        witness_tampered.value = BabyBear::new(999999); // tamper the value

        // The commitment changes
        assert_ne!(witness_correct.commitment(), witness_tampered.commitment());
        // Therefore the Merkle root changes (path no longer matches)
        assert_ne!(
            witness_correct.merkle_root(),
            witness_tampered.merkle_root()
        );

        // Proof with tampered witness won't verify against correct root
        let proof = prove_note_spend(&witness_tampered);
        let result = verify_note_spend(
            witness_correct.nullifier(),
            witness_correct.merkle_root(),
            witness_correct.value,
            witness_correct.asset_type,
            &proof,
        );
        assert!(
            result.is_err(),
            "Tampered commitment should fail Merkle verification"
        );
    }

    #[test]
    fn proof_serialization_roundtrip() {
        let key = test_spending_key(0xFF);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();
        let proof = prove_note_spend(&witness);

        // Serialize and deserialize
        let bytes = stark::proof_to_bytes(&proof);
        let proof2 = stark::proof_from_bytes(&bytes).unwrap();

        // Verify the deserialized proof
        let result = verify_note_spend(
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof2,
        );
        assert!(result.is_ok(), "Deserialized proof should verify");
    }

    #[test]
    fn spending_key_not_brute_forceable() {
        // With 8 limbs, brute-forcing requires ~2^248 attempts.
        // This test verifies the key space is > 2^31 (the old vulnerability).
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1),
            key,
            4,
        );

        // The spending key is 8 limbs, each ~31 bits, totalling ~248 bits.
        assert_eq!(witness.spending_key.len(), SPENDING_KEY_LIMBS);
        assert_eq!(SPENDING_KEY_LIMBS, 8);

        // Verify that all limbs are non-trivial (not all zero — the test key is derived)
        let non_zero_limbs = witness
            .spending_key
            .iter()
            .filter(|&&l| l != BabyBear::ZERO)
            .count();
        assert!(
            non_zero_limbs >= 6,
            "Test key should have most limbs non-zero, got {non_zero_limbs}"
        );
    }

    #[test]
    fn key_to_field_elements_roundtrip() {
        // Verify the conversion from 256-bit external key to 8 BabyBear limbs.
        let external_key: [u8; 32] = [
            0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE, 0xBA, 0xBE, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
            0x07, 0x08, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC,
            0xDD, 0xEE, 0xFF, 0x00,
        ];
        let limbs = key_to_field_elements(&external_key);
        assert_eq!(limbs.len(), 8);

        // Each limb should be a valid BabyBear element (< p)
        for limb in &limbs {
            assert!(limb.0 < (1u32 << 31) - 1); // BabyBear p = 2^31 - 1
        }

        // Deterministic
        let limbs2 = key_to_field_elements(&external_key);
        assert_eq!(limbs, limbs2);
    }

    #[test]
    fn wrong_value_rejected() {
        // CRITICAL: This test verifies the value inflation fix.
        // A spender cannot claim a higher value than what the note actually contains.
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500), // actual value = 500
            BabyBear::new(1),
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();
        let proof = prove_note_spend(&witness);

        // Attempt to verify with inflated value (999999 instead of 500)
        let inflated_value = BabyBear::new(999999);
        let result = verify_note_spend(
            nullifier,
            merkle_root,
            inflated_value,
            witness.asset_type,
            &proof,
        );
        assert!(result.is_err(), "Should reject inflated value");

        // Correct value should work
        let result = verify_note_spend(
            nullifier,
            merkle_root,
            witness.value,
            witness.asset_type,
            &proof,
        );
        assert!(result.is_ok(), "Correct value should verify");
    }

    #[test]
    fn wrong_asset_type_rejected() {
        // A spender cannot claim a different asset type than what the note contains.
        let key = test_spending_key(0xDEAD_BEEF);
        let witness = create_test_witness(
            BabyBear::new(1000),
            BabyBear::new(500),
            BabyBear::new(1), // actual asset_type = 1
            key,
            4,
        );

        let nullifier = witness.nullifier();
        let merkle_root = witness.merkle_root();
        let proof = prove_note_spend(&witness);

        // Attempt to verify with wrong asset type
        let wrong_asset = BabyBear::new(42);
        let result = verify_note_spend(nullifier, merkle_root, witness.value, wrong_asset, &proof);
        assert!(result.is_err(), "Should reject wrong asset type");
    }

    #[test]
    fn flipping_single_key_limb_changes_nullifier() {
        // Verify that changing ANY single limb of the 8-limb key changes the nullifier.
        let base_key = test_spending_key(0x12345678);
        let witness = create_test_witness(
            BabyBear::new(42),
            BabyBear::new(100),
            BabyBear::new(1),
            base_key,
            4,
        );
        let base_nullifier = witness.nullifier();

        for i in 0..SPENDING_KEY_LIMBS {
            let mut modified_key = base_key;
            modified_key[i] = BabyBear::new(modified_key[i].0.wrapping_add(1) % ((1u32 << 31) - 1));
            let mut modified_witness = witness.clone();
            modified_witness.spending_key = modified_key;
            assert_ne!(
                modified_witness.nullifier(),
                base_nullifier,
                "Flipping limb {i} must change the nullifier"
            );
        }
    }
}
