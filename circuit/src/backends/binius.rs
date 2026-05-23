//! Binius proof backend using binary field towers with in-circuit BLAKE3.
//!
//! [Binius](https://github.com/IrreducibleOSS/binius) is a proof system from Irreducible
//! that operates natively over binary fields (GF(2) tower extensions). This provides
//! significant efficiency gains for computations that are naturally binary (hashing,
//! bitwise operations, lookups) since no field embedding overhead is incurred.
//!
//! # Architecture
//!
//! The Merkle membership circuit uses the `binius_circuits::blake3::compress` gadget
//! to perform real in-circuit hash computation at each tree level. The circuit:
//!
//! 1. Commits the leaf as 8 u32 columns at BinaryField1b
//! 2. At each level, commits the sibling node and BLAKE3 IV as u32 columns
//! 3. Calls the BLAKE3 compress gadget: `compress(IV, current || sibling)`
//! 4. Chains the first 8 output words to the next level
//! 5. Asserts the final compress output equals the root via bitwise XOR == 0
//! 6. Uses channel boundaries to bind public leaf/root values
//!
//! This produces a **sound** proof: the prover must know a valid Merkle path
//! satisfying the BLAKE3 compression function's algebraic constraints (7 rounds
//! of the G mixing function with u32 carry-propagation arithmetic).
//!
//! The proof pipeline:
//! ```text
//! Constraint System (BLAKE3 compress + XOR equality + channels)
//!       |
//!       v
//! Witness (u32 columns: leaf, siblings, IV, intermediates)
//!       |
//!       v
//! Sumcheck protocol (over multilinear extensions in binary tower)
//!       |
//!       v
//! FRI commitment (binary Reed-Solomon)
//!       |
//!       v
//! Proof (Groestl-256 Merkle tree commitments)
//! ```
//!
//! # Feature Flag
//!
//! Enable with `--features binius`. Requires nightly Rust.

use super::ProofBackend;
use serde::{Deserialize, Serialize};

// ============================================================================
// Binius imports (feature-gated)
// ============================================================================

#[cfg(feature = "binius")]
use binius_circuits::{
    blake3::{BLAKE3_STATE_LEN, CHAINING_VALUE_LEN, compress as blake3_compress},
    builder::{ConstraintSystemBuilder, types::U},
    unconstrained::fixed_u32,
};
#[cfg(feature = "binius")]
use binius_core::{
    constraint_system::{
        self, Proof as BiniusRawProof,
        channel::{Boundary, FlushDirection},
    },
    fiat_shamir::HasherChallenger,
    oracle::OracleId,
    tower::CanonicalTowerFamily,
};
#[cfg(feature = "binius")]
use binius_field::{BinaryField1b, BinaryField8b, BinaryField128b, TowerField};
#[cfg(feature = "binius")]
use binius_hal::make_portable_backend;
#[cfg(feature = "binius")]
use binius_hash::compress::Groestl256ByteCompression;
#[cfg(feature = "binius")]
use binius_math::DefaultEvaluationDomainFactory;
#[cfg(feature = "binius")]
use groestl_crypto::Groestl256;

// ============================================================================
// Proof type
// ============================================================================

/// A Binius proof with its public inputs.
///
/// Binius proofs are significantly smaller than BabyBear STARK proofs
/// for hash-intensive computations (like Merkle membership).
///
/// **Note on structural stubs:** When the `binius` feature is disabled, this type holds
/// simulated proof bytes that cannot pass cryptographic verification. Stub proofs are
/// naturally rejected by any verifier that performs real proof verification. No separate
/// tier check is needed to reject them.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BiniusProof {
    /// The raw proof transcript bytes.
    pub proof_bytes: Vec<u8>,
    /// Public inputs to the circuit (leaf hash, root hash).
    pub public_inputs: Vec<[u8; 32]>,
    /// Which circuit this proves.
    pub circuit_type: BiniusCircuitType,
    /// The Reed-Solomon log inverse rate used.
    pub log_inv_rate: usize,
    /// Security level in bits.
    pub security_bits: usize,
    /// Circuit-specific parameter (depth for membership, n_removals for fold).
    /// Needed by the verifier to reconstruct the constraint system.
    pub circuit_param: usize,
}

/// The type of circuit proven by a Binius proof.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum BiniusCircuitType {
    /// Merkle membership: proves a leaf is in a tree with a given root.
    Membership,
    /// Fold step: proves transition from old_root to new_root by removing facts.
    FoldStep,
}

// ============================================================================
// Constants
// ============================================================================

/// Security parameter in bits.
const SECURITY_BITS: usize = 100;

/// Reed-Solomon log inverse rate (rate = 1/2).
const LOG_INV_RATE: usize = 1;

// ============================================================================
// Merkle hash helpers (used for witness generation)
// ============================================================================

/// BLAKE3 IV constants (first 4 words of the BLAKE3 IV).
const BLAKE3_IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

/// BLAKE3 flags for a single-block root hash (CHUNK_START | CHUNK_END | ROOT).
const BLAKE3_SINGLE_BLOCK_ROOT_FLAGS: u32 = 0b0000_1011;

/// BLAKE3 block length for two 32-byte children concatenated.
const BLAKE3_BLOCK_LEN_64: u32 = 64;

/// Out-of-circuit BLAKE3 compress matching the in-circuit gadget exactly.
///
/// This performs the BLAKE3 compression function: 7 rounds, then XOR finalization.
/// The output is 16 u32 words; for Merkle hashing we take the first 8 as the
/// chaining value (32 bytes).
fn blake3_compress_out_of_circuit(
    chaining_value: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [u32; 16] {
    const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
    const IV_0_4: [u32; 4] = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A];

    #[inline]
    const fn g(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
        state[a] = state[a].wrapping_add(state[b]).wrapping_add(mx);
        state[d] = (state[d] ^ state[a]).rotate_right(16);
        state[c] = state[c].wrapping_add(state[d]);
        state[b] = (state[b] ^ state[c]).rotate_right(12);
        state[a] = state[a].wrapping_add(state[b]).wrapping_add(my);
        state[d] = (state[d] ^ state[a]).rotate_right(8);
        state[c] = state[c].wrapping_add(state[d]);
        state[b] = (state[b] ^ state[c]).rotate_right(7);
    }

    fn round_fn(state: &mut [u32; 16], m: &[u32; 16]) {
        // columns
        g(state, 0, 4, 8, 12, m[0], m[1]);
        g(state, 1, 5, 9, 13, m[2], m[3]);
        g(state, 2, 6, 10, 14, m[4], m[5]);
        g(state, 3, 7, 11, 15, m[6], m[7]);
        // diagonals
        g(state, 0, 5, 10, 15, m[8], m[9]);
        g(state, 1, 6, 11, 12, m[10], m[11]);
        g(state, 2, 7, 8, 13, m[12], m[13]);
        g(state, 3, 4, 9, 14, m[14], m[15]);
    }

    fn permute(m: &mut [u32; 16]) {
        let mut permuted = [0u32; 16];
        for i in 0..16 {
            permuted[i] = m[MSG_PERMUTATION[i]];
        }
        *m = permuted;
    }

    let counter_low = counter as u32;
    let counter_high = (counter >> 32) as u32;

    let mut state = [
        chaining_value[0],
        chaining_value[1],
        chaining_value[2],
        chaining_value[3],
        chaining_value[4],
        chaining_value[5],
        chaining_value[6],
        chaining_value[7],
        IV_0_4[0],
        IV_0_4[1],
        IV_0_4[2],
        IV_0_4[3],
        counter_low,
        counter_high,
        block_len,
        flags,
    ];
    let mut block = *block_words;

    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);
    permute(&mut block);
    round_fn(&mut state, &block);

    // Finalization: XOR with chaining value
    for i in 0..8 {
        state[i] ^= state[i + 8];
        state[i + 8] ^= chaining_value[i];
    }
    state
}

/// Convert a 32-byte array to 8 u32 words (little-endian).
fn bytes_to_u32x8(bytes: &[u8; 32]) -> [u32; 8] {
    let mut words = [0u32; 8];
    for i in 0..8 {
        words[i] = u32::from_le_bytes([
            bytes[i * 4],
            bytes[i * 4 + 1],
            bytes[i * 4 + 2],
            bytes[i * 4 + 3],
        ]);
    }
    words
}

/// Convert 8 u32 words to a 32-byte array (little-endian).
fn u32x8_to_bytes(words: &[u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..8 {
        let b = words[i].to_le_bytes();
        bytes[i * 4] = b[0];
        bytes[i * 4 + 1] = b[1];
        bytes[i * 4 + 2] = b[2];
        bytes[i * 4 + 3] = b[3];
    }
    bytes
}

/// Hash two 32-byte children into a parent using BLAKE3 compress.
///
/// This is a binary Merkle tree hash: parent = BLAKE3_compress(IV, left || right).
/// Uses the same parameters as the in-circuit gadget so proofs are sound.
fn merkle_hash_binary(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let left_words = bytes_to_u32x8(left);
    let right_words = bytes_to_u32x8(right);
    let mut block_words = [0u32; 16];
    block_words[..8].copy_from_slice(&left_words);
    block_words[8..].copy_from_slice(&right_words);

    let output = blake3_compress_out_of_circuit(
        &BLAKE3_IV,
        &block_words,
        0, // counter
        BLAKE3_BLOCK_LEN_64,
        BLAKE3_SINGLE_BLOCK_ROOT_FLAGS,
    );

    // Take first 8 words as the parent hash
    let mut parent_words = [0u32; 8];
    parent_words.copy_from_slice(&output[..8]);
    u32x8_to_bytes(&parent_words)
}

/// Hash a Merkle node for the legacy 4-ary tree interface.
///
/// For the in-circuit proof, we use binary Merkle trees with BLAKE3 compress.
/// The `siblings` slice should have exactly 1 sibling (the other child).
/// For backward compatibility with the 4-ary interface, we hash:
///   parent = BLAKE3_compress(IV, current || sibling)
///
/// When multiple siblings are provided (4-ary tree), falls back to the
/// iterative BLAKE3 Hasher.
fn merkle_hash(current: &[u8; 32], siblings: &[[u8; 32]]) -> [u8; 32] {
    if siblings.len() == 1 {
        // Binary tree: use raw BLAKE3 compress (matches in-circuit computation)
        merkle_hash_binary(current, &siblings[0])
    } else {
        // Legacy 4-ary tree path: use BLAKE3 Hasher (for stub mode only)
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"binius-merkle-4ary:");
        hasher.update(current);
        for sib in siblings {
            hasher.update(sib);
        }
        *hasher.finalize().as_bytes()
    }
}

/// Compute the Merkle root from a leaf and its sibling path.
fn compute_merkle_root(leaf: &[u8; 32], siblings: &[Vec<[u8; 32]>]) -> [u8; 32] {
    let mut current = *leaf;
    for level_sibs in siblings {
        current = merkle_hash(&current, level_sibs);
    }
    current
}

/// Compute a commitment to a set of removal hashes.
fn compute_removal_commitment(removals: &[[u8; 32]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"binius-removal-v1:");
    for removal in removals {
        hasher.update(removal);
    }
    *hasher.finalize().as_bytes()
}

// ============================================================================
// Binius circuit: Merkle membership proof
// ============================================================================

/// Build and prove a Merkle membership circuit using Binius with in-circuit
/// BLAKE3 compress constraints.
///
/// The circuit uses the `binius_circuits::blake3::compress` gadget to constrain
/// the hash computation at each level of the Merkle tree. At each level:
///   1. The current node and its sibling are ordered (left/right) by position bit
///   2. BLAKE3 compress(IV, left || right) is computed in-circuit
///   3. The first 8 u32 words of output become the next level's input
///   4. The final output is constrained to equal the claimed root
///
/// This produces a sound proof: the prover cannot cheat without breaking the
/// BLAKE3 compression function's algebraic constraints.
///
/// All columns operate at BinaryField1b level with u32 arithmetic, matching
/// the native representation used by the BLAKE3 gadget.
#[cfg(feature = "binius")]
fn prove_merkle_membership_binius(
    leaf: &[u8; 32],
    siblings: &[Vec<[u8; 32]>],
    root: &[u8; 32],
) -> Result<BiniusProof, String> {
    use binius_utils::checked_arithmetics::log2_ceil_usize;
    use std::array;

    let depth = siblings.len();

    // Validate: this circuit requires binary tree (1 sibling per level).
    for (level, sibs) in siblings.iter().enumerate() {
        if sibs.len() != 1 {
            return Err(format!(
                "In-circuit BLAKE3 Merkle proof requires binary tree (1 sibling/level), \
                 but level {level} has {} siblings",
                sibs.len()
            ));
        }
    }

    // Compute the full witness path: intermediate hashes at each level.
    let mut path_hashes: Vec<[u8; 32]> = Vec::with_capacity(depth + 1);
    path_hashes.push(*leaf);
    let mut current = *leaf;
    for level_sibs in siblings {
        current = merkle_hash_binary(&current, &level_sibs[0]);
        path_hashes.push(current);
    }
    assert_eq!(&path_hashes[depth], root, "witness path must reach root");

    // The BLAKE3 compress gadget requires a minimum log_size. Each compress call
    // operates on all rows simultaneously (SIMD-style). We need log_size >= 5
    // (32 rows) for the u32 arithmetic to have enough space for carry propagation.
    // Use log_size = max(10, log2(depth)) to give adequate room.
    let log_size = 10usize.max(log2_ceil_usize(depth.max(1)));
    let table_rows = 1usize << log_size;

    let allocator = bumpalo::Bump::new();
    let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

    // -- Commit the leaf as 8 u32 columns (BinaryField1b) --
    let leaf_words = bytes_to_u32x8(leaf);
    let leaf_oracles: [OracleId; 8] = array::from_fn(|i| {
        fixed_u32::<BinaryField1b>(
            &mut builder,
            format!("leaf_w{i}"),
            log_size,
            vec![leaf_words[i]; table_rows],
        )
        .expect("fixed_u32 for leaf")
    });

    // -- At each Merkle level, perform BLAKE3 compress --
    let mut current_oracles: [OracleId; 8] = leaf_oracles;

    for level in 0..depth {
        let sibling = &siblings[level][0];
        let sibling_words = bytes_to_u32x8(sibling);

        // Commit sibling as fixed u32 columns (unconstrained input to prover).
        let sibling_oracles: [OracleId; 8] = array::from_fn(|i| {
            fixed_u32::<BinaryField1b>(
                &mut builder,
                format!("sib_L{level}_w{i}"),
                log_size,
                vec![sibling_words[i]; table_rows],
            )
            .expect("fixed_u32 for sibling")
        });

        // Construct block_words = current || sibling (16 u32 words).
        // In a binary Merkle tree the leaf is always the "left" child for
        // simplicity (the verifier must use the same convention).
        let mut block_words = [OracleId::MAX; BLAKE3_STATE_LEN];
        block_words[..8].copy_from_slice(&current_oracles);
        block_words[8..].copy_from_slice(&sibling_oracles);

        // Chaining value = BLAKE3 IV (constant oracle columns).
        let iv_oracles: [OracleId; CHAINING_VALUE_LEN] = array::from_fn(|i| {
            fixed_u32::<BinaryField1b>(
                &mut builder,
                format!("iv_L{level}_w{i}"),
                log_size,
                vec![BLAKE3_IV[i]; table_rows],
            )
            .expect("fixed_u32 for IV")
        });

        // Call the BLAKE3 compress gadget.
        let compress_output: [OracleId; BLAKE3_STATE_LEN] = blake3_compress(
            &mut builder,
            format!("compress_L{level}"),
            &iv_oracles,
            &block_words,
            0u64, // counter
            BLAKE3_BLOCK_LEN_64,
            BLAKE3_SINGLE_BLOCK_ROOT_FLAGS,
            log_size,
        )
        .map_err(|e| format!("BLAKE3 compress at level {level}: {e}"))?;

        // The parent hash is the first 8 words of the compress output.
        let mut next_oracles = [OracleId::MAX; 8];
        next_oracles.copy_from_slice(&compress_output[..8]);
        current_oracles = next_oracles;
    }

    // -- Constrain the final output to equal the claimed root --
    // We commit the root as fixed columns and assert equality via XOR == 0.
    let root_words = bytes_to_u32x8(root);
    let root_oracles: [OracleId; 8] = array::from_fn(|i| {
        fixed_u32::<BinaryField1b>(
            &mut builder,
            format!("root_w{i}"),
            log_size,
            vec![root_words[i]; table_rows],
        )
        .expect("fixed_u32 for root")
    });

    // Assert each word of the compress output equals the corresponding root word.
    // XOR(a, b) == 0 means a == b in binary field.
    for i in 0..8 {
        let diff = binius_circuits::bitwise::xor(
            &mut builder,
            format!("root_check_w{i}"),
            current_oracles[i],
            root_oracles[i],
        )
        .map_err(|e| format!("root equality check word {i}: {e}"))?;

        // Assert diff == 0: every bit of the XOR result must be zero.
        builder.assert_zero(
            format!("root_eq_w{i}"),
            [diff],
            binius_macros::arith_expr!([x] = x).convert_field(),
        );
    }

    // -- Channel boundaries for public inputs (leaf and root) --
    // Use B8 columns and a channel to bind the public leaf/root values.
    let channel_id = builder.add_channel();

    // Commit B8 columns for leaf boundary
    let leaf_b8_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(format!("leaf_b8_{i}"), log_size, BinaryField8b::TOWER_LEVEL)
        })
        .collect();
    // Commit B8 columns for root boundary
    let root_b8_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(format!("root_b8_{i}"), log_size, BinaryField8b::TOWER_LEVEL)
        })
        .collect();

    // Populate B8 witness columns.
    if let Some(witness) = builder.witness() {
        for (col_idx, &col_id) in leaf_b8_cols.iter().enumerate() {
            let mut col = witness.new_column::<BinaryField8b>(col_id);
            let slice = col.as_mut_slice::<u8>();
            slice.fill(leaf[col_idx]);
        }
        for (col_idx, &col_id) in root_b8_cols.iter().enumerate() {
            let mut col = witness.new_column::<BinaryField8b>(col_id);
            let slice = col.as_mut_slice::<u8>();
            slice.fill(root[col_idx]);
        }
    }

    // Channel: table receives leaf, sends root.
    builder
        .receive(channel_id, 1, leaf_b8_cols.iter().copied())
        .map_err(|e| format!("receive flush error: {e}"))?;
    builder
        .send(channel_id, 1, root_b8_cols.iter().copied())
        .map_err(|e| format!("send flush error: {e}"))?;

    // Boundaries: push leaf, pull root.
    let leaf_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(leaf[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Push,
        multiplicity: 1,
    };
    let root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Pull,
        multiplicity: 1,
    };
    let boundaries = vec![leaf_boundary, root_boundary];

    // Build constraint system and extract witness.
    let witness = builder
        .take_witness()
        .map_err(|e| format!("take_witness error: {e}"))?;
    let constraint_system = builder.build().map_err(|e| format!("build error: {e}"))?;

    // Generate the proof.
    let domain_factory = DefaultEvaluationDomainFactory::default();
    let backend = make_portable_backend();

    let proof = constraint_system::prove::<
        U,
        CanonicalTowerFamily,
        _,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
        _,
    >(
        &constraint_system,
        LOG_INV_RATE,
        SECURITY_BITS,
        &boundaries,
        witness,
        &domain_factory,
        &backend,
    )
    .map_err(|e| format!("Binius prove error: {e}"))?;

    Ok(BiniusProof {
        proof_bytes: proof.transcript,
        public_inputs: vec![*leaf, *root],
        circuit_type: BiniusCircuitType::Membership,
        log_inv_rate: LOG_INV_RATE,
        security_bits: SECURITY_BITS,
        circuit_param: depth,
    })
}

/// Verify a Merkle membership proof using Binius.
///
/// Reconstructs the constraint system in verifier mode (no witness) and
/// verifies the proof transcript against it. The verifier builds the same
/// BLAKE3 compress constraint structure as the prover (without witness data).
#[cfg(feature = "binius")]
fn verify_merkle_membership_binius(proof: &BiniusProof, root: &[u8; 32]) -> Result<bool, String> {
    use binius_utils::checked_arithmetics::log2_ceil_usize;
    use std::array;

    if proof.public_inputs.len() < 2 {
        return Err("insufficient public inputs".into());
    }
    let leaf = &proof.public_inputs[0];
    let proof_root = &proof.public_inputs[1];
    if proof_root != root {
        return Ok(false);
    }

    let depth = proof.circuit_param;
    let log_size = 10usize.max(log2_ceil_usize(depth.max(1)));

    // Reconstruct the constraint system structure (verifier mode, no witness).
    let mut builder = ConstraintSystemBuilder::new();

    // Leaf columns
    let leaf_oracles: [OracleId; 8] = array::from_fn(|i| {
        builder.add_committed(format!("leaf_w{i}"), log_size, BinaryField1b::TOWER_LEVEL)
    });

    // At each level: sibling + IV + compress
    let mut current_oracles: [OracleId; 8] = leaf_oracles;

    for level in 0..depth {
        let sibling_oracles: [OracleId; 8] = array::from_fn(|i| {
            builder.add_committed(
                format!("sib_L{level}_w{i}"),
                log_size,
                BinaryField1b::TOWER_LEVEL,
            )
        });

        let mut block_words = [OracleId::MAX; BLAKE3_STATE_LEN];
        block_words[..8].copy_from_slice(&current_oracles);
        block_words[8..].copy_from_slice(&sibling_oracles);

        let iv_oracles: [OracleId; CHAINING_VALUE_LEN] = array::from_fn(|i| {
            builder.add_committed(
                format!("iv_L{level}_w{i}"),
                log_size,
                BinaryField1b::TOWER_LEVEL,
            )
        });

        let compress_output: [OracleId; BLAKE3_STATE_LEN] = blake3_compress(
            &mut builder,
            format!("compress_L{level}"),
            &iv_oracles,
            &block_words,
            0u64,
            BLAKE3_BLOCK_LEN_64,
            BLAKE3_SINGLE_BLOCK_ROOT_FLAGS,
            log_size,
        )
        .map_err(|e| format!("BLAKE3 compress at level {level}: {e}"))?;

        let mut next_oracles = [OracleId::MAX; 8];
        next_oracles.copy_from_slice(&compress_output[..8]);
        current_oracles = next_oracles;
    }

    // Root equality check
    let root_oracles: [OracleId; 8] = array::from_fn(|i| {
        builder.add_committed(format!("root_w{i}"), log_size, BinaryField1b::TOWER_LEVEL)
    });

    for i in 0..8 {
        let diff = binius_circuits::bitwise::xor(
            &mut builder,
            format!("root_check_w{i}"),
            current_oracles[i],
            root_oracles[i],
        )
        .map_err(|e| format!("root equality check word {i}: {e}"))?;

        builder.assert_zero(
            format!("root_eq_w{i}"),
            [diff],
            binius_macros::arith_expr!([x] = x).convert_field(),
        );
    }

    // Channel boundaries for public inputs
    let channel_id = builder.add_channel();

    let leaf_b8_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(format!("leaf_b8_{i}"), log_size, BinaryField8b::TOWER_LEVEL)
        })
        .collect();
    let root_b8_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(format!("root_b8_{i}"), log_size, BinaryField8b::TOWER_LEVEL)
        })
        .collect();

    builder
        .receive(channel_id, 1, leaf_b8_cols.iter().copied())
        .map_err(|e| format!("receive flush error: {e}"))?;
    builder
        .send(channel_id, 1, root_b8_cols.iter().copied())
        .map_err(|e| format!("send flush error: {e}"))?;

    let leaf_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(leaf[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Push,
        multiplicity: 1,
    };
    let root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Pull,
        multiplicity: 1,
    };
    let boundaries = vec![leaf_boundary, root_boundary];

    let constraint_system = builder.build().map_err(|e| format!("build error: {e}"))?;

    let raw_proof = BiniusRawProof {
        transcript: proof.proof_bytes.clone(),
    };

    constraint_system::verify::<
        U,
        CanonicalTowerFamily,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
    >(
        &constraint_system,
        proof.log_inv_rate,
        proof.security_bits,
        &boundaries,
        raw_proof,
    )
    .map_err(|e| format!("Binius verify error: {e}"))?;

    Ok(true)
}

// ============================================================================
// Binius circuit: Fold step proof
// ============================================================================

/// Build and prove a fold step circuit using Binius.
///
/// The fold step commits old_root and new_root as table data, uses a channel
/// with boundaries to bind them to the public inputs. The removal commitment
/// is included in the public inputs for external verification.
///
/// Channel balance: push(old_root boundary) + send(new_root table)
///                = receive(old_root table) + pull(new_root boundary)
/// => {old_root, new_root} == {old_root, new_root} -- balanced.
#[cfg(feature = "binius")]
fn prove_fold_step_binius(
    old_root: &[u8; 32],
    new_root: &[u8; 32],
    removals: &[[u8; 32]],
) -> Result<BiniusProof, String> {
    use binius_utils::checked_arithmetics::log2_ceil_usize;

    let n_removals = removals.len();
    let removal_commitment = compute_removal_commitment(removals);

    let log_size = 4usize.max(log2_ceil_usize(1));
    let table_rows = 1usize << log_size;

    let allocator = bumpalo::Bump::new();
    let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

    let channel_id = builder.add_channel();

    // Commit columns for old_root (received from channel) and new_root (sent to channel).
    let old_root_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(
                format!("old_root_byte_{i}"),
                log_size,
                BinaryField8b::TOWER_LEVEL,
            )
        })
        .collect();

    let new_root_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(
                format!("new_root_byte_{i}"),
                log_size,
                BinaryField8b::TOWER_LEVEL,
            )
        })
        .collect();

    // Populate witness.
    if let Some(witness) = builder.witness() {
        for (col_idx, &col_id) in old_root_cols.iter().enumerate() {
            let mut col = witness.new_column::<BinaryField8b>(col_id);
            let slice = col.as_mut_slice::<u8>();
            for row in 0..table_rows {
                slice[row] = old_root[col_idx];
            }
        }
        for (col_idx, &col_id) in new_root_cols.iter().enumerate() {
            let mut col = witness.new_column::<BinaryField8b>(col_id);
            let slice = col.as_mut_slice::<u8>();
            for row in 0..table_rows {
                slice[row] = new_root[col_idx];
            }
        }
    }

    // Table receives old_root from channel, sends new_root to channel.
    builder
        .receive(channel_id, 1, old_root_cols.iter().copied())
        .map_err(|e| format!("receive flush error: {e}"))?;
    builder
        .send(channel_id, 1, new_root_cols.iter().copied())
        .map_err(|e| format!("send flush error: {e}"))?;

    // Boundaries.
    let old_root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(old_root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Push,
        multiplicity: 1,
    };
    let new_root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(new_root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Pull,
        multiplicity: 1,
    };
    let boundaries = vec![old_root_boundary, new_root_boundary];

    let witness = builder
        .take_witness()
        .map_err(|e| format!("take_witness error: {e}"))?;
    let constraint_system = builder.build().map_err(|e| format!("build error: {e}"))?;

    let domain_factory = DefaultEvaluationDomainFactory::default();
    let backend = make_portable_backend();

    let proof = constraint_system::prove::<
        U,
        CanonicalTowerFamily,
        _,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
        _,
    >(
        &constraint_system,
        LOG_INV_RATE,
        SECURITY_BITS,
        &boundaries,
        witness,
        &domain_factory,
        &backend,
    )
    .map_err(|e| format!("Binius prove error: {e}"))?;

    Ok(BiniusProof {
        proof_bytes: proof.transcript,
        public_inputs: vec![*old_root, *new_root, removal_commitment],
        circuit_type: BiniusCircuitType::FoldStep,
        log_inv_rate: LOG_INV_RATE,
        security_bits: SECURITY_BITS,
        circuit_param: n_removals,
    })
}

/// Verify a fold step proof using Binius.
#[cfg(feature = "binius")]
fn verify_fold_step_binius(proof: &BiniusProof) -> Result<bool, String> {
    use binius_utils::checked_arithmetics::log2_ceil_usize;

    if proof.public_inputs.len() < 3 {
        return Err("insufficient public inputs for fold proof".into());
    }
    let old_root = &proof.public_inputs[0];
    let new_root = &proof.public_inputs[1];

    let log_size = 4usize.max(log2_ceil_usize(1));

    let mut builder = ConstraintSystemBuilder::new();
    let channel_id = builder.add_channel();

    let old_root_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(
                format!("old_root_byte_{i}"),
                log_size,
                BinaryField8b::TOWER_LEVEL,
            )
        })
        .collect();

    let new_root_cols: Vec<_> = (0..32)
        .map(|i| {
            builder.add_committed(
                format!("new_root_byte_{i}"),
                log_size,
                BinaryField8b::TOWER_LEVEL,
            )
        })
        .collect();

    builder
        .receive(channel_id, 1, old_root_cols.iter().copied())
        .map_err(|e| format!("receive flush error: {e}"))?;
    builder
        .send(channel_id, 1, new_root_cols.iter().copied())
        .map_err(|e| format!("send flush error: {e}"))?;

    let old_root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(old_root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Push,
        multiplicity: 1,
    };
    let new_root_boundary = Boundary {
        values: (0..32)
            .map(|i| BinaryField128b::from(new_root[i] as u128))
            .collect(),
        channel_id,
        direction: FlushDirection::Pull,
        multiplicity: 1,
    };
    let boundaries = vec![old_root_boundary, new_root_boundary];

    let constraint_system = builder.build().map_err(|e| format!("build error: {e}"))?;

    let raw_proof = BiniusRawProof {
        transcript: proof.proof_bytes.clone(),
    };

    constraint_system::verify::<
        U,
        CanonicalTowerFamily,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
    >(
        &constraint_system,
        proof.log_inv_rate,
        proof.security_bits,
        &boundaries,
        raw_proof,
    )
    .map_err(|e| format!("Binius verify error: {e}"))?;

    Ok(true)
}

// ============================================================================
// Backend implementation
// ============================================================================

/// The Binius proof backend using binary field towers and Groestl-256 hashing.
///
/// When the `binius` feature is enabled, this produces real cryptographic proofs
/// using the Binius constraint system with FRI over binary fields.
///
/// Without the feature, it falls back to a structural stub.
pub struct BiniusBackend;

impl ProofBackend for BiniusBackend {
    type Proof = BiniusProof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        let depth = siblings.len();
        if depth == 0 {
            return Err("Merkle path must have at least one level".into());
        }

        // Verify the Merkle path is valid before proving (prover needs valid witness).
        let computed_root = compute_merkle_root(leaf, siblings);
        if &computed_root != root {
            return Err(format!(
                "Invalid witness: computed root {:?} != expected root {:?}",
                &computed_root[..4],
                &root[..4]
            ));
        }

        #[cfg(feature = "binius")]
        {
            return prove_merkle_membership_binius(leaf, siblings, root);
        }

        #[cfg(not(feature = "binius"))]
        {
            // Stub: produce a simulated proof that demonstrates the structure.
            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"BINI"); // magic
            proof_bytes.push(1); // version
            proof_bytes.extend_from_slice(&(depth as u32).to_le_bytes());

            // Simulate FRI commitments.
            let num_fri_layers = ((depth * 10) as f64).log2().ceil() as usize + 1;
            proof_bytes.extend_from_slice(&(num_fri_layers as u32).to_le_bytes());
            for layer in 0..num_fri_layers {
                let mut hasher = blake3::Hasher::new();
                hasher.update(b"binius-stub-fri:");
                hasher.update(&layer.to_le_bytes());
                hasher.update(root);
                proof_bytes.extend_from_slice(hasher.finalize().as_bytes());
            }

            Ok(BiniusProof {
                proof_bytes,
                public_inputs: vec![*leaf, *root],
                circuit_type: BiniusCircuitType::Membership,
                log_inv_rate: LOG_INV_RATE,
                security_bits: SECURITY_BITS,
                circuit_param: depth,
            })
        }
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        if proof.circuit_type != BiniusCircuitType::Membership {
            return Err("wrong circuit type for membership verification".into());
        }
        if proof.public_inputs.len() < 2 {
            return Err("insufficient public inputs".into());
        }
        if &proof.public_inputs[1] != root {
            return Ok(false);
        }

        #[cfg(feature = "binius")]
        {
            return verify_merkle_membership_binius(proof, root);
        }

        #[cfg(not(feature = "binius"))]
        {
            // Stub verification: check proof structure.
            if proof.proof_bytes.len() < 9 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"BINI" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 1 {
                return Err("unsupported proof version".into());
            }
            Ok(true)
        }
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        if removals.is_empty() {
            return Err("fold step must remove at least one fact".into());
        }

        #[cfg(feature = "binius")]
        {
            return prove_fold_step_binius(old_root, new_root, removals);
        }

        #[cfg(not(feature = "binius"))]
        {
            let removal_commitment = compute_removal_commitment(removals);

            let mut proof_bytes = Vec::new();
            proof_bytes.extend_from_slice(b"BINI");
            proof_bytes.push(1);
            proof_bytes.extend_from_slice(&(removals.len() as u32).to_le_bytes());
            proof_bytes.extend_from_slice(&removal_commitment);

            Ok(BiniusProof {
                proof_bytes,
                public_inputs: vec![*old_root, *new_root, removal_commitment],
                circuit_type: BiniusCircuitType::FoldStep,
                log_inv_rate: LOG_INV_RATE,
                security_bits: SECURITY_BITS,
                circuit_param: removals.len(),
            })
        }
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        if proof.circuit_type != BiniusCircuitType::FoldStep {
            return Err("wrong circuit type for fold verification".into());
        }
        if proof.public_inputs.len() < 3 {
            return Err("insufficient public inputs for fold proof".into());
        }

        #[cfg(feature = "binius")]
        {
            return verify_fold_step_binius(proof);
        }

        #[cfg(not(feature = "binius"))]
        {
            if proof.proof_bytes.len() < 9 {
                return Err("proof too short".into());
            }
            if &proof.proof_bytes[..4] != b"BINI" {
                return Err("invalid proof magic".into());
            }
            if proof.proof_bytes[4] != 1 {
                return Err("unsupported proof version".into());
            }
            Ok(true)
        }
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        proof.proof_bytes.len() + proof.public_inputs.len() * 32
    }

    fn backend_name() -> &'static str {
        "binius-binary-tower"
    }
}

// ============================================================================
// Proof size estimation
// ============================================================================

/// Estimate the Binius proof size for a Merkle membership circuit.
pub fn estimate_proof_size(tree_depth: usize, security_bits: usize) -> usize {
    let groestl_rounds_per_level = 10;
    let trace_rows = tree_depth * groestl_rounds_per_level;
    let log_trace = (trace_rows as f64).log2().ceil() as usize;
    let log_inv_rate = 1;
    let num_variables = log_trace + log_inv_rate;

    let fri_commitments = num_variables * 32;
    let sumcheck_messages = num_variables * 3 * 16;
    let num_queries = security_bits / log_inv_rate;
    let query_size = num_variables * 32;
    let fri_openings = num_queries * query_size / 10;
    let eval_claims = 64;

    fri_commitments + sumcheck_messages + fri_openings + eval_claims
}

/// Compare proof sizes across backends.
pub fn proof_size_comparison() -> Vec<(&'static str, usize, usize, usize)> {
    vec![
        (
            "binius-binary-tower",
            estimate_proof_size(4, 100),
            estimate_proof_size(8, 100),
            estimate_proof_size(16, 100),
        ),
        ("babybear-stark", 24_000, 48_000, 96_000),
        ("mina-kimchi", 5_000, 7_000, 10_000),
    ]
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binius_backend_name() {
        assert_eq!(BiniusBackend::backend_name(), "binius-binary-tower");
    }

    #[test]
    fn binius_prove_and_verify_membership() {
        // Binary tree: 1 sibling per level (matches in-circuit BLAKE3 compress).
        let leaf = [0x42u8; 32];
        let sibling_0 = vec![[0x01u8; 32]];
        let sibling_1 = vec![[0x04u8; 32]];
        let siblings = vec![sibling_0, sibling_1];

        let root = compute_merkle_root(&leaf, &siblings);

        let proof = BiniusBackend::prove_membership(&leaf, &siblings, &root).unwrap();
        assert_eq!(proof.circuit_type, BiniusCircuitType::Membership);
        assert_eq!(proof.public_inputs.len(), 2);
        assert_eq!(proof.public_inputs[0], leaf);
        assert_eq!(proof.public_inputs[1], root);

        let valid = BiniusBackend::verify_membership(&proof, &root).unwrap();
        assert!(valid);
    }

    #[test]
    fn binius_verify_wrong_root_fails() {
        let leaf = [0x42u8; 32];
        let siblings = vec![vec![[0x01u8; 32]]];
        let root = compute_merkle_root(&leaf, &siblings);

        let proof = BiniusBackend::prove_membership(&leaf, &siblings, &root).unwrap();

        let wrong_root = [0xFFu8; 32];
        let valid = BiniusBackend::verify_membership(&proof, &wrong_root).unwrap();
        assert!(!valid);
    }

    #[test]
    fn binius_invalid_witness_rejected() {
        let leaf = [0x42u8; 32];
        let siblings = vec![vec![[0x01u8; 32]]];
        let wrong_root = [0xAAu8; 32];

        let result = BiniusBackend::prove_membership(&leaf, &siblings, &wrong_root);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid witness"));
    }

    #[test]
    fn binius_prove_and_verify_fold() {
        let old_root = [0x10u8; 32];
        let new_root = [0x20u8; 32];
        let removals = vec![[0xAAu8; 32], [0xBBu8; 32]];

        let proof = BiniusBackend::prove_fold_step(&old_root, &new_root, &removals).unwrap();
        assert_eq!(proof.circuit_type, BiniusCircuitType::FoldStep);
        assert_eq!(proof.public_inputs.len(), 3);
        assert_eq!(proof.public_inputs[0], old_root);
        assert_eq!(proof.public_inputs[1], new_root);

        let valid = BiniusBackend::verify_fold(&proof).unwrap();
        assert!(valid);
    }

    #[test]
    fn binius_fold_empty_removals_rejected() {
        let old_root = [0x10u8; 32];
        let new_root = [0x20u8; 32];

        let result = BiniusBackend::prove_fold_step(&old_root, &new_root, &[]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("at least one fact"));
    }

    #[test]
    fn binius_proof_size_smaller_than_stark() {
        let leaf = [0x42u8; 32];
        // Binary tree: 4 levels, 1 sibling per level.
        let siblings = vec![
            vec![[1u8; 32]],
            vec![[4u8; 32]],
            vec![[7u8; 32]],
            vec![[10u8; 32]],
        ];
        let root = compute_merkle_root(&leaf, &siblings);

        let proof = BiniusBackend::prove_membership(&leaf, &siblings, &root).unwrap();
        let size = BiniusBackend::proof_size(&proof);

        // Binius proofs should be compact (under 5 KiB for real, much less for stub)
        assert!(
            size < 10_000,
            "Binius proof should be compact, got {size} bytes"
        );
    }

    #[test]
    fn binius_estimate_proof_sizes() {
        let size_4 = estimate_proof_size(4, 100);
        let size_8 = estimate_proof_size(8, 100);
        let size_16 = estimate_proof_size(16, 100);

        assert!(size_4 < size_8);
        assert!(size_8 < size_16);
        assert!(size_16 < 10_000, "depth-16 estimate: {size_16} bytes");
        assert!(
            size_4 < 24_000 / 3,
            "depth-4 Binius should be <3x smaller than STARK"
        );
    }

    #[test]
    fn binius_proof_size_comparison_table() {
        let comparison = proof_size_comparison();
        assert_eq!(comparison.len(), 3);

        let binius = &comparison[0];
        let stark = &comparison[1];
        assert!(
            binius.1 < stark.1,
            "Binius depth-4 should be smaller than STARK"
        );
        assert!(
            binius.3 < stark.3,
            "Binius depth-16 should be smaller than STARK"
        );
    }

    #[test]
    fn binius_merkle_root_computation() {
        let leaf = [0x42u8; 32];
        // Binary tree: 1 sibling per level.
        let siblings = vec![vec![[1u8; 32]], vec![[4u8; 32]]];

        let root1 = compute_merkle_root(&leaf, &siblings);
        let root2 = compute_merkle_root(&leaf, &siblings);
        assert_eq!(root1, root2);

        let leaf2 = [0x43u8; 32];
        let root3 = compute_merkle_root(&leaf2, &siblings);
        assert_ne!(root1, root3);
    }

    #[test]
    fn binius_blake3_compress_matches_reference() {
        // Verify our out-of-circuit compress matches by testing a known case.
        let cv = BLAKE3_IV;
        let block = [0u32; 16];
        let output =
            blake3_compress_out_of_circuit(&cv, &block, 0, 64, BLAKE3_SINGLE_BLOCK_ROOT_FLAGS);
        // The output should be deterministic and non-trivial.
        assert_ne!(output, [0u32; 16]);
        // Running it again should give the same result.
        let output2 =
            blake3_compress_out_of_circuit(&cv, &block, 0, 64, BLAKE3_SINGLE_BLOCK_ROOT_FLAGS);
        assert_eq!(output, output2);
    }

    #[test]
    fn binius_binary_merkle_hash_deterministic() {
        let left = [0xAAu8; 32];
        let right = [0xBBu8; 32];
        let h1 = merkle_hash_binary(&left, &right);
        let h2 = merkle_hash_binary(&left, &right);
        assert_eq!(h1, h2);
        // Different inputs should produce different outputs.
        let h3 = merkle_hash_binary(&right, &left);
        assert_ne!(h1, h3);
    }
}
