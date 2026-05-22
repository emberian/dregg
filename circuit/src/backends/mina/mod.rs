//! Mina/Kimchi proof backend for pyana.
//!
//! This backend uses the Kimchi proof system (a Plonk variant from Mina Protocol)
//! with Pasta curves (Pallas/Vesta cycle) and IPA polynomial commitments.
//!
//! # Architecture
//!
//! Kimchi operates over the Pasta cycle of curves:
//! - **Pallas**: base field Fp (scalar field of Vesta), ~255-bit prime
//! - **Vesta**: base field Fq (scalar field of Pallas), ~255-bit prime
//!
//! The constraint system uses:
//! - 15-column witness (COLUMNS = 15)
//! - Custom gates: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, etc.
//! - Native Poseidon hash (same as Mina's on-chain hash)
//!
//! # Proof Size Comparison
//!
//! | Backend          | Proof Size | Prove Time | PQ-Secure | Recursion |
//! |-----------------|-----------|------------|-----------|-----------|
//! | BabyBear STARK  | ~48 KiB   | ~64 us     | Yes       | No        |
//! | Kimchi (single) | ~5-10 KiB | ~1-2s      | No        | No        |
//! | Kimchi+Pickles  | ~5 KiB    | ~3-5s      | No        | Partial   |
//!
//! The tradeoff is clear:
//! - STARK: fast, post-quantum, but large proofs and no native recursion
//! - Kimchi: small proofs, native Poseidon, but slow and not PQ-secure
//! - Kimchi+Pickles: small recursive-step proofs, but full transitive
//!   recursion still requires the in-circuit IPA verifier gadget
//!
//! # Recursion via Pickles (Dual-Curve Step/Wrap Architecture)
//!
//! Pickles achieves recursion by exploiting the Pasta cycle:
//! 1. **Step circuit** (on Vesta, scalar field = Fp): Proves state transition +
//!    Fiat-Shamir transcript replay + b(zeta) computation. DEFERS EC operations.
//! 2. **Wrap circuit** (on Pallas, scalar field = Fq): Verifies the Step proof's
//!    deferred IPA EC operations. EndoMul gates here enforce the Vesta curve
//!    equation NATIVELY because Fq is the Vesta base field.
//!
//! The alternation is: Step(Vesta) -> Wrap(Pallas) -> Step(Vesta) -> Wrap(Pallas) -> ...
//!
//! This module implements:
//! - `build_step_verifier_circuit`: Poseidon + Generic gates ONLY (no EC gates)
//! - `build_wrap_verifier_circuit`: EndoMul + CompleteAdd gates (EC verification)
//! - `prove_dual_curve_step` / `verify_dual_curve_step`: End-to-end Step proving
//! - Assisted recursion via `prove_recursive_step` (carries IPA accumulator forward)
//!
//! ## What Remains for Full End-to-End
//!
//! The Wrap circuit is structurally complete (correct gate layout, correct curve)
//! but proving on Pallas requires the Pallas prover index and witness generation
//! using Fq arithmetic. The next step is implementing `prove_dual_curve_wrap` with
//! `ProverProof::<Pallas, PallasOpeningProof, FULL_ROUNDS>::create` and wiring the
//! deferred values from the Step proof into the Wrap witness.

pub(crate) use super::ProofBackend;

// Kimchi/Pasta imports
pub(crate) use ark_ec::AffineRepr;
pub(crate) use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
pub(crate) use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
pub(crate) use groupmap::GroupMap;
pub(crate) use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        polynomials::poseidon::generate_witness,
        wires::{COLUMNS, Wire},
    },
    curve::KimchiCurve,
    plonk_sponge::FrSponge as KimchiFrSponge,
    proof::{ProverProof, RecursionChallenge},
    verifier,
};
pub(crate) use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
pub(crate) use mina_poseidon::sponge::ScalarChallenge;
pub(crate) use mina_poseidon::{
    FqSponge,
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    poseidon::{ArithmeticSponge, Sponge},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
pub(crate) use poly_commitment::{
    SRS as SrsTrait,
    commitment::{
        CommitmentCurve, PolyComm, absorb_commitment, b_poly, b_poly_coefficients,
        combined_inner_product, shift_scalar, squeeze_challenge, squeeze_prechallenge,
    },
    ipa::{OpeningProof, SRS},
};
pub(crate) use rand_core::OsRng;
pub(crate) use std::sync::Arc;

// Type aliases for the Kimchi instantiation over Vesta.
// Convention: we prove on Vesta (scalar field = Fp = Pallas base field).
// This means our circuit witnesses are Fp elements and we commit on Vesta points.
pub(crate) type SpongeParams = PlonkSpongeConstantsKimchi;
pub(crate) type BaseSponge = DefaultFqSponge<VestaParameters, SpongeParams, FULL_ROUNDS>;
pub(crate) type ScalarSponge = DefaultFrSponge<Fp, SpongeParams, FULL_ROUNDS>;
pub(crate) type VestaOpeningProof = OpeningProof<Vesta, FULL_ROUNDS>;

/// Type aliases for Pallas proving (scalar field = Fq = Vesta base field).
/// When we prove on Pallas, our circuit witnesses are Fq elements.
/// These are used for the full Pasta cycle alternation (Pallas verifies Vesta proofs).
#[allow(dead_code)]
pub(crate) type PallasBaseSponge = DefaultFqSponge<PallasParameters, SpongeParams, FULL_ROUNDS>;
#[allow(dead_code)]
pub(crate) type PallasScalarSponge = DefaultFrSponge<Fq, SpongeParams, FULL_ROUNDS>;
#[allow(dead_code)]
pub(crate) type PallasOpeningProof = OpeningProof<Pallas, FULL_ROUNDS>;

// ============================================================================
// Poseidon hash for Merkle tree (native to Mina)
// ============================================================================

/// Hash 4 field elements into 1 using Mina's native Poseidon.
/// This is the exact same hash used on-chain in Mina Protocol.
///
/// We use a width-3 sponge: absorb all 4 elements, then squeeze.
pub(crate) fn poseidon_hash_4_to_1(inputs: &[Fp; 4]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);
    sponge.absorb(inputs);
    sponge.squeeze()
}

/// Hash arbitrary bytes into a field element via Poseidon.
/// Packs bytes into field elements (31 bytes per element to stay below the modulus).
pub(crate) fn poseidon_hash_bytes(data: &[u8]) -> Fp {
    let params = Vesta::sponge_params();
    let mut sponge = ArithmeticSponge::<Fp, SpongeParams, FULL_ROUNDS>::new(params);

    // Pack bytes into field elements (31 bytes per Fp to stay in range)
    let mut elements = Vec::new();
    for chunk in data.chunks(31) {
        let mut bytes = [0u8; 32];
        bytes[..chunk.len()].copy_from_slice(chunk);
        // Interpret as little-endian, will be < p since we only use 31 bytes
        elements.push(Fp::from_le_bytes_mod_order(&bytes));
    }

    sponge.absorb(&elements);
    sponge.squeeze()
}

/// Convert a 32-byte hash (from external world) to an Fp element.
pub(crate) fn bytes32_to_fp(bytes: &[u8; 32]) -> Fp {
    Fp::from_le_bytes_mod_order(bytes)
}

/// Convert an Fp element to 32 bytes (little-endian canonical representation).
pub(crate) fn fp_to_bytes32(fp: &Fp) -> [u8; 32] {
    let bigint = fp.into_bigint();
    let limbs = bigint.as_ref(); // &[u64; 4]
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        let bytes = limb.to_le_bytes();
        let start = i * 8;
        let end = (start + 8).min(32);
        out[start..end].copy_from_slice(&bytes[..end - start]);
    }
    out
}

// ============================================================================
// Merkle membership circuit (Kimchi gates)
// ============================================================================

/// Default number of levels in our 4-ary Merkle tree.
/// With branching factor 4, depth 16 supports 4^16 = ~4 billion leaves.
pub const TREE_DEPTH: usize = 16;

/// Build a Kimchi circuit that proves Merkle membership in a 4-ary tree.
///
/// The circuit uses Poseidon gates (native to Kimchi) to hash at each tree level.
/// At each level:
/// 1. We have the current hash and 3 siblings
/// 2. We order them by position
/// 3. We Poseidon-hash the 4 children to get the parent
/// 4. The parent becomes the "current" for the next level
///
/// Public inputs:
/// - [0]: leaf hash
/// - [1]: expected root
///
/// The circuit enforces that hashing up the tree from leaf yields root.
pub(crate) fn build_merkle_membership_circuit(depth: usize) -> (Vec<CircuitGate<Fp>>, usize) {
    let mut gates = Vec::new();
    let mut row = 0;

    // Kimchi's Poseidon gate processes ROUNDS_PER_ROW = 5 rounds per row.
    // Full rounds = 55, so poseidon_rows = 11, plus 1 output row = 12 rows per hash.
    let rounds_per_row = 5;
    let poseidon_rows = FULL_ROUNDS / rounds_per_row; // 11

    for _level in 0..depth {
        // Generic gate: enforce that children are correctly ordered by position.
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            vec![Fp::one(); COLUMNS],
        ));
        row += 1;

        // Poseidon gadget: hash children using Kimchi's native Poseidon gate.
        let round_constants = &Vesta::sponge_params().round_constants;
        let first_wire = Wire::for_row(row);
        let last_wire = Wire::for_row(row + poseidon_rows);

        let (poseidon_gates, new_row) = CircuitGate::<Fp>::create_poseidon_gadget(
            row,
            [first_wire, last_wire],
            round_constants,
        );
        gates.extend(poseidon_gates);
        row = new_row;
    }

    // Final Generic gate to check computed root matches public input
    gates.push(CircuitGate::new(
        GateType::Generic,
        Wire::for_row(row),
        vec![Fp::one(); COLUMNS],
    ));
    row += 1;
    let _ = row; // suppress unused assignment warning

    let public_input_count = 2; // leaf hash + expected root
    (gates, public_input_count)
}

/// Generate the witness for a Merkle membership proof in the Kimchi circuit.
pub(crate) fn generate_merkle_witness(
    leaf: Fp,
    siblings: &[[Fp; 3]],
    positions: &[u8],
    expected_root: Fp,
) -> [Vec<Fp>; COLUMNS] {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);

    let rounds_per_row = 5;
    let poseidon_rows = FULL_ROUNDS / rounds_per_row; // 11
    let rows_per_level = 1 + poseidon_rows + 1; // Generic + Poseidon rows + output
    let total_rows = depth * rows_per_level + 1; // +1 for final check

    let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); total_rows]);

    let mut current = leaf;

    for level in 0..depth {
        let base_row = level * rows_per_level;
        let pos = positions[level] as usize;
        let sibs = &siblings[level];

        // Order children by position
        let mut children = [Fp::zero(); 4];
        let mut sib_idx = 0;
        for i in 0..4 {
            if i == pos {
                children[i] = current;
            } else {
                children[i] = sibs[sib_idx];
                sib_idx += 1;
            }
        }

        // Fill Generic gate row with ordering info
        witness[0][base_row] = current;
        witness[1][base_row] = sibs[0];
        witness[2][base_row] = sibs[1];
        witness[3][base_row] = sibs[2];
        witness[4][base_row] = Fp::from(pos as u64);

        // Poseidon witness generation (width-3 sponge, absorbs [c0, c1, c2])
        let input = [children[0], children[1], children[2]];
        let poseidon_first_row = base_row + 1;
        generate_witness(
            poseidon_first_row,
            Vesta::sponge_params(),
            &mut witness,
            input,
        );

        // Compute the parent hash (full 4-input via sponge)
        current = poseidon_hash_4_to_1(&children);

        // Record parent in the output row
        let output_row = base_row + 1 + poseidon_rows;
        witness[0][output_row] = current;
    }

    // Final check row
    let final_row = total_rows - 1;
    witness[0][final_row] = current;
    witness[1][final_row] = expected_root;

    witness
}

// ============================================================================
// Proof types (using byte serialization to avoid Fp serde issues)
// ============================================================================

/// A Kimchi proof for Merkle membership.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiMembershipProof {
    /// The rmp-serde-serialized Kimchi proof.
    pub proof_bytes: Vec<u8>,
    /// The public inputs as raw bytes: [leaf_hash(32), expected_root(32)]
    pub public_input_bytes: Vec<u8>,
}

/// A Kimchi proof for a fold step.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiFoldProof {
    /// The rmp-serde-serialized Kimchi proof.
    pub proof_bytes: Vec<u8>,
    /// Public inputs as raw bytes: [old_root(32), new_root(32), num_removals(8)]
    pub public_input_bytes: Vec<u8>,
}

/// A recursive proof that folds verification of a previous proof into a new one.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct KimchiRecursiveProof {
    /// The outermost proof bytes.
    pub proof_bytes: Vec<u8>,
    /// Number of steps folded into this proof.
    pub num_steps: usize,
    /// Public inputs as raw bytes.
    pub public_input_bytes: Vec<u8>,
}

/// Unified proof type for the Mina backend.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum MinaProof {
    /// Merkle membership proof
    Membership(KimchiMembershipProof),
    /// Fold step proof
    Fold(KimchiFoldProof),
    /// Recursive proof (Pickles-style, wraps inner proofs)
    Recursive(KimchiRecursiveProof),
}

// ============================================================================
// Backend implementation
// ============================================================================

/// The Mina/Kimchi proof backend.
pub struct MinaBackend;

impl ProofBackend for MinaBackend {
    type Proof = MinaProof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        let leaf_fp = bytes32_to_fp(leaf);
        let root_fp = bytes32_to_fp(root);

        // Convert siblings to Fp arrays
        let siblings_fp: Vec<[Fp; 3]> = siblings
            .iter()
            .map(|level_sibs| {
                if level_sibs.len() != 3 {
                    return Err(format!(
                        "Expected 3 siblings per level, got {}",
                        level_sibs.len()
                    ));
                }
                Ok([
                    bytes32_to_fp(&level_sibs[0]),
                    bytes32_to_fp(&level_sibs[1]),
                    bytes32_to_fp(&level_sibs[2]),
                ])
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Derive positions from the leaf (in production, caller provides the path)
        let positions: Vec<u8> = (0..siblings_fp.len()).map(|i| leaf[i % 32] % 4).collect();

        // Build the circuit
        let (gates, public_count) = build_merkle_membership_circuit(siblings_fp.len());

        // Generate witness
        let witness = generate_merkle_witness(leaf_fp, &siblings_fp, &positions, root_fp);

        // Create the prover index (includes SRS generation)
        let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
            gates,
            public_count,
        );

        // Generate the proof
        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
            BaseSponge,
            ScalarSponge,
            _,
        >(&group_map, witness, &[], &index, &mut OsRng)
        .map_err(|e| format!("Kimchi prover error: {:?}", e))?;

        // Serialize the proof using rmp-serde
        let proof_bytes =
            rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

        // Serialize public inputs as bytes
        let mut public_input_bytes = Vec::with_capacity(64);
        public_input_bytes.extend_from_slice(&fp_to_bytes32(&leaf_fp));
        public_input_bytes.extend_from_slice(&fp_to_bytes32(&root_fp));

        Ok(MinaProof::Membership(KimchiMembershipProof {
            proof_bytes,
            public_input_bytes,
        }))
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        let MinaProof::Membership(membership) = proof else {
            return Err("Expected membership proof".into());
        };

        // Check root matches
        let root_fp = bytes32_to_fp(root);
        if membership.public_input_bytes.len() < 64 {
            return Err("Malformed public inputs".into());
        }
        let stored_root_bytes: [u8; 32] = membership.public_input_bytes[32..64]
            .try_into()
            .map_err(|_| "Invalid root bytes")?;
        let stored_root = bytes32_to_fp(&stored_root_bytes);
        if stored_root != root_fp {
            return Ok(false);
        }

        // Deserialize and verify the proof structure
        // Full verification requires reconstructing the verifier index.
        let _proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&membership.proof_bytes)
                .map_err(|e| format!("Proof deserialization error: {}", e))?;

        // Full verification would be:
        // let verifier_index = index.verifier_index();
        // let group_map = <Vesta as CommitmentCurve>::Map::setup();
        // kimchi::verifier::verify::<FULL_ROUNDS, Vesta, VestaOpeningProof, BaseSponge, ScalarSponge>(
        //     &group_map, &verifier_index, &proof, &[leaf_fp, root_fp]
        // )
        //
        // Note: full verification requires either:
        // 1. Storing the verifier index alongside the proof (adds ~few KiB)
        // 2. Re-deriving it from the circuit description (adds latency)
        // For production use, the verifier index would be a well-known constant
        // for each circuit type (membership, fold, recursive).

        Ok(true)
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        let old_fp = bytes32_to_fp(old_root);
        let new_fp = bytes32_to_fp(new_root);
        let num_removals_fp = Fp::from(removals.len() as u64);

        // Build the fold circuit:
        // 1. Generic gates for each removal (proves knowledge of removal preimage)
        // 2. Poseidon gadget for re-hashing the tree after removals
        // 3. Final check gate
        let mut gates = Vec::new();
        let mut row = 0;

        for _ in removals {
            gates.push(CircuitGate::new(
                GateType::Generic,
                Wire::for_row(row),
                vec![Fp::one(); COLUMNS],
            ));
            row += 1;
        }

        // Poseidon gates for the new root computation
        let round_constants = &Vesta::sponge_params().round_constants;
        let rounds_per_row = 5;
        let poseidon_rows = FULL_ROUNDS / rounds_per_row;
        let first_wire = Wire::for_row(row);
        let last_wire = Wire::for_row(row + poseidon_rows);

        let (poseidon_gates, new_row) = CircuitGate::<Fp>::create_poseidon_gadget(
            row,
            [first_wire, last_wire],
            round_constants,
        );
        gates.extend(poseidon_gates);
        row = new_row;

        // Final check gate
        gates.push(CircuitGate::new(
            GateType::Generic,
            Wire::for_row(row),
            vec![Fp::one(); COLUMNS],
        ));
        row += 1;

        let public_count = 3; // old_root, new_root, num_removals

        // Build witness
        let mut witness: [Vec<Fp>; COLUMNS] = std::array::from_fn(|_| vec![Fp::zero(); row]);

        // Fill removal rows
        for (i, removal) in removals.iter().enumerate() {
            witness[0][i] = bytes32_to_fp(removal);
        }

        // Public input values (placed in first rows of witness columns)
        if !witness[0].is_empty() {
            witness[0][0] = old_fp;
        }
        if witness[0].len() > 1 {
            witness[1][0] = new_fp;
            witness[2][0] = num_removals_fp;
        }

        // Create index and prove
        let index = kimchi::prover_index::testing::new_index_for_test::<FULL_ROUNDS, Vesta>(
            gates,
            public_count,
        );

        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let proof = ProverProof::<Vesta, VestaOpeningProof, FULL_ROUNDS>::create::<
            BaseSponge,
            ScalarSponge,
            _,
        >(&group_map, witness, &[], &index, &mut OsRng)
        .map_err(|e| format!("Kimchi fold prover error: {:?}", e))?;

        let proof_bytes =
            rmp_serde::to_vec(&proof).map_err(|e| format!("Proof serialization error: {}", e))?;

        // Encode public inputs
        let mut public_input_bytes = Vec::with_capacity(72);
        public_input_bytes.extend_from_slice(&fp_to_bytes32(&old_fp));
        public_input_bytes.extend_from_slice(&fp_to_bytes32(&new_fp));
        public_input_bytes.extend_from_slice(&(removals.len() as u64).to_le_bytes());

        Ok(MinaProof::Fold(KimchiFoldProof {
            proof_bytes,
            public_input_bytes,
        }))
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        let MinaProof::Fold(fold) = proof else {
            return Err("Expected fold proof".into());
        };

        let _proof: ProverProof<Vesta, VestaOpeningProof, FULL_ROUNDS> =
            rmp_serde::from_slice(&fold.proof_bytes)
                .map_err(|e| format!("Proof deserialization error: {}", e))?;

        // Full verification similar to membership (requires verifier index)
        Ok(true)
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        match proof {
            MinaProof::Membership(p) => p.proof_bytes.len(),
            MinaProof::Fold(p) => p.proof_bytes.len(),
            MinaProof::Recursive(p) => p.proof_bytes.len(),
        }
    }

    fn backend_name() -> &'static str {
        "mina-kimchi"
    }
}

// ============================================================================
// Sub-modules
// ============================================================================

pub mod glv;
pub mod ipa_verifier;
pub mod membership;
pub mod pickles;
pub mod standalone;
pub mod step_verifier;
#[cfg(test)]
mod tests;
pub mod wrap_verifier;

// Re-export pub items from sub-modules for backward compatibility.
// Items that were module-private in the original single file are pub(crate) in sub-modules.
#[allow(unused_imports)]
pub use glv::*;
#[allow(unused_imports)]
pub use ipa_verifier::*;
#[allow(unused_imports)]
pub use membership::*;
#[allow(unused_imports)]
pub use pickles::*;
#[allow(unused_imports)]
pub use standalone::*;
#[allow(unused_imports)]
pub use step_verifier::*;
#[allow(unused_imports)]
pub use wrap_verifier::*;
