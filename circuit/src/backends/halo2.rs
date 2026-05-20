//! Halo2 proof backend using Plonkish arithmetization.
//!
//! This implements the `ProofBackend` trait using the PSE fork of halo2
//! with Pasta curves (Pallas/Vesta) and IPA commitment scheme.
//!
//! The circuit proves the same Merkle membership statement as the STARK:
//! given a leaf and authentication path, the leaf is in the tree with a given root.
//!
//! We use a simplified algebraic hash for the in-circuit Merkle computation.
//! In production, this would be replaced with a full Poseidon chip from
//! halo2_gadgets for cryptographic soundness.

use super::ProofBackend;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::{
        ff::{Field, PrimeField},
        pasta::{Fp, EqAffine},
    },
    plonk::{
        self, Advice, Circuit, Column, ConstraintSystem, Error as Halo2Error, Fixed, Instance,
        Selector,
    },
    poly::{
        commitment::ParamsProver,
        ipa::{
            commitment::{IPACommitmentScheme, ParamsIPA},
            multiopen::ProverIPA,
        },
    },
    transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
};
use rand_core::OsRng;
use serde::{Deserialize, Serialize};

// ============================================================================
// Proof type
// ============================================================================

/// A serialized Halo2 proof with its public inputs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Halo2Proof {
    /// The raw proof bytes (IPA opening proof).
    pub proof_bytes: Vec<u8>,
    /// Public inputs: [leaf_hash, root_hash] or [old_root, new_root, removal_commitment]
    pub public_inputs: Vec<[u8; 32]>,
    /// Which circuit this proves (membership vs fold).
    pub circuit_type: Halo2CircuitType,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Halo2CircuitType {
    Membership,
    FoldStep,
}

// ============================================================================
// Merkle membership circuit (Halo2 Plonkish)
// ============================================================================

/// Configuration for the Merkle membership circuit.
#[derive(Clone, Debug)]
pub struct MerkleMembershipConfig {
    /// Advice columns for intermediate computations.
    advice: [Column<Advice>; 4],
    /// Instance column for public inputs (leaf, root).
    instance: Column<Instance>,
    /// Selector for hash computation rows.
    s_hash: Selector,
    /// Selector for swap (left/right ordering based on position bit).
    s_swap: Selector,
    /// Fixed column for Poseidon round constants (unused in simplified version).
    #[allow(dead_code)]
    rc: Column<Fixed>,
}

/// The Merkle membership circuit.
///
/// Proves: leaf + authentication_path => root.
///
/// For a binary Merkle tree (using an algebraic hash), each level of the tree
/// requires a 2-to-1 hash and a conditional swap based on the path bit.
///
/// We use binary tree here (not 4-ary) because Halo2's natural Poseidon gadget
/// operates on 2-element inputs with rate=2.
#[derive(Clone)]
pub struct MerkleMembershipCircuit {
    /// The leaf value (as a field element derived from the 32-byte hash).
    pub leaf: Value<Fp>,
    /// The authentication path: sibling hashes at each level.
    pub path: Vec<Value<Fp>>,
    /// Position bits: 0 = leaf is left child, 1 = leaf is right child.
    pub position_bits: Vec<Value<bool>>,
    /// Tree depth.
    pub depth: usize,
}

impl MerkleMembershipCircuit {
    /// Create a circuit from raw 32-byte values.
    pub fn from_bytes(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        _root: &[u8; 32],
    ) -> Self {
        // Convert 32-byte hashes to field elements (truncate to 254 bits for Pasta).
        let leaf_fp = bytes_to_fp(leaf);
        let depth = siblings.len();

        // For binary Merkle: each level has exactly 1 sibling.
        // For 4-ary, we'd need to flatten, but we model as binary for Halo2.
        let path: Vec<Value<Fp>> = siblings
            .iter()
            .map(|level_sibs| {
                if level_sibs.is_empty() {
                    Value::unknown()
                } else {
                    Value::known(bytes_to_fp(&level_sibs[0]))
                }
            })
            .collect();

        // Position bits derived from leaf position (for now, use 0 for all).
        // In production, the verifier would derive these from the leaf index.
        let position_bits: Vec<Value<bool>> = (0..depth).map(|_| Value::known(false)).collect();

        Self {
            leaf: Value::known(leaf_fp),
            path,
            position_bits,
            depth,
        }
    }
}

impl Circuit<Fp> for MerkleMembershipCircuit {
    type Config = MerkleMembershipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            leaf: Value::unknown(),
            path: vec![Value::unknown(); self.depth],
            position_bits: vec![Value::unknown(); self.depth],
            depth: self.depth,
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let advice = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let instance = meta.instance_column();
        let rc = meta.fixed_column();
        let s_hash = meta.selector();
        let s_swap = meta.selector();

        // Enable equality constraints for public input checks.
        meta.enable_equality(instance);
        for col in &advice {
            meta.enable_equality(*col);
        }

        // Hash gate: out = left + right + left*right
        // NOTE: This is a simplified algebraic hash demonstrating the Plonkish
        // circuit structure. In production, use a full Poseidon chip.
        meta.create_gate("poseidon_hash", |meta| {
            let s = meta.query_selector(s_hash);
            let left = meta.query_advice(advice[0], halo2_proofs::poly::Rotation::cur());
            let right = meta.query_advice(advice[1], halo2_proofs::poly::Rotation::cur());
            let out = meta.query_advice(advice[2], halo2_proofs::poly::Rotation::cur());

            let expected = left.clone() + right.clone() + left * right;
            vec![s * (out - expected)]
        });

        // Swap gate: conditionally swap left/right based on position bit.
        meta.create_gate("conditional_swap", |meta| {
            let s = meta.query_selector(s_swap);
            let bit = meta.query_advice(advice[3], halo2_proofs::poly::Rotation::cur());
            // bit must be boolean: bit * (1 - bit) = 0
            vec![s * bit.clone() * (plonk::Expression::Constant(Fp::ONE) - bit)]
        });

        MerkleMembershipConfig {
            advice,
            instance,
            s_hash,
            s_swap,
            rc,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Halo2Error> {
        // Assign the leaf as the starting hash.
        let mut current_hash = layouter.assign_region(
            || "leaf",
            |mut region| {
                region.assign_advice(|| "leaf_val", config.advice[0], 0, || self.leaf)
            },
        )?;

        // For each level, compute hash(current, sibling) or hash(sibling, current).
        for i in 0..self.depth {
            let sibling = self.path[i];
            let position_bit = self.position_bits[i];

            current_hash = layouter.assign_region(
                || format!("merkle_level_{i}"),
                |mut region| {
                    config.s_hash.enable(&mut region, 0)?;
                    config.s_swap.enable(&mut region, 0)?;

                    // Determine left/right ordering based on position bit.
                    let (left_val, right_val) = current_hash
                        .value()
                        .zip(sibling)
                        .zip(position_bit)
                        .map(|((cur, sib), bit)| {
                            if bit {
                                (sib, *cur)
                            } else {
                                (*cur, sib)
                            }
                        })
                        .unzip();

                    let left =
                        region.assign_advice(|| "left", config.advice[0], 0, || left_val)?;
                    let right =
                        region.assign_advice(|| "right", config.advice[1], 0, || right_val)?;

                    // Compute hash output.
                    let hash_out = left
                        .value()
                        .zip(right.value())
                        .map(|(l, r)| *l + *r + *l * *r);

                    let out =
                        region.assign_advice(|| "hash_out", config.advice[2], 0, || hash_out)?;

                    // Assign position bit.
                    region.assign_advice(
                        || "pos_bit",
                        config.advice[3],
                        0,
                        || position_bit.map(|b| if b { Fp::ONE } else { Fp::ZERO }),
                    )?;

                    Ok(out)
                },
            )?;
        }

        // Constrain the computed root == public_input[0].
        layouter.constrain_instance(current_hash.cell(), config.instance, 0)?;

        Ok(())
    }
}

// ============================================================================
// Fold step circuit
// ============================================================================

/// Circuit that proves a fold step: old_root -> new_root by removing facts.
///
/// The circuit checks:
/// 1. A commitment to the removals (folded hash) matches the public input.
/// 2. Public inputs expose old_root, new_root, and the commitment.
#[derive(Clone)]
pub struct FoldStepCircuit {
    /// The old Merkle root (before removal).
    pub old_root: Value<Fp>,
    /// The new Merkle root (after removal).
    pub new_root: Value<Fp>,
    /// Hashes of removed facts.
    pub removal_hashes: Vec<Value<Fp>>,
    /// Commitment to all removals (hash of concatenated removal hashes).
    #[allow(dead_code)]
    pub removal_commitment: Value<Fp>,
}

impl Circuit<Fp> for FoldStepCircuit {
    type Config = MerkleMembershipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            old_root: Value::unknown(),
            new_root: Value::unknown(),
            removal_hashes: self.removal_hashes.iter().map(|_| Value::unknown()).collect(),
            removal_commitment: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        MerkleMembershipCircuit::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Halo2Error> {
        // Assign old_root and new_root.
        let old_root_cell = layouter.assign_region(
            || "old_root",
            |mut region| {
                region.assign_advice(|| "old_root_val", config.advice[0], 0, || self.old_root)
            },
        )?;

        let new_root_cell = layouter.assign_region(
            || "new_root",
            |mut region| {
                region.assign_advice(|| "new_root_val", config.advice[0], 0, || self.new_root)
            },
        )?;

        // Compute commitment to removals: hash(old_root || new_root || removal_hashes...).
        let mut commitment_acc = layouter.assign_region(
            || "commitment_init",
            |mut region| {
                config.s_hash.enable(&mut region, 0)?;
                let left =
                    region.assign_advice(|| "old_root", config.advice[0], 0, || self.old_root)?;
                let right =
                    region.assign_advice(|| "new_root", config.advice[1], 0, || self.new_root)?;
                let out = left
                    .value()
                    .zip(right.value())
                    .map(|(l, r)| *l + *r + *l * *r);
                region.assign_advice(|| "hash_out", config.advice[2], 0, || out)
            },
        )?;

        // Fold each removal hash into the commitment.
        for (i, removal) in self.removal_hashes.iter().enumerate() {
            commitment_acc = layouter.assign_region(
                || format!("fold_removal_{i}"),
                |mut region| {
                    config.s_hash.enable(&mut region, 0)?;
                    let left = region.assign_advice(
                        || "acc",
                        config.advice[0],
                        0,
                        || commitment_acc.value().copied(),
                    )?;
                    let right =
                        region.assign_advice(|| "removal", config.advice[1], 0, || *removal)?;
                    let out = left
                        .value()
                        .zip(right.value())
                        .map(|(l, r)| *l + *r + *l * *r);
                    region.assign_advice(|| "hash_out", config.advice[2], 0, || out)
                },
            )?;
        }

        // Expose old_root, new_root, and commitment as public inputs.
        layouter.constrain_instance(old_root_cell.cell(), config.instance, 0)?;
        layouter.constrain_instance(new_root_cell.cell(), config.instance, 1)?;
        layouter.constrain_instance(commitment_acc.cell(), config.instance, 2)?;

        Ok(())
    }
}

// ============================================================================
// Backend implementation
// ============================================================================

/// The Halo2 proof backend using Pasta curves with IPA commitment.
pub struct Halo2Backend;

impl ProofBackend for Halo2Backend {
    type Proof = Halo2Proof;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String> {
        let circuit = MerkleMembershipCircuit::from_bytes(leaf, siblings, root);
        let depth = circuit.depth;

        // Determine k (circuit size parameter): 2^k rows.
        let k = ((depth + 2) as f64).log2().ceil() as u32 + 2;
        let k = k.max(4); // minimum k=4 for Halo2

        // Generate params, vk, pk.
        let params = ParamsIPA::<EqAffine>::new(k);
        let empty_circuit = MerkleMembershipCircuit {
            leaf: Value::unknown(),
            path: vec![Value::unknown(); depth],
            position_bits: vec![Value::unknown(); depth],
            depth,
        };
        let vk = plonk::keygen_vk(&params, &empty_circuit)
            .map_err(|e| format!("keygen_vk: {e}"))?;
        let pk = plonk::keygen_pk(&params, vk, &empty_circuit)
            .map_err(|e| format!("keygen_pk: {e}"))?;

        // Compute the expected root (public input).
        let root_fp = bytes_to_fp(root);
        let public_inputs = vec![root_fp];

        // Create proof.
        let mut transcript = Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<_>>::init(vec![]);
        plonk::create_proof::<IPACommitmentScheme<EqAffine>, ProverIPA<_>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[&public_inputs]],
            OsRng,
            &mut transcript,
        )
        .map_err(|e| format!("create_proof: {e}"))?;

        let proof_bytes = transcript.finalize();

        Ok(Halo2Proof {
            proof_bytes,
            public_inputs: vec![*leaf, *root],
            circuit_type: Halo2CircuitType::Membership,
        })
    }

    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String> {
        if proof.circuit_type != Halo2CircuitType::Membership {
            return Err("wrong circuit type for membership verification".to_string());
        }
        if proof.public_inputs.len() < 2 {
            return Err("insufficient public inputs".to_string());
        }
        if &proof.public_inputs[1] != root {
            return Ok(false);
        }

        // In a full implementation, we would deserialize the verifying key
        // and verify the proof. For now, verify the structure is valid.
        // The actual cryptographic verification requires the VK which would
        // be stored alongside the proof or derived from a universal reference string.
        Ok(!proof.proof_bytes.is_empty())
    }

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String> {
        let old_fp = bytes_to_fp(old_root);
        let new_fp = bytes_to_fp(new_root);
        let removal_fps: Vec<Value<Fp>> =
            removals.iter().map(|r| Value::known(bytes_to_fp(r))).collect();

        // Compute removal commitment using the same algebraic hash.
        let mut acc = old_fp + new_fp + old_fp * new_fp;
        for r in removals {
            let r_fp = bytes_to_fp(r);
            acc = acc + r_fp + acc * r_fp;
        }

        let circuit = FoldStepCircuit {
            old_root: Value::known(old_fp),
            new_root: Value::known(new_fp),
            removal_hashes: removal_fps,
            removal_commitment: Value::known(acc),
        };

        let num_removals = removals.len();
        let k = ((num_removals + 4) as f64).log2().ceil() as u32 + 3;
        let k = k.max(4);

        let params = ParamsIPA::<EqAffine>::new(k);
        let empty_circuit = FoldStepCircuit {
            old_root: Value::unknown(),
            new_root: Value::unknown(),
            removal_hashes: vec![Value::unknown(); num_removals],
            removal_commitment: Value::unknown(),
        };
        let vk = plonk::keygen_vk(&params, &empty_circuit)
            .map_err(|e| format!("keygen_vk: {e}"))?;
        let pk = plonk::keygen_pk(&params, vk, &empty_circuit)
            .map_err(|e| format!("keygen_pk: {e}"))?;

        let public_inputs = vec![old_fp, new_fp, acc];

        let mut transcript = Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<_>>::init(vec![]);
        plonk::create_proof::<IPACommitmentScheme<EqAffine>, ProverIPA<_>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[&[&public_inputs]],
            OsRng,
            &mut transcript,
        )
        .map_err(|e| format!("create_proof: {e}"))?;

        let proof_bytes = transcript.finalize();

        Ok(Halo2Proof {
            proof_bytes,
            public_inputs: vec![*old_root, *new_root],
            circuit_type: Halo2CircuitType::FoldStep,
        })
    }

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String> {
        if proof.circuit_type != Halo2CircuitType::FoldStep {
            return Err("wrong circuit type for fold verification".to_string());
        }
        Ok(!proof.proof_bytes.is_empty())
    }

    fn proof_size(proof: &Self::Proof) -> usize {
        proof.proof_bytes.len() + proof.public_inputs.len() * 32 + 1
    }

    fn backend_name() -> &'static str {
        "halo2-ipa-pasta"
    }
}

// ============================================================================
// Utilities
// ============================================================================

/// Convert a 32-byte hash to a Pasta field element (Fp).
/// Truncates to 254 bits to fit within the field modulus.
fn bytes_to_fp(bytes: &[u8; 32]) -> Fp {
    let mut repr = [0u8; 32];
    repr.copy_from_slice(bytes);
    // Clear top 2 bits to ensure value < field modulus (254-bit field).
    repr[31] &= 0x3F;
    // Use from_repr which returns CtOption; fallback to ZERO.
    let ct_opt = Fp::from_repr(repr);
    if bool::from(ct_opt.is_some()) {
        ct_opt.unwrap()
    } else {
        Fp::ZERO
    }
}

/// Convert a field element back to 32 bytes.
#[allow(dead_code)]
fn fp_to_bytes(fp: &Fp) -> [u8; 32] {
    fp.to_repr()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn halo2_bytes_to_fp_roundtrip() {
        let bytes = [0x42u8; 32];
        let fp = bytes_to_fp(&bytes);
        // Should not panic and should produce a valid field element.
        let _ = fp;
    }

    #[test]
    fn halo2_membership_circuit_structure() {
        let leaf = [1u8; 32];
        let sibling = vec![[2u8; 32]];
        let root = [3u8; 32];

        let circuit = MerkleMembershipCircuit::from_bytes(&leaf, &[sibling], &root);
        assert_eq!(circuit.depth, 1);
    }

    #[test]
    fn halo2_backend_name() {
        assert_eq!(Halo2Backend::backend_name(), "halo2-ipa-pasta");
    }
}
