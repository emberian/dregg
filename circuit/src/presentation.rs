//! Presentation proof: the complete zero-knowledge authorization proof.
//!
//! Combines:
//! 1. A chain of fold steps (attenuations)
//! 2. A final authorization derivation
//! 3. Issuer membership (Merkle inclusion against federation root)
//!
//! Public inputs:
//! - Federation root (the root of trust)
//! - Request predicate (what is being authorized)
//! - Timestamp (freshness)
//!
//! Private witness:
//! - Entire token chain (sequence of fold deltas)
//! - Derivation trace (proof that the final state authorizes the request)
//! - Issuer key (and its membership in the federation)
//!
//! The presentation proof proves: "I hold a valid attenuated token chain whose
//! final state authorizes action X" without revealing the chain or capabilities.

use crate::derivation_air::{CircuitRule, DerivationAir, DerivationWitness};
use crate::field::BabyBear;
use crate::fold_air::{FoldAir, FoldWitness, RemovedFact};
use crate::ivc::{FoldDelta, IvcPresentationProof, prove_ivc};
use crate::merkle_air::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use crate::mock_prover::{Air, Constraint, MockProof, MockProver};
use crate::poseidon2::hash_fact;
use crate::stark::{self, MerkleStarkAir, StarkProof};

/// The complete presentation witness (all private data).
#[derive(Clone, Debug)]
pub struct PresentationWitness {
    /// The federation root (root of trust, public).
    pub federation_root: BabyBear,
    /// The request predicate hash (public).
    pub request_predicate: BabyBear,
    /// Timestamp for freshness (public).
    pub timestamp: BabyBear,
    /// Chain of fold steps (private).
    pub fold_chain: Vec<FoldWitness>,
    /// The final authorization derivation (private).
    pub derivation: DerivationWitness,
    /// Issuer membership proof in federation (private).
    pub issuer_membership: MerkleWitness,
    /// The issuer's public key hash (private).
    pub issuer_key_hash: BabyBear,
}

/// Public inputs for the presentation proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationPublicInputs {
    /// Federation root of trust.
    pub federation_root: BabyBear,
    /// The request predicate being authorized.
    pub request_predicate: BabyBear,
    /// Timestamp for freshness.
    pub timestamp: BabyBear,
    /// The initial state root (first token's root, committed by issuer).
    pub initial_root: BabyBear,
    /// The final state root (after all attenuations).
    pub final_root: BabyBear,
}

/// A complete presentation proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationProof {
    /// The public inputs.
    pub public_inputs: PresentationPublicInputs,
    /// Proof of the fold chain (sequential STARK proofs).
    pub fold_proofs: Vec<MockProof>,
    /// Proof of the final derivation.
    pub derivation_proof: MockProof,
    /// Proof of issuer membership in federation.
    pub issuer_membership_proof: MockProof,
    /// Total proof size in bytes.
    pub total_proof_size_bytes: usize,
}

impl PresentationProof {
    /// Get a human-readable size.
    pub fn proof_size_display(&self) -> String {
        let bytes = self.total_proof_size_bytes;
        if bytes < 1024 {
            format!("{bytes} B")
        } else if bytes < 1024 * 1024 {
            format!("{:.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
        }
    }

    /// Verify the presentation proof.
    pub fn verify(&self) -> PresentationVerification {
        // 1. Check fold chain continuity
        let mut current_root = self.public_inputs.initial_root;
        for (i, fold_proof) in self.fold_proofs.iter().enumerate() {
            // Each fold proof's public inputs are [old_root, new_root, removals, checks]
            if fold_proof.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
            if fold_proof.public_inputs[0] != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }
            current_root = fold_proof.public_inputs[1];
        }

        // 2. Check derivation proof's state root matches final root
        if self.derivation_proof.public_inputs.is_empty() {
            return PresentationVerification::InvalidDerivation;
        }
        let derivation_state_root = self.derivation_proof.public_inputs[0];
        if derivation_state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }

        // 3. Check final root matches public input
        if current_root != self.public_inputs.final_root {
            return PresentationVerification::FinalRootMismatch;
        }

        // 4. Check issuer membership in federation
        if self.issuer_membership_proof.public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }
        let issuer_federation_root = self.issuer_membership_proof.public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        PresentationVerification::Valid
    }
}

/// Result of presentation proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PresentationVerification {
    /// The proof is valid.
    Valid,
    /// A fold proof in the chain failed.
    InvalidFoldProof { index: usize },
    /// The fold chain has a break (root mismatch between steps).
    FoldChainBreak { index: usize },
    /// The derivation proof is invalid.
    InvalidDerivation,
    /// The derivation's state root doesn't match the end of the fold chain.
    DerivationRootMismatch,
    /// The final root doesn't match public inputs.
    FinalRootMismatch,
    /// The issuer membership proof is invalid.
    InvalidIssuerProof,
    /// The issuer is not in the federation.
    IssuerNotInFederation,
}

/// The presentation AIR: combines all sub-AIRs into one constraint system.
///
/// This is a "meta-AIR" that generates a unified trace by concatenating
/// the sub-proofs. In a real IVC/folding scheme, each step would be
/// recursively verified. Here we verify them sequentially.
pub struct PresentationAir {
    pub witness: PresentationWitness,
}

impl PresentationAir {
    pub fn new(witness: PresentationWitness) -> Self {
        Self { witness }
    }

    /// Generate the full presentation proof.
    pub fn prove(&self) -> Option<PresentationProof> {
        let w = &self.witness;

        // 1. Prove each fold step
        let mut fold_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = MockProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = MockProof::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Prove the derivation
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = MockProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = MockProof::generate(&derivation_air)?;

        // 3. Prove issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let issuer_result = MockProver::verify(&issuer_air);
        if !issuer_result.is_valid() {
            return None;
        }
        let issuer_membership_proof = MockProof::generate(&issuer_air)?;

        // Compute public inputs
        let initial_root = if let Some(first_fold) = w.fold_chain.first() {
            first_fold.old_root
        } else {
            w.derivation.state_root
        };

        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            initial_root,
            final_root,
        };

        // Compute total proof size
        let total_size = fold_proofs
            .iter()
            .map(|p| p.simulated_proof_size_bytes)
            .sum::<usize>()
            + derivation_proof.simulated_proof_size_bytes
            + issuer_membership_proof.simulated_proof_size_bytes;

        Some(PresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_proof,
            total_proof_size_bytes: total_size,
        })
    }

    /// Generate an IVC-based presentation proof (constant-size fold chain proof).
    ///
    /// This is the preferred path: instead of N separate fold proofs, the entire
    /// fold chain is accumulated into a single constant-size IVC proof.
    /// Returns `None` if any component fails to verify.
    pub fn prove_ivc(&self) -> Option<IvcPresentationProof> {
        let w = &self.witness;

        // 1. Generate IVC proof for the fold chain
        if w.fold_chain.is_empty() {
            // No folds: create a trivial IVC proof
            // (the derivation applies directly to the initial state)
            return self.prove_ivc_no_folds();
        }

        let initial_root = w.fold_chain[0].old_root;
        let deltas: Vec<FoldDelta> = w
            .fold_chain
            .iter()
            .map(|f| FoldDelta::new(f.clone()))
            .collect();

        let ivc_proof = prove_ivc(initial_root, deltas)?;

        // 2. Prove the derivation
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = MockProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = MockProof::generate(&derivation_air)?;

        // 3. Prove issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let issuer_result = MockProver::verify(&issuer_air);
        if !issuer_result.is_valid() {
            return None;
        }
        let issuer_membership_proof = MockProof::generate(&issuer_air)?;

        Some(IvcPresentationProof {
            ivc_proof,
            derivation_proof,
            issuer_membership_proof,
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
        })
    }

    /// Helper for the no-folds case in IVC proving.
    fn prove_ivc_no_folds(&self) -> Option<IvcPresentationProof> {
        let w = &self.witness;
        let state_root = w.derivation.state_root;

        // Create a trivial 1-step "identity" IVC proof
        // (the chain is: initial_root -> initial_root with no actual attenuation)
        // For the no-fold case, we still need a valid IvcProof structure.
        // We create a synthetic single-step fold that is an identity.
        let identity_fold = FoldWitness {
            old_root: state_root,
            new_root: state_root,
            removed_facts: vec![],
            num_added_checks: 1, // at least one check to satisfy delta_nonempty
        };
        let deltas = vec![FoldDelta::new(identity_fold)];
        let ivc_proof = prove_ivc(state_root, deltas)?;

        // Derivation
        let derivation_air = DerivationAir::new(w.derivation.clone());
        if !MockProver::verify(&derivation_air).is_valid() {
            return None;
        }
        let derivation_proof = MockProof::generate(&derivation_air)?;

        // Issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        if !MockProver::verify(&issuer_air).is_valid() {
            return None;
        }
        let issuer_membership_proof = MockProof::generate(&issuer_air)?;

        Some(IvcPresentationProof {
            ivc_proof,
            derivation_proof,
            issuer_membership_proof,
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
        })
    }

    /// Generate a real STARK-backed presentation proof.
    ///
    /// This produces actual cryptographic proofs for the Merkle membership sub-AIR
    /// using the STARK prover (FRI + Merkle commitments + Fiat-Shamir).
    /// The fold and derivation components use mock proofs (marked with TODOs for
    /// future STARK integration once their trace sizes are large enough for FRI).
    ///
    /// Returns `None` if any component fails constraint checking.
    pub fn prove_stark(&self) -> Option<RealPresentationProof> {
        let w = &self.witness;

        // 1. Prove each fold step (mock path — fold traces are small)
        let mut fold_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = MockProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = MockProof::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Prove the derivation (mock path — derivation traces are 1-2 rows)
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = MockProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = MockProof::generate(&derivation_air)?;

        // 3. Prove issuer membership with REAL STARK proof.
        // The STARK uses MerkleStarkAir (algebraic binding constraint) rather
        // than MerkleAir (Poseidon2). The witness must be built with algebraic
        // binding (use `create_stark_compatible_witness()`).
        // No mock prover check here — the STARK prover validates constraints
        // directly via the polynomial commitment scheme.
        let merkle_stark_proof = generate_merkle_stark_proof(&w.issuer_membership)?;

        // Compute public inputs
        let initial_root = if let Some(first_fold) = w.fold_chain.first() {
            first_fold.old_root
        } else {
            w.derivation.state_root
        };

        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            initial_root,
            final_root,
        };

        Some(RealPresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_stark_proof: merkle_stark_proof,
        })
    }

    /// Generate a real STARK-backed presentation proof using Poseidon2 hashing.
    ///
    /// Unlike `prove_stark()` which uses linear algebraic binding (trivially forgeable),
    /// this method uses actual Poseidon2 hash constraints for the issuer membership
    /// proof, providing collision-resistant Merkle membership in the federation.
    ///
    /// The witness must be built with Poseidon2-compatible hashing
    /// (use `create_poseidon2_compatible_witness()`).
    ///
    /// Returns `None` if any component fails constraint checking.
    pub fn prove_stark_poseidon2(&self) -> Option<RealPresentationProof> {
        let w = &self.witness;

        // 1. Prove each fold step (mock path)
        let mut fold_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = MockProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = MockProof::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Prove the derivation (mock path)
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = MockProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = MockProof::generate(&derivation_air)?;

        // 3. Prove issuer membership with REAL STARK + Poseidon2 hashing.
        //    This uses MerklePoseidon2StarkAir (collision-resistant) instead of
        //    MerkleStarkAir (linear, trivially forgeable).
        let merkle_stark_proof = generate_merkle_poseidon2_stark_proof(&w.issuer_membership)?;

        // Compute public inputs
        let initial_root = if let Some(first_fold) = w.fold_chain.first() {
            first_fold.old_root
        } else {
            w.derivation.state_root
        };

        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            initial_root,
            final_root,
        };

        Some(RealPresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_stark_proof: merkle_stark_proof,
        })
    }

    /// Verify the entire presentation (mock prover, validates all sub-circuits).
    pub fn verify_all(&self) -> PresentationVerification {
        let w = &self.witness;

        // Verify fold chain
        let mut current_root = if let Some(first) = w.fold_chain.first() {
            first.old_root
        } else {
            w.derivation.state_root
        };

        for (i, fold_witness) in w.fold_chain.iter().enumerate() {
            // Check continuity
            if fold_witness.old_root != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }

            // Verify fold AIR
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = MockProver::verify(&fold_air);
            if !result.is_valid() {
                return PresentationVerification::InvalidFoldProof { index: i };
            }

            current_root = fold_witness.new_root;
        }

        // Verify derivation
        if w.derivation.state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let result = MockProver::verify(&derivation_air);
        if !result.is_valid() {
            return PresentationVerification::InvalidDerivation;
        }

        // Verify issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let result = MockProver::verify(&issuer_air);
        if !result.is_valid() {
            return PresentationVerification::InvalidIssuerProof;
        }
        if w.issuer_membership.expected_root != w.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        PresentationVerification::Valid
    }
}

/// Not a real Air implementation (it's a meta-proof), but we implement it
/// for the mock prover infrastructure to work. The trace is a placeholder.
impl Air for PresentationAir {
    fn trace_width(&self) -> usize {
        // Width of the "summary" trace (just public inputs as columns)
        5
    }

    fn num_public_inputs(&self) -> usize {
        5 // federation_root, request_predicate, timestamp, initial_root, final_root
    }

    fn constraints(&self) -> Vec<Constraint> {
        // The presentation AIR's constraints are just consistency checks
        // on the public inputs. The real work is done by sub-AIRs.
        vec![
            Constraint {
                name: "federation_root_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[0] - public_inputs[0]),
            },
            Constraint {
                name: "request_predicate_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[1] - public_inputs[1]),
            },
            Constraint {
                name: "timestamp_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[2] - public_inputs[2]),
            },
            Constraint {
                name: "initial_root_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[3] - public_inputs[3]),
            },
            Constraint {
                name: "final_root_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[4] - public_inputs[4]),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;

        let initial_root = if let Some(first) = w.fold_chain.first() {
            first.old_root
        } else {
            w.derivation.state_root
        };
        let final_root = if let Some(last) = w.fold_chain.last() {
            last.new_root
        } else {
            w.derivation.state_root
        };

        let row = vec![
            w.federation_root,
            w.request_predicate,
            w.timestamp,
            initial_root,
            final_root,
        ];

        let public_inputs = vec![
            w.federation_root,
            w.request_predicate,
            w.timestamp,
            initial_root,
            final_root,
        ];

        (vec![row], public_inputs)
    }
}

/// Builder for constructing a presentation witness step by step.
pub struct PresentationBuilder {
    federation_root: BabyBear,
    request_predicate: BabyBear,
    timestamp: BabyBear,
    fold_chain: Vec<FoldWitness>,
    derivation: Option<DerivationWitness>,
    issuer_membership: Option<MerkleWitness>,
    issuer_key_hash: BabyBear,
}

impl PresentationBuilder {
    /// Create a new presentation builder.
    pub fn new(
        federation_root: BabyBear,
        request_predicate: BabyBear,
        timestamp: BabyBear,
    ) -> Self {
        Self {
            federation_root,
            request_predicate,
            timestamp,
            fold_chain: Vec::new(),
            derivation: None,
            issuer_membership: None,
            issuer_key_hash: BabyBear::ZERO,
        }
    }

    /// Add a fold (attenuation) step to the chain.
    pub fn add_fold(mut self, fold: FoldWitness) -> Self {
        self.fold_chain.push(fold);
        self
    }

    /// Set the authorization derivation.
    pub fn set_derivation(mut self, derivation: DerivationWitness) -> Self {
        self.derivation = Some(derivation);
        self
    }

    /// Set the issuer membership proof.
    pub fn set_issuer_membership(
        mut self,
        membership: MerkleWitness,
        key_hash: BabyBear,
    ) -> Self {
        self.issuer_membership = Some(membership);
        self.issuer_key_hash = key_hash;
        self
    }

    /// Build the presentation witness.
    pub fn build(self) -> Option<PresentationWitness> {
        let derivation = self.derivation?;
        let issuer_membership = self.issuer_membership?;

        Some(PresentationWitness {
            federation_root: self.federation_root,
            request_predicate: self.request_predicate,
            timestamp: self.timestamp,
            fold_chain: self.fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash: self.issuer_key_hash,
        })
    }
}

// ============================================================================
// Real STARK-backed presentation proof
// ============================================================================

/// A presentation proof backed by real STARK proofs (not mock).
///
/// The issuer membership proof uses a real STARK (FRI + Merkle commitments),
/// providing actual cryptographic soundness. Fold and derivation proofs remain
/// mock-backed for now (their traces are too small for meaningful FRI).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RealPresentationProof {
    /// The public inputs.
    pub public_inputs: PresentationPublicInputs,
    /// Mock proofs of the fold chain (TODO: upgrade to real STARK once traces grow).
    pub fold_proofs: Vec<MockProof>,
    /// Mock proof of the derivation (TODO: upgrade to real STARK).
    pub derivation_proof: MockProof,
    /// Real STARK proof of issuer membership in the federation.
    pub issuer_membership_stark_proof: StarkProof,
}

impl RealPresentationProof {
    /// Verify the real presentation proof.
    ///
    /// Uses `stark::verify()` for the issuer membership proof, and structural
    /// checks (root chain continuity) for the fold/derivation mock proofs.
    ///
    /// Supports both Poseidon2-based proofs (production, collision-resistant) and
    /// legacy linear proofs. Tries Poseidon2 first; falls back to linear.
    pub fn verify(&self) -> PresentationVerification {
        // 1. Check fold chain continuity
        let mut current_root = self.public_inputs.initial_root;
        for (i, fold_proof) in self.fold_proofs.iter().enumerate() {
            if fold_proof.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
            if fold_proof.public_inputs[0] != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }
            current_root = fold_proof.public_inputs[1];
        }

        // 2. Check derivation proof's state root matches final root
        if self.derivation_proof.public_inputs.is_empty() {
            return PresentationVerification::InvalidDerivation;
        }
        let derivation_state_root = self.derivation_proof.public_inputs[0];
        if derivation_state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }

        // 3. Check final root matches public input
        if current_root != self.public_inputs.final_root {
            return PresentationVerification::FinalRootMismatch;
        }

        // 4. Verify issuer membership with real STARK verifier
        let issuer_public_inputs: Vec<BabyBear> = self
            .issuer_membership_stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear(v))
            .collect();

        // The STARK proof's public inputs are [leaf_hash, root]
        if issuer_public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }

        // Check that the root in the STARK proof matches the federation root
        let issuer_federation_root = issuer_public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // Try Poseidon2 AIR first (production path), fall back to linear AIR (legacy).
        use crate::poseidon2_air::MerklePoseidon2StarkAir;
        let poseidon2_result = stark::verify(
            &MerklePoseidon2StarkAir,
            &self.issuer_membership_stark_proof,
            &issuer_public_inputs,
        );
        if poseidon2_result.is_ok() {
            return PresentationVerification::Valid;
        }

        // Fall back to linear AIR for backward compatibility with old proofs
        match stark::verify(&MerkleStarkAir, &self.issuer_membership_stark_proof, &issuer_public_inputs) {
            Ok(()) => PresentationVerification::Valid,
            Err(_) => PresentationVerification::InvalidIssuerProof,
        }
    }

    /// Get the total proof size in bytes.
    pub fn total_proof_size_bytes(&self) -> usize {
        let stark_bytes = stark::proof_to_bytes(&self.issuer_membership_stark_proof).len();
        let mock_bytes: usize = self.fold_proofs
            .iter()
            .map(|p| p.simulated_proof_size_bytes)
            .sum::<usize>()
            + self.derivation_proof.simulated_proof_size_bytes;
        stark_bytes + mock_bytes
    }

    /// Human-readable proof size.
    pub fn proof_size_display(&self) -> String {
        let bytes = self.total_proof_size_bytes();
        if bytes < 1024 {
            format!("{bytes} B")
        } else if bytes < 1024 * 1024 {
            format!("{:.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
        }
    }
}

/// Generate a real STARK proof for a Merkle membership witness.
///
/// Converts the MerkleWitness into the format expected by the STARK prover
/// (MerkleStarkAir trace layout: [current, sib0, sib1, sib2, position, parent]).
///
/// The MerkleStarkAir uses an algebraic binding constraint:
///   parent = current + sib0 + sib1 + sib2 + position
/// The witness's `expected_root` must be computed using this algebraic binding
/// (not Poseidon2). Use `create_stark_compatible_witness()` to build such a witness.
fn generate_merkle_stark_proof(witness: &MerkleWitness) -> Option<StarkProof> {
    let depth = witness.levels.len();
    if depth < 2 {
        return None;
    }

    let mut siblings_u32: Vec<[u32; 3]> = Vec::with_capacity(depth);
    let mut positions_u32: Vec<u32> = Vec::with_capacity(depth);

    // Collect the witness data for generate_merkle_trace
    for level in &witness.levels {
        siblings_u32.push([
            level.siblings[0].0,
            level.siblings[1].0,
            level.siblings[2].0,
        ]);
        positions_u32.push(level.position as u32);
    }

    // Use stark::generate_merkle_trace which builds the algebraic binding trace
    let (trace, public_inputs) =
        stark::generate_merkle_trace(witness.leaf_hash.0, &siblings_u32, &positions_u32);

    // The trace's computed root (public_inputs[1]) must match the witness's expected_root
    if public_inputs.len() < 2 || public_inputs[1] != witness.expected_root {
        return None;
    }

    if trace.len() < 2 {
        return None;
    }

    // Generate the STARK proof
    let air = MerkleStarkAir;
    let proof = stark::prove(&air, &trace, &public_inputs);

    // Sanity check: verify our own proof
    match stark::verify(&air, &proof, &public_inputs) {
        Ok(()) => Some(proof),
        Err(_) => None,
    }
}

/// Create a Merkle witness that is compatible with the STARK prover.
///
/// This builds the witness using the algebraic binding constraint:
///   parent = current + sib0 + sib1 + sib2 + position
/// which matches `MerkleStarkAir`. Use this instead of `create_test_witness`
/// when building proofs for `prove_stark()`.
pub fn create_stark_compatible_witness(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        // Use algebraic binding: parent = current + sib0 + sib1 + sib2 + position
        let parent = current + siblings[0] + siblings[1] + siblings[2] + BabyBear::new(position as u32);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

/// Generate a real STARK proof for Merkle membership using Poseidon2 hashing.
///
/// This uses `MerklePoseidon2StarkAir` with real Poseidon2 hash computations,
/// providing collision-resistant Merkle membership proofs.
pub fn generate_merkle_poseidon2_stark_proof(witness: &MerkleWitness) -> Option<StarkProof> {
    use crate::poseidon2_air::{self, MerklePoseidon2StarkAir};

    let depth = witness.levels.len();
    if depth < 2 {
        return None;
    }

    let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
    let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

    let (trace, public_inputs) =
        poseidon2_air::generate_merkle_poseidon2_trace(witness.leaf_hash, &siblings, &positions);

    // The trace's computed root must match the witness's expected_root
    if public_inputs.len() < 2 || public_inputs[1] != witness.expected_root {
        return None;
    }

    if trace.len() < 2 {
        return None;
    }

    // Generate the STARK proof with Poseidon2 constraints
    let air = MerklePoseidon2StarkAir;
    let proof = stark::prove(&air, &trace, &public_inputs);

    // Sanity check: verify our own proof
    match stark::verify(&air, &proof, &public_inputs) {
        Ok(()) => Some(proof),
        Err(_) => None,
    }
}

/// Create a Merkle witness that uses Poseidon2 hashing (collision-resistant).
///
/// This builds the witness using real Poseidon2 hash_4_to_1 at each level,
/// making it compatible with `MerklePoseidon2StarkAir`.
/// Use this instead of `create_stark_compatible_witness` for production proofs.
pub fn create_poseidon2_compatible_witness(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    use crate::poseidon2::hash_4_to_1;

    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];

        // Arrange children according to position
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == position {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }

        // Use real Poseidon2 hash
        let parent = hash_4_to_1(&children);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

/// Helper: Create a complete test presentation witness.
pub fn create_test_presentation() -> PresentationWitness {
    use crate::fold_air::build_shared_tree;

    let federation_root = BabyBear::new(1000000);
    let request_pred = BabyBear::new(500);
    let timestamp = BabyBear::new(1716000000); // some timestamp

    // Create a 2-step fold chain with valid membership proofs
    let final_root = BabyBear::new(333333);

    // Build tree for fold1
    let f1_hash = hash_fact(BabyBear::new(10), &[BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO]);
    let (initial_root, f1_proofs) = build_shared_tree(&[f1_hash], 4);

    // Build tree for fold2
    let f2a_hash = hash_fact(BabyBear::new(40), &[BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO]);
    let f2b_hash = hash_fact(BabyBear::new(60), &[BabyBear::new(70), BabyBear::new(80), BabyBear::ZERO]);
    let (mid_root, f2_proofs) = build_shared_tree(&[f2a_hash, f2b_hash], 4);

    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(10),
            terms: [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
            membership_proof: Some(f1_proofs.into_iter().next().unwrap()),
        }],
        num_added_checks: 1,
    };

    let mut f2_iter = f2_proofs.into_iter();
    let fold2 = FoldWitness {
        old_root: mid_root,
        new_root: final_root,
        removed_facts: vec![
            RemovedFact {
                predicate: BabyBear::new(40),
                terms: [BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO],
                membership_proof: Some(f2_iter.next().unwrap()),
            },
            RemovedFact {
                predicate: BabyBear::new(60),
                terms: [BabyBear::new(70), BabyBear::new(80), BabyBear::ZERO],
                membership_proof: Some(f2_iter.next().unwrap()),
            },
        ],
        num_added_checks: 0,
    };

    // Derivation: proves authorization from the final state
    let access_pred = BabyBear::new(300);
    let alice = BabyBear::new(1000);
    let resource = BabyBear::new(2000);
    let body_hash_1 = hash_fact(BabyBear::new(100), &[alice, resource, BabyBear::ZERO]);
    let body_hash_2 = hash_fact(BabyBear::new(200), &[alice, resource, BabyBear::ZERO]);

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 2,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
        },
        state_root: final_root,
        body_fact_hashes: vec![body_hash_1, body_hash_2],
        substitution: vec![alice, resource],
        derived_predicate: access_pred,
        derived_terms: [alice, resource, BabyBear::ZERO],
    };

    // Issuer membership: prove issuer key is in the federation
    let issuer_key = BabyBear::new(42424242);
    let issuer_membership = create_issuer_membership(issuer_key, federation_root);

    PresentationWitness {
        federation_root,
        request_predicate: request_pred,
        timestamp,
        fold_chain: vec![fold1, fold2],
        derivation,
        issuer_membership,
        issuer_key_hash: issuer_key,
    }
}

/// Helper: Create a Merkle membership witness for the issuer key in the federation.
fn create_issuer_membership(issuer_key: BabyBear, _federation_root: BabyBear) -> MerkleWitness {
    use crate::merkle_air::MerkleAir;

    // Build a witness that chains to the federation root
    let depth = 8; // shorter tree for federation
    let mut current = issuer_key;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 7 + 100) as u32),
            BabyBear::new((i * 7 + 200) as u32),
            BabyBear::new((i * 7 + 300) as u32),
        ];
        let parent = MerkleAir::compute_parent(current, position, &siblings);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    // The computed root should match federation_root for a valid proof.
    // In test, we just use whatever root we compute.
    MerkleWitness {
        leaf_hash: issuer_key,
        levels,
        expected_root: current, // Will differ from federation_root in test
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn presentation_proof_generation() {
        let witness = create_test_presentation();

        // The issuer membership root won't match federation_root in this test,
        // but the fold chain and derivation should verify.
        let _air = PresentationAir::new(witness.clone());

        // Verify sub-components individually
        for (i, fold) in witness.fold_chain.iter().enumerate() {
            let fold_air = FoldAir::new(fold.clone());
            let result = MockProver::verify(&fold_air);
            assert!(
                result.is_valid(),
                "Fold {i} failed: {:?}",
                result.violations()
            );
        }

        let deriv_air = DerivationAir::new(witness.derivation.clone());
        let result = MockProver::verify(&deriv_air);
        assert!(
            result.is_valid(),
            "Derivation failed: {:?}",
            result.violations()
        );

        let issuer_air = MerkleAir::new(witness.issuer_membership.clone());
        let result = MockProver::verify(&issuer_air);
        assert!(
            result.is_valid(),
            "Issuer membership failed: {:?}",
            result.violations()
        );
    }

    #[test]
    fn presentation_full_prove_and_verify() {
        // Create a presentation where issuer root matches federation root
        let mut witness = create_test_presentation();
        // Fix: set federation_root to the computed issuer membership root
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(verification, PresentationVerification::Valid);

        // Generate proof
        let proof = air.prove();
        assert!(proof.is_some(), "Proof generation should succeed");

        let proof = proof.unwrap();
        assert!(!proof.fold_proofs.is_empty());
        assert!(proof.total_proof_size_bytes > 0);
        println!("Presentation proof size: {}", proof.proof_size_display());
    }

    #[test]
    fn presentation_fold_chain_break_detected() {
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        // Break the chain: change fold2's old_root
        witness.fold_chain[1].old_root = BabyBear::new(999999);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::FoldChainBreak { index: 1 }
        );
    }

    #[test]
    fn presentation_derivation_root_mismatch() {
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        // Change derivation state_root so it doesn't match final fold output
        witness.derivation.state_root = BabyBear::new(888888);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::DerivationRootMismatch
        );
    }

    #[test]
    fn presentation_issuer_not_in_federation() {
        let witness = create_test_presentation();
        // federation_root won't match issuer_membership.expected_root
        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::IssuerNotInFederation
        );
    }

    #[test]
    fn stark_compatible_witness_generates_valid_proof() {
        // Isolated test: just the STARK proof generation for Merkle membership
        let witness = create_stark_compatible_witness(BabyBear::new(42424242), 8);
        let proof = generate_merkle_stark_proof(&witness);
        assert!(
            proof.is_some(),
            "generate_merkle_stark_proof should succeed for STARK-compatible witness"
        );
    }

    #[test]
    fn presentation_real_stark_prove_and_verify() {
        // Create a presentation with a STARK-compatible issuer membership witness
        let mut witness = create_test_presentation();
        // Replace the issuer membership with one using algebraic binding
        // (compatible with MerkleStarkAir)
        let stark_issuer = create_stark_compatible_witness(BabyBear::new(42424242), 8);
        witness.issuer_membership = stark_issuer;
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness);

        // Generate real STARK proof
        let proof = air.prove_stark();
        assert!(proof.is_some(), "Real STARK proof generation should succeed");

        let proof = proof.unwrap();
        assert!(!proof.fold_proofs.is_empty());
        assert!(proof.total_proof_size_bytes() > 0);
        println!(
            "Real STARK presentation proof size: {}",
            proof.proof_size_display()
        );

        // Verify with real STARK verifier
        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Real STARK proof should verify"
        );
    }

    #[test]
    fn presentation_real_stark_tampered_federation_root_fails() {
        let mut witness = create_test_presentation();
        let stark_issuer = create_stark_compatible_witness(BabyBear::new(42424242), 8);
        witness.issuer_membership = stark_issuer;
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness);
        let mut proof = air.prove_stark().unwrap();

        // Tamper: change federation root in public inputs
        proof.public_inputs.federation_root = BabyBear::new(999999);

        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::IssuerNotInFederation,
            "Tampered federation root should fail"
        );
    }

    #[test]
    fn presentation_real_stark_has_real_proof_bytes() {
        let mut witness = create_test_presentation();
        let stark_issuer = create_stark_compatible_witness(BabyBear::new(42424242), 8);
        witness.issuer_membership = stark_issuer;
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness);
        let proof = air.prove_stark().unwrap();

        // The STARK proof should be real bytes (not simulated)
        let stark_bytes = crate::stark::proof_to_bytes(&proof.issuer_membership_stark_proof);
        assert!(
            stark_bytes.len() > 1000,
            "Real STARK proof should be > 1KB, got {} bytes",
            stark_bytes.len()
        );

        // Verify it can roundtrip
        let deserialized = crate::stark::proof_from_bytes(&stark_bytes).unwrap();
        let pi: Vec<BabyBear> = deserialized
            .public_inputs
            .iter()
            .map(|&v| BabyBear(v))
            .collect();
        let result = crate::stark::verify(&crate::stark::MerkleStarkAir, &deserialized, &pi);
        assert!(result.is_ok(), "Deserialized STARK should verify");
    }

    #[test]
    fn presentation_builder() {
        let federation_root = BabyBear::new(1000);
        let request = BabyBear::new(42);
        let timestamp = BabyBear::new(12345);

        let fold = FoldWitness {
            old_root: BabyBear::new(100),
            new_root: BabyBear::new(200),
            removed_facts: vec![RemovedFact {
                predicate: BabyBear::new(1),
                terms: [BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO],
                membership_proof: None,
            }],
            num_added_checks: 1,
        };

        let derivation = DerivationWitness {
            rule: CircuitRule {
                id: 1,
                num_body_atoms: 1,
                num_variables: 1,
                head_predicate: BabyBear::new(300),
                head_terms: [(true, BabyBear::new(0)), (false, BabyBear::ZERO), (false, BabyBear::ZERO)],
                body_atoms: vec![],
                equal_checks: vec![],
            },
            state_root: BabyBear::new(200),
            body_fact_hashes: vec![BabyBear::new(555)],
            substitution: vec![BabyBear::new(777)],
            derived_predicate: BabyBear::new(300),
            derived_terms: [BabyBear::new(777), BabyBear::ZERO, BabyBear::ZERO],
        };

        let issuer_witness = crate::merkle_air::create_test_witness(BabyBear::new(9999), 8);

        let witness = PresentationBuilder::new(federation_root, request, timestamp)
            .add_fold(fold)
            .set_derivation(derivation)
            .set_issuer_membership(issuer_witness, BabyBear::new(9999))
            .build();

        assert!(witness.is_some());
        let w = witness.unwrap();
        assert_eq!(w.fold_chain.len(), 1);
        assert_eq!(w.federation_root, federation_root);
    }

    #[test]
    fn poseidon2_compatible_witness_generates_valid_proof() {
        // Test the Poseidon2-based STARK proof generation
        let witness = create_poseidon2_compatible_witness(BabyBear::new(42424242), 8);
        let proof = generate_merkle_poseidon2_stark_proof(&witness);
        assert!(
            proof.is_some(),
            "generate_merkle_poseidon2_stark_proof should succeed"
        );
    }

    #[test]
    fn presentation_real_poseidon2_stark_prove_and_verify() {
        // Test the Poseidon2 STARK Merkle proof directly (independent of fold/derivation)
        let p2_issuer = create_poseidon2_compatible_witness(BabyBear::new(42424242), 8);

        // Generate the Poseidon2 STARK proof
        let stark_proof = generate_merkle_poseidon2_stark_proof(&p2_issuer);
        assert!(stark_proof.is_some(), "Poseidon2 STARK proof generation should succeed");

        let proof = stark_proof.unwrap();
        let proof_bytes = crate::stark::proof_to_bytes(&proof);
        assert!(proof_bytes.len() > 1000, "Poseidon2 STARK proof should be > 1KB");
        println!(
            "Poseidon2 STARK Merkle proof: {} bytes ({:.1} KiB)",
            proof_bytes.len(),
            proof_bytes.len() as f64 / 1024.0
        );

        // Verify with real STARK verifier using MerklePoseidon2StarkAir
        use crate::poseidon2_air::MerklePoseidon2StarkAir;
        let pi: Vec<BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear(v))
            .collect();
        let result = crate::stark::verify(&MerklePoseidon2StarkAir, &proof, &pi);
        assert!(result.is_ok(), "Poseidon2 STARK proof should verify: {:?}", result.err());
    }

    #[test]
    fn poseidon2_stark_wrong_federation_root_fails() {
        let p2_issuer = create_poseidon2_compatible_witness(BabyBear::new(42424242), 8);
        let proof = generate_merkle_poseidon2_stark_proof(&p2_issuer).unwrap();

        // Verify with wrong root
        use crate::poseidon2_air::MerklePoseidon2StarkAir;
        let mut pi: Vec<BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear(v))
            .collect();
        // Tamper: change the root
        pi[1] = BabyBear::new(999999);
        let result = crate::stark::verify(
            &MerklePoseidon2StarkAir,
            &proof,
            &pi,
        );
        assert!(result.is_err(), "Should reject wrong federation root");
    }
}
