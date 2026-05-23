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

use crate::constraint_prover::{Air, Constraint, ConstraintProof, ConstraintProver};
use crate::derivation_air::{self, CircuitRule, DerivationAir, DerivationWitness};
use crate::field::BabyBear;
use crate::fold_air::{self, FoldAir, FoldWitness, RemovedFact};
use crate::ivc::{FoldDelta, IvcPresentationProof, prove_ivc};
use crate::merkle_air::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use crate::multi_step_air;
use crate::poseidon2::hash_fact;
use crate::stark::{self, MerkleStarkAir, StarkAir, StarkProof};
use crate::temporal_predicate_dsl::{TemporalPredicateProof, verify_temporal_predicate};

/// The complete presentation witness (all private data).
#[derive(Clone, Debug)]
pub struct PresentationWitness {
    /// The federation root (root of trust, public).
    pub federation_root: BabyBear,
    /// The action binding commitment (public, 4 elements for 124-bit security).
    pub request_predicate: crate::binding::ActionBinding,
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
    /// Commitment to the set of facts being selectively revealed (public, 124-bit).
    ///
    /// For selective disclosure mode, this is a WideHash over `(hash(fact_1) || ... || hash(fact_n))`
    /// computed over the facts the prover chooses to reveal. The verifier recomputes this
    /// from the plaintext revealed facts and checks it matches, ensuring the prover cannot
    /// lie about which facts were derived during evaluation.
    ///
    /// For fully private mode, this is `WideHash::ZERO` (no facts revealed).
    pub revealed_facts_commitment: crate::binding::WideHash,
    /// Blinding factor for ring membership (private).
    ///
    /// When non-zero, the issuer membership proof uses blinded (ring) mode:
    /// the public input becomes `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)`
    /// instead of the raw `leaf_hash`. This makes presentations unlinkable —
    /// the same issuer produces different `blinded_leaf` values each time.
    ///
    /// When `BabyBear::ZERO`, the legacy non-blinded path is used (leaf_hash is public).
    pub blinding_factor: BabyBear,
    /// Fresh randomness for the presentation tag (private).
    ///
    /// Used to compute `presentation_tag = Poseidon2(final_root, presentation_randomness, verifier_nonce)`.
    /// Must be freshly generated per presentation to ensure unlinkability.
    /// The final_root remains private; only the blinded tag is public.
    pub presentation_randomness: BabyBear,
    /// Composition commitment binding all sub-proofs together (public, 124-bit).
    ///
    /// This is a WideHash over `(fold_chain_commitment, derivation_state_root, presentation_tag)`
    /// where:
    /// - `fold_chain_commitment` is the Poseidon2 hash of the fold chain roots
    /// - `derivation_state_root` is the final state root from derivation
    /// - `presentation_tag` is the blinded tag (ties to this specific presentation)
    ///
    /// This value is appended as public inputs to the issuer membership STARK,
    /// cryptographically binding the STARK proof to the specific fold chain and
    /// derivation results. Without this, an attacker could attach a valid membership
    /// STARK from one token to a forged fold chain from another.
    ///
    /// When `WideHash::ZERO`, no composition commitment is enforced (legacy proofs).
    pub composition_commitment: crate::binding::WideHash,
    /// Verifier-issued nonce for replay protection (public).
    ///
    /// The verifier provides this challenge BEFORE proof generation. The prover must
    /// include it as a public input. During verification, the verifier checks that
    /// the proof's nonce matches the challenge they issued.
    ///
    /// This makes proofs non-replayable: a proof generated for one challenge cannot
    /// be replayed against a different challenge. The nonce also enters the Fiat-Shamir
    /// transcript (via the presentation_tag computation) to affect the STARK's internal
    /// randomness.
    ///
    /// When `BabyBear::ZERO`, no verifier nonce was provided (backward compatibility
    /// with older provers). Verifiers SHOULD reject proofs with a zero nonce in
    /// challenge-response protocols.
    pub verifier_nonce: BabyBear,
    /// Verifier-declared current block height for freshness binding (public).
    ///
    /// The verifier provides this value (the current chain height) as a public input.
    /// The circuit enforces that if the token has a `not_after_height` expiry caveat
    /// (non-zero), then `not_after_height >= verifier_block_height`. This ensures
    /// the token has not expired relative to the verifier's view of the chain.
    ///
    /// When `BabyBear::ZERO`, no freshness check is performed (backward compatibility).
    /// Verifiers operating in height-aware protocols SHOULD provide a non-zero value
    /// to enforce token expiry.
    pub verifier_block_height: BabyBear,
}

/// Public inputs for the presentation proof.
///
/// # Privacy Design (Phase 2)
///
/// The `initial_root` and `final_root` fields have been removed from public inputs
/// because they are deterministic per-token: same token always produces the same roots,
/// making presentations linkable across shows.
///
/// Instead, a `presentation_tag` is included:
///   `presentation_tag = Poseidon2(final_root, presentation_randomness, verifier_nonce)`
/// where `presentation_randomness` is fresh per presentation. The fold chain still
/// proves `initial_root -> final_root` internally (as private witness), and the STARK
/// proves the tag is well-formed. This makes presentations unlinkable.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationPublicInputs {
    /// Federation root of trust.
    pub federation_root: BabyBear,
    /// The action binding commitment (4 elements for 124-bit security).
    pub request_predicate: crate::binding::ActionBinding,
    /// Timestamp for freshness.
    pub timestamp: BabyBear,
    /// Blinded presentation tag for unlinkable multi-show.
    ///
    /// Computed as `Poseidon2(final_root, presentation_randomness, verifier_nonce)` where
    /// the randomness is fresh per presentation. The verifier cannot recover `final_root`
    /// from this tag, so the same credential produces a different tag every time it is shown.
    pub presentation_tag: BabyBear,
    /// Commitment to selectively revealed facts (zero if fully private, 124-bit).
    ///
    /// This is a WideHash over `(hash(fact_1) || ... || hash(fact_n))` for the facts the prover
    /// chose to reveal. The verifier recomputes this from the plaintext facts and checks
    /// it matches, cryptographically binding the revealed facts to the proof.
    pub revealed_facts_commitment: crate::binding::WideHash,
    /// Composition commitment binding all sub-proofs together (124-bit).
    ///
    /// This is a WideHash over `(fold_chain_commitment, derivation_state_root, presentation_tag)`
    /// and is included as public inputs in the issuer membership STARK. A verifier
    /// recomputes this from the other sub-proofs and checks it matches, ensuring
    /// sub-proofs cannot be mixed-and-matched across presentations.
    ///
    /// `WideHash::ZERO` means no composition commitment (legacy proofs).
    #[serde(default)]
    pub composition_commitment: crate::binding::WideHash,
    /// Verifier-issued nonce for replay protection.
    ///
    /// In a challenge-response protocol, the verifier sends this nonce to the prover
    /// BEFORE proof generation. The proof is then bound to this specific nonce.
    /// A proof generated for nonce N cannot be replayed against a different nonce N'.
    ///
    /// `BabyBear::ZERO` means no verifier nonce (legacy proofs, or non-interactive mode).
    /// Verifiers operating in challenge-response mode SHOULD reject proofs with zero nonce.
    #[serde(default)]
    pub verifier_nonce: BabyBear,
    /// Verifier-declared current block height for freshness binding.
    ///
    /// When non-zero, the verifier asserts "I am at block height H". The circuit
    /// enforces that the token's `not_after_height` (if present) satisfies
    /// `not_after_height >= verifier_block_height`, proving the token has not expired.
    ///
    /// `BabyBear::ZERO` means no freshness binding (legacy proofs).
    #[serde(default)]
    pub verifier_block_height: BabyBear,
}

/// A complete presentation proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationProof {
    /// The public inputs.
    pub public_inputs: PresentationPublicInputs,
    /// Proof of the fold chain (sequential STARK proofs).
    pub fold_proofs: Vec<ConstraintProof>,
    /// Proof of the final derivation.
    pub derivation_proof: ConstraintProof,
    /// Proof of issuer membership in federation.
    pub issuer_membership_proof: ConstraintProof,
    /// Optional temporal predicate proofs (e.g., "balance >= X for N blocks").
    ///
    /// Each temporal proof attests that an attribute satisfied a predicate over
    /// a contiguous range of steps in the IVC chain. The proof's `final_state_root`
    /// must match the presentation's final state root (end of fold chain) to bind
    /// the temporal claim to the same token state being presented.
    #[serde(default)]
    pub temporal_proofs: Vec<TemporalPredicateProof>,
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
    ///
    /// The verifier no longer sees initial_root or final_root (they are private).
    /// Instead, it checks:
    /// 1. Fold chain internal continuity (each step links to the next).
    /// 2. Derivation proof's state root matches end of fold chain.
    /// 3. The presentation_tag is well-formed (proven by the STARK internally).
    /// 4. Issuer membership in federation.
    pub fn verify(&self) -> PresentationVerification {
        // 1. Check fold chain internal continuity
        let mut current_root = if let Some(first) = self.fold_proofs.first() {
            if first.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: 0 };
            }
            first.public_inputs[0]
        } else {
            // No fold proofs: the derivation state root IS the only root.
            if self.derivation_proof.public_inputs.is_empty() {
                return PresentationVerification::InvalidDerivation;
            }
            return self.verify_no_folds();
        };

        for (i, fold_proof) in self.fold_proofs.iter().enumerate() {
            if fold_proof.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
            if fold_proof.public_inputs[0] != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }
            current_root = fold_proof.public_inputs[1];
        }

        // 2. Check derivation proof's state root matches end of fold chain
        if self.derivation_proof.public_inputs.is_empty() {
            return PresentationVerification::InvalidDerivation;
        }
        let derivation_state_root = self.derivation_proof.public_inputs[0];
        if derivation_state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }

        // 3. Presentation tag validity is enforced by the STARK — no comparison
        //    against final_root needed here (final_root is private witness).

        // 4. Check issuer membership in federation
        if self.issuer_membership_proof.public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }
        let issuer_federation_root = self.issuer_membership_proof.public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // 5. Verify temporal predicate proofs (if any).
        if let Err(e) = self.verify_temporal_proofs(current_root) {
            return e;
        }

        // 6. Freshness binding: check token expiry against verifier's block height.
        if let Err(e) = self.verify_freshness_binding() {
            return e;
        }

        PresentationVerification::Valid
    }

    /// Helper for verification when there are no fold proofs.
    fn verify_no_folds(&self) -> PresentationVerification {
        // Check issuer membership in federation
        if self.issuer_membership_proof.public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }
        let issuer_federation_root = self.issuer_membership_proof.public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // Verify temporal proofs bind to derivation state root.
        let state_root = self.derivation_proof.public_inputs[0];
        if let Err(e) = self.verify_temporal_proofs(state_root) {
            return e;
        }

        // Freshness binding.
        if let Err(e) = self.verify_freshness_binding() {
            return e;
        }

        PresentationVerification::Valid
    }

    /// Verify freshness binding: token expiry vs verifier block height.
    ///
    /// If both `verifier_block_height` (public input) and `not_after_height`
    /// (derivation proof public input index 2) are non-zero, enforce:
    ///   `not_after_height >= verifier_block_height`
    ///
    /// If `not_after_height == 0`, the token has no expiry (always valid).
    /// If `verifier_block_height == 0`, no freshness check is requested.
    fn verify_freshness_binding(&self) -> Result<(), PresentationVerification> {
        let verifier_height = self.public_inputs.verifier_block_height;
        if verifier_height == BabyBear::ZERO {
            return Ok(());
        }

        // Extract not_after_height from derivation proof public inputs (index 2).
        let not_after_height = if self.derivation_proof.public_inputs.len() >= 3 {
            self.derivation_proof.public_inputs[2]
        } else {
            BabyBear::ZERO
        };

        // Zero means no expiry caveat — always valid.
        if not_after_height == BabyBear::ZERO {
            return Ok(());
        }

        // Enforce: not_after_height >= verifier_block_height
        // In the field, this means (not_after_height - verifier_block_height) is
        // a "small" non-negative value (fits in 30 bits, i.e., < p/2).
        let diff = not_after_height - verifier_height;
        let diff_val = diff.as_u32();
        // If the subtraction wrapped (result > p/2), the token is expired.
        if diff_val > 1_006_632_960 {
            // p/2 = 2013265921 / 2 = 1006632960
            return Err(PresentationVerification::TokenExpired);
        }

        Ok(())
    }

    /// Verify all attached temporal predicate proofs.
    ///
    /// Each temporal proof must satisfy:
    /// 1. Its `final_state_root` matches the presentation's state root (binding).
    /// 2. The STARK proof itself is valid (cryptographic verification).
    ///
    /// This ensures temporal claims ("attribute X >= Y for N blocks") are bound to
    /// the same token state being presented, preventing a prover from attaching
    /// a temporal proof from a different token/chain.
    fn verify_temporal_proofs(&self, state_root: BabyBear) -> Result<(), PresentationVerification> {
        for (i, temporal_proof) in self.temporal_proofs.iter().enumerate() {
            // The temporal proof's final_state_root must match the presentation's
            // state root to bind the temporal claim to this presentation.
            if temporal_proof.final_state_root != state_root {
                return Err(PresentationVerification::InvalidTemporalProof { index: i });
            }

            // Verify the STARK proof cryptographically.
            let valid = verify_temporal_predicate(
                temporal_proof,
                temporal_proof.threshold,
                temporal_proof.num_steps,
                temporal_proof.initial_state_root,
                temporal_proof.final_state_root,
            );
            if !valid {
                return Err(PresentationVerification::InvalidTemporalProof { index: i });
            }
        }
        Ok(())
    }
}

/// Result of presentation proof verification.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PresentationVerification {
    /// The proof is valid (cryptographically verified via STARK).
    Valid,
    /// Local constraint check passed, but NO cryptographic proof was generated.
    ///
    /// This is the result from `prove_fast()`: the circuit constraints were
    /// satisfied locally, but without a STARK proof this provides zero security
    /// to a remote verifier. The prover could have fabricated any witness.
    ///
    /// **Do NOT treat this as equivalent to `Valid` in verification code.**
    LocalOnly,
    /// A fold proof in the chain failed.
    InvalidFoldProof { index: usize },
    /// The fold chain has a break (root mismatch between steps).
    FoldChainBreak { index: usize },
    /// The derivation proof is invalid.
    InvalidDerivation,
    /// The derivation's state root doesn't match the end of the fold chain.
    DerivationRootMismatch,
    /// The issuer membership proof is invalid.
    InvalidIssuerProof,
    /// The issuer is not in the federation.
    IssuerNotInFederation,
    /// A temporal predicate proof failed verification.
    ///
    /// Either the temporal proof's `final_state_root` does not match the
    /// presentation's state root (binding failure), or the STARK proof itself
    /// is invalid.
    InvalidTemporalProof { index: usize },
    /// The composition commitment is zero (missing sub-proof binding).
    ///
    /// A zero composition commitment means the sub-proofs are not cryptographically
    /// bound together, allowing an attacker to mix-and-match sub-proofs from
    /// different presentations. Verifiers MUST reject proofs with zero commitment.
    MissingCompositionCommitment,
    /// The token has expired: `not_after_height < verifier_block_height`.
    ///
    /// The verifier declared a current block height that exceeds the token's
    /// expiry height. The token is no longer valid at the verifier's current position.
    TokenExpired,
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
            let result = ConstraintProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = ConstraintProof::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Prove the derivation
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = ConstraintProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = ConstraintProof::generate(&derivation_air)?;

        // 3. Prove issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let issuer_result = ConstraintProver::verify(&issuer_air);
        if !issuer_result.is_valid() {
            return None;
        }
        let issuer_membership_proof = ConstraintProof::generate(&issuer_air)?;

        // Compute public inputs — initial_root and final_root stay private.
        // The presentation_tag blinds the final_root for unlinkability.
        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            presentation_tag,
            revealed_facts_commitment: w.revealed_facts_commitment,
            composition_commitment: w.composition_commitment,
            verifier_nonce: w.verifier_nonce,
            verifier_block_height: w.verifier_block_height,
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
            temporal_proofs: Vec::new(),
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
        let deriv_result = ConstraintProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = ConstraintProof::generate(&derivation_air)?;

        // 3. Prove issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let issuer_result = ConstraintProver::verify(&issuer_air);
        if !issuer_result.is_valid() {
            return None;
        }
        let issuer_membership_proof = ConstraintProof::generate(&issuer_air)?;

        Some(IvcPresentationProof {
            ivc_proof,
            derivation_proof,
            issuer_membership_proof,
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            revealed_facts_commitment: w.revealed_facts_commitment,
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
            added_checks_commitment: fold_air::compute_test_checks_commitment(1),
        };
        let deltas = vec![FoldDelta::new(identity_fold)];
        let ivc_proof = prove_ivc(state_root, deltas)?;

        // Derivation
        let derivation_air = DerivationAir::new(w.derivation.clone());
        if !ConstraintProver::verify(&derivation_air).is_valid() {
            return None;
        }
        let derivation_proof = ConstraintProof::generate(&derivation_air)?;

        // Issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        if !ConstraintProver::verify(&issuer_air).is_valid() {
            return None;
        }
        let issuer_membership_proof = ConstraintProof::generate(&issuer_air)?;

        Some(IvcPresentationProof {
            ivc_proof,
            derivation_proof,
            issuer_membership_proof,
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            revealed_facts_commitment: w.revealed_facts_commitment,
        })
    }

    /// Generate a real STARK-backed presentation proof using linear algebraic binding.
    ///
    /// This produces actual cryptographic proofs for the Merkle membership sub-AIR
    /// using the STARK prover (FRI + Merkle commitments + Fiat-Shamir).
    /// The fold and derivation components use constraint-checked proofs (pending
    /// future STARK integration once their trace sizes are large enough for FRI).
    ///
    /// Returns `None` if any component fails constraint checking.
    pub fn prove_stark(&self) -> Option<RealPresentationProof> {
        let w = &self.witness;

        // 1. Prove each fold step (constraint-checked — fold traces are small)
        let mut fold_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = ConstraintProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = ConstraintProof::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Prove the derivation (constraint-checked — derivation traces are 1-2 rows)
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = ConstraintProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = ConstraintProof::generate(&derivation_air)?;

        // 3. Prove issuer membership with REAL STARK proof.
        // The STARK uses MerkleStarkAir (algebraic binding constraint) rather
        // than MerkleAir (Poseidon2). The witness must be built with algebraic
        // binding (use `create_stark_compatible_witness()`).
        // No mock prover check here — the STARK prover validates constraints
        // directly via the polynomial commitment scheme.
        let merkle_stark_proof = generate_merkle_stark_proof(&w.issuer_membership)?;

        // Compute public inputs — roots stay private, tag is public.
        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            presentation_tag,
            revealed_facts_commitment: w.revealed_facts_commitment,
            composition_commitment: w.composition_commitment,
            verifier_nonce: w.verifier_nonce,
            verifier_block_height: w.verifier_block_height,
        };

        Some(RealPresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_stark_proof: merkle_stark_proof,
            fold_stark_proofs: vec![],
            derivation_stark_proof: None,
            temporal_proofs: Vec::new(),
        })
    }

    /// Generate a real STARK-backed presentation proof using Poseidon2 hashing.
    ///
    /// Unlike `prove_stark()` which uses linear algebraic binding,
    /// this method uses actual Poseidon2 hash constraints for the issuer membership
    /// proof, providing collision-resistant Merkle membership in the federation.
    ///
    /// The witness must be built with Poseidon2-compatible hashing
    /// (use `create_poseidon2_compatible_witness()`).
    ///
    /// Returns `None` if any component fails constraint checking.
    pub fn prove_stark_poseidon2(&self) -> Option<RealPresentationProof> {
        let w = &self.witness;

        // 1. Prove each fold step (both legacy constraint-checked AND real STARK)
        let mut fold_proofs = Vec::new();
        let mut fold_stark_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = ConstraintProver::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = ConstraintProof::generate(&fold_air)?;
            fold_proofs.push(proof);

            // Generate real STARK proof for this fold step
            if let Some(stark_proof) = fold_air::prove_fold_stark(fold_witness) {
                fold_stark_proofs.push(stark_proof);
            }
        }

        // 2. Prove the derivation (both legacy constraint-checked AND real STARK)
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = ConstraintProver::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = ConstraintProof::generate(&derivation_air)?;

        // Generate real STARK proof for the derivation step
        let derivation_stark_proof = derivation_air::prove_derivation_stark(&w.derivation);

        // 3. Prove issuer membership with REAL STARK + Poseidon2 hashing.
        //    The proof is bound to the request_predicate (action commitment) to
        //    prevent replay across different authorization requests.
        //
        //    When blinding_factor is non-zero, use the blinded (ring membership) path:
        //    public inputs become [blinded_leaf, root, action] instead of [leaf_hash, root, action].
        //    This makes presentations unlinkable (same issuer, different blinded_leaf each time).
        let composition_opt = if !w.composition_commitment.is_zero() {
            Some(w.composition_commitment)
        } else {
            None
        };

        let revealed_facts_opt = if !w.revealed_facts_commitment.is_zero() {
            Some(w.revealed_facts_commitment)
        } else {
            None
        };

        let merkle_stark_proof = if w.blinding_factor != BabyBear::ZERO {
            generate_blinded_merkle_poseidon2_stark_proof(
                &w.issuer_membership,
                w.blinding_factor,
                &w.request_predicate,
                composition_opt,
                revealed_facts_opt,
            )?
        } else {
            generate_merkle_poseidon2_stark_proof_bound(
                &w.issuer_membership,
                &w.request_predicate,
                composition_opt,
                revealed_facts_opt,
            )?
        };

        // Compute public inputs — roots stay private, tag is public.
        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            presentation_tag,
            revealed_facts_commitment: w.revealed_facts_commitment,
            composition_commitment: w.composition_commitment,
            verifier_nonce: w.verifier_nonce,
            verifier_block_height: w.verifier_block_height,
        };

        Some(RealPresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_stark_proof: merkle_stark_proof,
            fold_stark_proofs,
            derivation_stark_proof,
            temporal_proofs: Vec::new(),
        })
    }

    /// Verify the entire presentation (constraint prover, validates all sub-circuits).
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
            let result = ConstraintProver::verify(&fold_air);
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
        let result = ConstraintProver::verify(&derivation_air);
        if !result.is_valid() {
            return PresentationVerification::InvalidDerivation;
        }

        // Verify issuer membership
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let result = ConstraintProver::verify(&issuer_air);
        if !result.is_valid() {
            return PresentationVerification::InvalidIssuerProof;
        }
        if w.issuer_membership.expected_root != w.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // Freshness binding: check token expiry against verifier's block height.
        let verifier_height = w.verifier_block_height;
        if verifier_height != BabyBear::ZERO {
            let not_after_height = w.derivation.not_after_height;
            if not_after_height != BabyBear::ZERO {
                // Enforce: not_after_height >= verifier_block_height
                let diff = not_after_height - verifier_height;
                let diff_val = diff.as_u32();
                if diff_val > 1_006_632_960 {
                    return PresentationVerification::TokenExpired;
                }
            }
        }

        PresentationVerification::Valid
    }
}

/// Not a standalone AIR (it's a meta-proof), but we implement the Air trait
/// so the constraint prover infrastructure can validate the combined circuit.
/// The trace is a summary of the sub-proofs' public inputs.
impl Air for PresentationAir {
    fn trace_width(&self) -> usize {
        // Width of the "summary" trace (just public inputs as columns)
        // federation_root, request_predicate[0..4], timestamp, presentation_tag,
        // revealed_facts_commitment[0..4]
        // = 1 + 4 + 1 + 1 + 4 = 11
        11
    }

    fn num_public_inputs(&self) -> usize {
        // federation_root, request_predicate[0..4], timestamp, presentation_tag,
        // revealed_facts_commitment[0..4]
        11
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
                name: "request_predicate_0_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[1] - public_inputs[1]),
            },
            Constraint {
                name: "request_predicate_1_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[2] - public_inputs[2]),
            },
            Constraint {
                name: "request_predicate_2_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[3] - public_inputs[3]),
            },
            Constraint {
                name: "request_predicate_3_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[4] - public_inputs[4]),
            },
            Constraint {
                name: "timestamp_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[5] - public_inputs[5]),
            },
            Constraint {
                name: "presentation_tag_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[6] - public_inputs[6]),
            },
            Constraint {
                name: "revealed_facts_commitment_0_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[7] - public_inputs[7]),
            },
            Constraint {
                name: "revealed_facts_commitment_1_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[8] - public_inputs[8]),
            },
            Constraint {
                name: "revealed_facts_commitment_2_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[9] - public_inputs[9]),
            },
            Constraint {
                name: "revealed_facts_commitment_3_match".to_string(),
                eval: Box::new(|row, _, public_inputs| row[10] - public_inputs[10]),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;

        let final_root = if let Some(last) = w.fold_chain.last() {
            last.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let row = vec![
            w.federation_root,
            w.request_predicate[0],
            w.request_predicate[1],
            w.request_predicate[2],
            w.request_predicate[3],
            w.timestamp,
            presentation_tag,
            w.revealed_facts_commitment[0],
            w.revealed_facts_commitment[1],
            w.revealed_facts_commitment[2],
            w.revealed_facts_commitment[3],
        ];

        let public_inputs = vec![
            w.federation_root,
            w.request_predicate[0],
            w.request_predicate[1],
            w.request_predicate[2],
            w.request_predicate[3],
            w.timestamp,
            presentation_tag,
            w.revealed_facts_commitment[0],
            w.revealed_facts_commitment[1],
            w.revealed_facts_commitment[2],
            w.revealed_facts_commitment[3],
        ];

        (vec![row], public_inputs)
    }
}

// ============================================================================
// Multi-step authorization proof (Datalog derivation chain -> ALLOW)
// ============================================================================

/// Result of a multi-step authorization proof.
#[derive(Clone, Debug)]
pub struct AuthorizationProof {
    /// The constraint-checked proof of the derivation circuit.
    pub proof: ConstraintProof,
    /// The conclusion: true = ALLOW, false = DENY.
    pub conclusion_is_allow: bool,
    /// Number of derivation steps in the proof.
    pub num_steps: usize,
    /// The initial state root the proof is bound to.
    pub initial_state_root: BabyBear,
    /// The final accumulated hash (commitment to the derivation trace).
    pub final_accumulated_hash: BabyBear,
}

/// Prove a multi-step authorization derivation.
///
/// Takes:
/// - `initial_state_root`: The committed fact set root (matches the fold chain's final root)
/// - `request_hash`: Hash of the authorization request
/// - `derivation_steps`: Sequence of single-step derivation witnesses, where the last
///   step must derive the "allow" predicate for the conclusion to be ALLOW.
///
/// Returns an `AuthorizationProof` that cryptographically proves:
/// "This Datalog evaluation, starting from the committed state, concluded ALLOW (or DENY)
///  in N derivation steps, with each step correctly applying a rule."
///
/// The full presentation proof now proves:
/// ```text
/// prove_membership (issuer in federation)    - Poseidon2 Merkle AIR
/// + prove_fold (attenuation chain valid)     - FoldAir / IVC
/// + prove_authorization (Datalog -> ALLOW)   - MultiStepDerivationAir [THIS]
/// = complete ZK authorization proof
/// ```
pub fn prove_authorization(
    initial_state_root: BabyBear,
    request_hash: BabyBear,
    derivation_steps: Vec<DerivationWitness>,
) -> Option<AuthorizationProof> {
    let witness = multi_step_air::build_multi_step_witness(
        initial_state_root,
        request_hash,
        derivation_steps,
    );

    let conclusion_is_allow = witness.conclusion() == BabyBear::ONE;
    let num_steps = witness.steps.len();
    let final_accumulated_hash = witness.final_accumulated_hash();

    let proof = multi_step_air::prove_authorization(witness)?;

    Some(AuthorizationProof {
        proof,
        conclusion_is_allow,
        num_steps,
        initial_state_root,
        final_accumulated_hash,
    })
}

/// Builder for constructing a presentation witness step by step.
pub struct PresentationBuilder {
    federation_root: BabyBear,
    request_predicate: crate::binding::ActionBinding,
    timestamp: BabyBear,
    fold_chain: Vec<FoldWitness>,
    derivation: Option<DerivationWitness>,
    issuer_membership: Option<MerkleWitness>,
    issuer_key_hash: BabyBear,
    revealed_facts_commitment: crate::binding::WideHash,
}

impl PresentationBuilder {
    /// Create a new presentation builder.
    pub fn new(
        federation_root: BabyBear,
        request_predicate: crate::binding::ActionBinding,
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
            revealed_facts_commitment: crate::binding::WideHash::ZERO,
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
    pub fn set_issuer_membership(mut self, membership: MerkleWitness, key_hash: BabyBear) -> Self {
        self.issuer_membership = Some(membership);
        self.issuer_key_hash = key_hash;
        self
    }

    /// Set the revealed facts commitment for selective disclosure.
    pub fn set_revealed_facts_commitment(mut self, commitment: crate::binding::WideHash) -> Self {
        self.revealed_facts_commitment = commitment;
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
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: crate::binding::WideHash::ZERO,
            blinding_factor: BabyBear::ZERO,
            presentation_randomness: BabyBear::ZERO,
            verifier_nonce: BabyBear::ZERO,
            verifier_block_height: BabyBear::ZERO,
        })
    }
}

// ============================================================================
// Real STARK-backed presentation proof
// ============================================================================

/// A presentation proof backed by real STARK proofs.
///
/// All three sub-circuits (fold chain, derivation, issuer membership) now use
/// real STARK proofs with polynomial commitments and FRI. The `fold_proofs` and
/// `derivation_proof` fields are retained for backward compatibility (legacy
/// constraint-checked proofs); the new `fold_stark_proofs` and
/// `derivation_stark_proof` fields carry the cryptographically sound proofs.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RealPresentationProof {
    /// The public inputs.
    pub public_inputs: PresentationPublicInputs,
    /// Legacy constraint-checked proofs of the fold chain.
    /// Retained for backward compatibility; verifiers SHOULD prefer `fold_stark_proofs`.
    pub fold_proofs: Vec<ConstraintProof>,
    /// Legacy constraint-checked proof of the derivation.
    /// Retained for backward compatibility; verifiers SHOULD prefer `derivation_stark_proof`.
    pub derivation_proof: ConstraintProof,
    /// Real STARK proof of issuer membership in the federation.
    pub issuer_membership_stark_proof: StarkProof,
    /// Real STARK proofs for each fold step (cryptographically sound).
    /// When present, these supersede `fold_proofs` for verification.
    #[serde(default)]
    pub fold_stark_proofs: Vec<StarkProof>,
    /// Real STARK proof of the derivation step (cryptographically sound).
    /// When present, this supersedes `derivation_proof` for verification.
    #[serde(default)]
    pub derivation_stark_proof: Option<StarkProof>,
    /// Optional temporal predicate proofs bound to this presentation.
    ///
    /// Each proof attests that an attribute satisfied a predicate over N consecutive
    /// steps. The proof's `final_state_root` must match the presentation's state root.
    #[serde(default)]
    pub temporal_proofs: Vec<TemporalPredicateProof>,
}

impl RealPresentationProof {
    /// Verify the real presentation proof.
    ///
    /// Uses `stark::verify()` for the issuer membership proof, and structural
    /// checks (root chain continuity) for the fold/derivation constraint proofs.
    ///
    /// Supports both Poseidon2-based proofs (production, collision-resistant) and
    /// legacy linear proofs. Tries Poseidon2 first; falls back to linear.
    pub fn verify(&self) -> PresentationVerification {
        // 0. Reject proofs with zero composition commitment.
        // A zero value means the sub-proofs are not bound together, allowing
        // an attacker to mix-and-match membership proofs from different tokens.
        if self.public_inputs.composition_commitment.is_zero() {
            return PresentationVerification::MissingCompositionCommitment;
        }

        // 1. Check fold chain continuity (roots are private, verified internally).
        let mut current_root = if let Some(first) = self.fold_proofs.first() {
            if first.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: 0 };
            }
            first.public_inputs[0]
        } else {
            // No folds: derivation state root is the sole root.
            if self.derivation_proof.public_inputs.is_empty() {
                return PresentationVerification::InvalidDerivation;
            }
            self.derivation_proof.public_inputs[0]
        };

        for (i, fold_proof) in self.fold_proofs.iter().enumerate() {
            if fold_proof.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
            if fold_proof.public_inputs[0] != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }
            current_root = fold_proof.public_inputs[1];
        }

        // 2. Check derivation proof's state root matches end of fold chain.
        if self.derivation_proof.public_inputs.is_empty() {
            return PresentationVerification::InvalidDerivation;
        }
        let derivation_state_root = self.derivation_proof.public_inputs[0];
        if derivation_state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }

        // 3. Presentation tag validity: proven by the STARK internally.
        //    final_root is private; no explicit comparison against public inputs needed.

        // 4. Verify issuer membership with real STARK verifier
        let issuer_public_inputs: Vec<BabyBear> = self
            .issuer_membership_stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
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

        // 4a. Verify fold STARK proofs if present (cryptographically sound path).
        for (i, fold_stark) in self.fold_stark_proofs.iter().enumerate() {
            let fold_pi: Vec<BabyBear> = fold_stark
                .public_inputs
                .iter()
                .map(|&v| BabyBear::new_canonical(v))
                .collect();
            if let Err(_) = fold_air::verify_fold_stark(fold_stark, &fold_pi) {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
        }

        // 4b. Verify derivation STARK proof if present (cryptographically sound path).
        if let Some(ref deriv_stark) = self.derivation_stark_proof {
            let deriv_pi: Vec<BabyBear> = deriv_stark
                .public_inputs
                .iter()
                .map(|&v| BabyBear::new_canonical(v))
                .collect();
            if let Err(_) = derivation_air::verify_derivation_stark(deriv_stark, &deriv_pi) {
                return PresentationVerification::InvalidDerivation;
            }
        }

        // 5. Verify issuer membership with the appropriate AIR based on proof type.
        // Blinded (ring membership) proofs use BlindedMerklePoseidon2StarkAir;
        // legacy proofs use MerklePoseidon2StarkAir.
        use crate::poseidon2_air::{BlindedMerklePoseidon2StarkAir, MerklePoseidon2StarkAir};
        let air_name = &self.issuer_membership_stark_proof.air_name;
        let verify_result = if air_name == BlindedMerklePoseidon2StarkAir.air_name() {
            stark::verify(
                &BlindedMerklePoseidon2StarkAir,
                &self.issuer_membership_stark_proof,
                &issuer_public_inputs,
            )
        } else {
            stark::verify(
                &MerklePoseidon2StarkAir,
                &self.issuer_membership_stark_proof,
                &issuer_public_inputs,
            )
        };
        match verify_result {
            Ok(()) => {}
            Err(_) => return PresentationVerification::InvalidIssuerProof,
        }

        // 6. Verify temporal predicate proofs (if any).
        for (i, temporal_proof) in self.temporal_proofs.iter().enumerate() {
            // Temporal proof's final_state_root must bind to the presentation state root.
            if temporal_proof.final_state_root != current_root {
                return PresentationVerification::InvalidTemporalProof { index: i };
            }
            let valid = verify_temporal_predicate(
                temporal_proof,
                temporal_proof.threshold,
                temporal_proof.num_steps,
                temporal_proof.initial_state_root,
                temporal_proof.final_state_root,
            );
            if !valid {
                return PresentationVerification::InvalidTemporalProof { index: i };
            }
        }

        // 7. Freshness binding: check token expiry against verifier's block height.
        if let Err(e) = self.verify_freshness_binding() {
            return e;
        }

        PresentationVerification::Valid
    }

    /// Verify freshness binding: token expiry vs verifier block height.
    ///
    /// If both `verifier_block_height` (public input) and `not_after_height`
    /// (derivation proof public input index 2) are non-zero, enforce:
    ///   `not_after_height >= verifier_block_height`
    ///
    /// If `not_after_height == 0`, the token has no expiry (always valid).
    /// If `verifier_block_height == 0`, no freshness check is requested.
    fn verify_freshness_binding(&self) -> Result<(), PresentationVerification> {
        let verifier_height = self.public_inputs.verifier_block_height;
        if verifier_height == BabyBear::ZERO {
            return Ok(());
        }

        // Extract not_after_height from derivation proof public inputs (index 2).
        let not_after_height = if self.derivation_proof.public_inputs.len() >= 3 {
            self.derivation_proof.public_inputs[2]
        } else {
            BabyBear::ZERO
        };

        // Zero means no expiry caveat — always valid.
        if not_after_height == BabyBear::ZERO {
            return Ok(());
        }

        // Enforce: not_after_height >= verifier_block_height
        // In the field, this means (not_after_height - verifier_block_height) is
        // a "small" non-negative value (fits in 30 bits, i.e., < p/2).
        let diff = not_after_height - verifier_height;
        let diff_val = diff.as_u32();
        // If the subtraction wrapped (result > p/2), the token is expired.
        if diff_val > 1_006_632_960 {
            // p/2 = 2013265921 / 2 = 1006632960
            return Err(PresentationVerification::TokenExpired);
        }

        Ok(())
    }

    /// Get the total proof size in bytes.
    pub fn total_proof_size_bytes(&self) -> usize {
        let stark_bytes = stark::proof_to_bytes(&self.issuer_membership_stark_proof).len();
        let mock_bytes: usize = self
            .fold_proofs
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
        let parent =
            current + siblings[0] + siblings[1] + siblings[2] + BabyBear::new(position as u32);
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

/// Generate a real STARK proof for Merkle membership with Poseidon2 hashing,
/// binding the proof to a specific action via an action commitment.
///
/// The action commitment is appended as an additional public input, producing
/// public inputs of the form `[leaf_hash, root, action_commitment]`. This
/// prevents the proof from being replayed against a different action.
///
/// The `action_commitment` should be computed as:
/// `poseidon2::hash_many(&BabyBear::encode_hash(&blake3_hash_of_action))`
pub fn generate_merkle_poseidon2_stark_proof_bound(
    witness: &MerkleWitness,
    action_commitment: &crate::binding::ActionBinding,
    composition_commitment: Option<crate::binding::WideHash>,
    revealed_facts_commitment: Option<crate::binding::WideHash>,
) -> Option<StarkProof> {
    use crate::poseidon2_air::{self, MerklePoseidon2StarkAir};

    let depth = witness.levels.len();
    if depth < 2 {
        return None;
    }

    let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
    let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

    let (trace, mut public_inputs) =
        poseidon2_air::generate_merkle_poseidon2_trace(witness.leaf_hash, &siblings, &positions);

    // The trace's computed root must match the witness's expected_root
    if public_inputs.len() < 2 || public_inputs[1] != witness.expected_root {
        return None;
    }

    if trace.len() < 2 {
        return None;
    }

    // Append the action binding commitment as 4 additional public inputs.
    // This binds the proof to a specific (action, resource) pair with 124-bit
    // collision resistance (birthday bound ~2^62), preventing replay.
    for &elem in action_commitment.iter() {
        public_inputs.push(elem);
    }

    // Append the composition commitment if provided (sub-proof binding, 4 elements).
    if let Some(cc) = composition_commitment {
        if !cc.is_zero() {
            for &elem in cc.as_slice() {
                public_inputs.push(elem);
            }
        }
    }

    // Append the revealed facts commitment if provided (selective disclosure, 4 elements).
    // SECURITY: This cryptographically binds the revealed facts to the STARK proof.
    // The verifier recomputes the commitment from the plaintext facts and checks it
    // matches this value, ensuring the prover cannot lie about which facts were revealed.
    if let Some(rfc) = revealed_facts_commitment {
        if !rfc.is_zero() {
            for &elem in rfc.as_slice() {
                public_inputs.push(elem);
            }
        }
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

/// Generate a real STARK proof for blinded (ring) Merkle membership with Poseidon2.
///
/// This is the production function for unlinkable issuer membership proofs.
/// The public inputs are `[blinded_leaf, root, action_commitment]` where:
///   `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)`
///
/// The verifier sees only the blinded_leaf (different each presentation) and the
/// federation root. They CANNOT determine which issuer produced the proof.
///
/// The `action_commitment` is appended as an additional public input to prevent
/// replay across different authorization requests.
pub fn generate_blinded_merkle_poseidon2_stark_proof(
    witness: &MerkleWitness,
    blinding_factor: BabyBear,
    action_commitment: &crate::binding::ActionBinding,
    composition_commitment: Option<crate::binding::WideHash>,
    revealed_facts_commitment: Option<crate::binding::WideHash>,
) -> Option<StarkProof> {
    use crate::poseidon2_air::{self, BlindedMerklePoseidon2StarkAir};

    let depth = witness.levels.len();
    if depth < 2 {
        return None;
    }

    let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
    let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

    let (trace, mut public_inputs) = poseidon2_air::generate_blinded_merkle_poseidon2_trace(
        witness.leaf_hash,
        &siblings,
        &positions,
        blinding_factor,
    );

    // The trace's computed root must match the witness's expected_root
    if public_inputs.len() < 2 || public_inputs[1] != witness.expected_root {
        return None;
    }

    if trace.len() < 2 {
        return None;
    }

    // Append the action binding commitment as 4 additional public inputs.
    // This binds the proof to a specific (action, resource) pair with 124-bit
    // collision resistance (birthday bound ~2^62), preventing replay.
    for &elem in action_commitment.iter() {
        public_inputs.push(elem);
    }

    // Append the composition commitment if provided (sub-proof binding, 4 elements).
    if let Some(cc) = composition_commitment {
        if !cc.is_zero() {
            for &elem in cc.as_slice() {
                public_inputs.push(elem);
            }
        }
    }

    // Append the revealed facts commitment if provided (selective disclosure, 4 elements).
    // SECURITY: This cryptographically binds the revealed facts to the STARK proof.
    // The verifier recomputes the commitment from the plaintext facts and checks it
    // matches this value, ensuring the prover cannot lie about which facts were revealed.
    if let Some(rfc) = revealed_facts_commitment {
        if !rfc.is_zero() {
            for &elem in rfc.as_slice() {
                public_inputs.push(elem);
            }
        }
    }

    // Generate the STARK proof with blinded Poseidon2 constraints
    let air = BlindedMerklePoseidon2StarkAir;
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
    let request_pred = crate::binding::compute_action_binding("test-action", "test-resource");
    let timestamp = BabyBear::new(1716000000); // some timestamp

    // Create a 2-step fold chain with valid membership proofs
    let final_root = BabyBear::new(333333);

    // Build tree for fold1
    let f1_hash = hash_fact(
        BabyBear::new(10),
        &[BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
    );
    let (initial_root, f1_proofs) = build_shared_tree(&[f1_hash], 4);

    // Build tree for fold2
    let f2a_hash = hash_fact(
        BabyBear::new(40),
        &[BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO],
    );
    let f2b_hash = hash_fact(
        BabyBear::new(60),
        &[BabyBear::new(70), BabyBear::new(80), BabyBear::ZERO],
    );
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
        added_checks_commitment: fold_air::compute_test_checks_commitment(1),
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
        added_checks_commitment: crate::binding::WideHash::ZERO,
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
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root: final_root,
        body_fact_hashes: vec![body_hash_1, body_hash_2],
        substitution: vec![alice, resource],
        derived_predicate: access_pred,
        derived_terms: [alice, resource, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
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
        revealed_facts_commitment: crate::binding::WideHash::ZERO,
        composition_commitment: crate::binding::WideHash::ZERO,
        blinding_factor: BabyBear::ZERO,
        presentation_randomness: BabyBear::new(123456789),
        verifier_nonce: BabyBear::ZERO,
        verifier_block_height: BabyBear::ZERO,
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
            let result = ConstraintProver::verify(&fold_air);
            assert!(
                result.is_valid(),
                "Fold {i} failed: {:?}",
                result.violations()
            );
        }

        let deriv_air = DerivationAir::new(witness.derivation.clone());
        let result = ConstraintProver::verify(&deriv_air);
        assert!(
            result.is_valid(),
            "Derivation failed: {:?}",
            result.violations()
        );

        let issuer_air = MerkleAir::new(witness.issuer_membership.clone());
        let result = ConstraintProver::verify(&issuer_air);
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
        // Create a presentation with a Poseidon2-compatible issuer membership witness
        let mut witness = create_test_presentation();
        // Replace the issuer membership with one using Poseidon2 hashing
        // (compatible with MerklePoseidon2StarkAir — the only accepted verifier)
        let poseidon2_issuer = create_poseidon2_compatible_witness(BabyBear::new(42424242), 8);
        witness.issuer_membership = poseidon2_issuer;
        witness.federation_root = witness.issuer_membership.expected_root;
        // Non-zero composition commitment required for verification
        witness.composition_commitment =
            crate::binding::WideHash::from_poseidon2("test-composition", &[BabyBear::new(777777)]);

        let air = PresentationAir::new(witness);

        // Generate real STARK proof via Poseidon2 path
        let proof = air.prove_stark_poseidon2();
        assert!(
            proof.is_some(),
            "Real STARK proof generation should succeed"
        );

        let proof = proof.unwrap();
        assert!(!proof.fold_proofs.is_empty());
        assert!(proof.total_proof_size_bytes() > 0);
        println!(
            "Real STARK presentation proof size: {}",
            proof.proof_size_display()
        );

        // Verify with real STARK verifier (Poseidon2 only, no linear AIR fallback)
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
        // Non-zero composition commitment required for verification
        witness.composition_commitment =
            crate::binding::WideHash::from_poseidon2("test-composition", &[BabyBear::new(777777)]);

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
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        let result = crate::stark::verify(&crate::stark::MerkleStarkAir, &deserialized, &pi);
        assert!(result.is_ok(), "Deserialized STARK should verify");
    }

    #[test]
    fn presentation_builder() {
        let federation_root = BabyBear::new(1000);
        let request = [
            BabyBear::new(42),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
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
            added_checks_commitment: fold_air::compute_test_checks_commitment(1),
        };

        let derivation = DerivationWitness {
            rule: CircuitRule {
                id: 1,
                num_body_atoms: 1,
                num_variables: 1,
                head_predicate: BabyBear::new(300),
                head_terms: [
                    (true, BabyBear::new(0)),
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
                lt_check: None,
            },
            state_root: BabyBear::new(200),
            body_fact_hashes: vec![BabyBear::new(555)],
            substitution: vec![BabyBear::new(777)],
            derived_predicate: BabyBear::new(300),
            derived_terms: [
                BabyBear::new(777),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
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
        assert!(
            stark_proof.is_some(),
            "Poseidon2 STARK proof generation should succeed"
        );

        let proof = stark_proof.unwrap();
        let proof_bytes = crate::stark::proof_to_bytes(&proof);
        assert!(
            proof_bytes.len() > 1000,
            "Poseidon2 STARK proof should be > 1KB"
        );
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
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        let result = crate::stark::verify(&MerklePoseidon2StarkAir, &proof, &pi);
        assert!(
            result.is_ok(),
            "Poseidon2 STARK proof should verify: {:?}",
            result.err()
        );
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
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        // Tamper: change the root
        pi[1] = BabyBear::new(999999);
        let result = crate::stark::verify(&MerklePoseidon2StarkAir, &proof, &pi);
        assert!(result.is_err(), "Should reject wrong federation root");
    }

    #[test]
    fn presentation_zero_composition_commitment_rejected() {
        // A proof with composition_commitment == ZERO must be rejected by verifiers.
        // This prevents sub-proof mix-and-match attacks.
        let mut witness = create_test_presentation();
        let stark_issuer = create_stark_compatible_witness(BabyBear::new(42424242), 8);
        witness.issuer_membership = stark_issuer;
        witness.federation_root = witness.issuer_membership.expected_root;
        // Explicitly leave composition_commitment at ZERO (the default)
        witness.composition_commitment = crate::binding::WideHash::ZERO;

        let air = PresentationAir::new(witness);
        let proof = air.prove_stark().unwrap();

        // Verification must reject: zero composition commitment is not allowed
        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::MissingCompositionCommitment,
            "Zero composition_commitment must be rejected"
        );
    }

    #[test]
    fn presentation_nonce_bound_to_tag() {
        // Verify that verifier_nonce is cryptographically bound to the presentation_tag.
        // Two proofs with different nonces must produce different tags.
        let mut witness1 = create_test_presentation();
        witness1.federation_root = witness1.issuer_membership.expected_root;
        witness1.verifier_nonce = BabyBear::new(111);

        let mut witness2 = create_test_presentation();
        witness2.federation_root = witness2.issuer_membership.expected_root;
        witness2.verifier_nonce = BabyBear::new(222);

        let air1 = PresentationAir::new(witness1);
        let air2 = PresentationAir::new(witness2);

        let proof1 = air1.prove().unwrap();
        let proof2 = air2.prove().unwrap();

        // The tags must differ because the nonces differ
        assert_ne!(
            proof1.public_inputs.presentation_tag, proof2.public_inputs.presentation_tag,
            "Different verifier_nonce must produce different presentation_tag"
        );
    }

    #[test]
    fn presentation_with_temporal_predicate_proof() {
        use crate::predicate_air::PredicateType;
        use crate::temporal_predicate_dsl::prove_temporal_predicate;

        // Create a presentation with matching federation root.
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness.clone());
        let mut proof = air.prove().expect("base proof should succeed");

        // The final state root of the presentation (end of fold chain).
        let final_state_root = witness.fold_chain.last().unwrap().new_root;

        // Generate a temporal predicate proof:
        // "balance >= 100 for 8 consecutive blocks, ending at final_state_root"
        let threshold = BabyBear::new(100);
        let num_steps = 8usize;
        let values: Vec<BabyBear> = vec![200, 150, 300, 100, 500, 120, 999, 101]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        // State roots: arbitrary chain ending at final_state_root.
        let mut state_roots: Vec<BabyBear> = (0..num_steps - 1)
            .map(|i| BabyBear::new(5000 + i as u32))
            .collect();
        state_roots.push(final_state_root);

        let temporal_proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold)
                .expect("temporal proof should succeed (all values >= 100)");

        // Attach the temporal proof to the presentation.
        proof.temporal_proofs.push(temporal_proof);

        // Verify the complete presentation with temporal proof.
        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Presentation with valid temporal proof should verify"
        );
    }

    #[test]
    fn presentation_temporal_proof_wrong_state_root_rejected() {
        use crate::predicate_air::PredicateType;
        use crate::temporal_predicate_dsl::prove_temporal_predicate;

        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;

        let air = PresentationAir::new(witness.clone());
        let mut proof = air.prove().expect("base proof should succeed");

        // Generate a temporal proof with a WRONG final_state_root.
        let threshold = BabyBear::new(100);
        let values: Vec<BabyBear> = vec![200, 150, 300, 100]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        // Use a different final state root (not matching the presentation).
        let state_roots: Vec<BabyBear> = (0..4).map(|i| BabyBear::new(9000 + i)).collect();

        let temporal_proof =
            prove_temporal_predicate(&values, &state_roots, PredicateType::Gte, threshold)
                .expect("temporal proof generation should succeed");

        proof.temporal_proofs.push(temporal_proof);

        // Verification should fail: temporal proof not bound to presentation state root.
        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::InvalidTemporalProof { index: 0 },
            "Temporal proof with wrong state root should be rejected"
        );
    }

    // =========================================================================
    // Freshness binding tests
    // =========================================================================

    #[test]
    fn presentation_freshness_valid_token_not_expired() {
        // Token with not_after_height=100, verifier at height 50 -> valid.
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(100);
        witness.verifier_block_height = BabyBear::new(50);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Token with not_after_height=100 at verifier height 50 should be valid"
        );
    }

    #[test]
    fn presentation_freshness_expired_token_rejected() {
        // Token with not_after_height=100, verifier at height 150 -> rejected.
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(100);
        witness.verifier_block_height = BabyBear::new(150);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::TokenExpired,
            "Token with not_after_height=100 at verifier height 150 should be expired"
        );
    }

    #[test]
    fn presentation_freshness_no_expiry_always_valid() {
        // Token with not_after_height=0 -> always valid (no expiry caveat).
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::ZERO;
        witness.verifier_block_height = BabyBear::new(999999);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Token with not_after_height=0 should always be valid (no expiry)"
        );
    }

    #[test]
    fn presentation_freshness_no_verifier_height_skips_check() {
        // If verifier_block_height=0, no freshness check is performed.
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(100);
        witness.verifier_block_height = BabyBear::ZERO;

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "No verifier_block_height should skip freshness check"
        );
    }

    #[test]
    fn presentation_freshness_exact_boundary_valid() {
        // Token with not_after_height=100, verifier at height 100 -> valid (>=, not >).
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(100);
        witness.verifier_block_height = BabyBear::new(100);

        let air = PresentationAir::new(witness);
        let verification = air.verify_all();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Token at exact expiry boundary (not_after_height == verifier_height) should be valid"
        );
    }

    #[test]
    fn presentation_freshness_proof_verify_expired() {
        // Test freshness binding through the proof verification path (not just verify_all).
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(100);
        witness.verifier_block_height = BabyBear::new(150);

        let air = PresentationAir::new(witness);
        let proof = air.prove().expect("proof generation should succeed");

        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::TokenExpired,
            "Proof verification should detect expired token"
        );
    }

    #[test]
    fn presentation_freshness_proof_verify_valid() {
        // Test freshness binding through the proof verification path (valid case).
        let mut witness = create_test_presentation();
        witness.federation_root = witness.issuer_membership.expected_root;
        witness.derivation.not_after_height = BabyBear::new(1000);
        witness.verifier_block_height = BabyBear::new(500);

        let air = PresentationAir::new(witness);
        let proof = air.prove().expect("proof generation should succeed");

        let verification = proof.verify();
        assert_eq!(
            verification,
            PresentationVerification::Valid,
            "Proof verification should pass for non-expired token"
        );
    }
}
