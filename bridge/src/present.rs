//! Full presentation builder.
//!
//! The presentation builder takes a plaintext token chain (a sequence of
//! attenuations) and produces a ZK-ready presentation proof. This is the
//! high-level API that orchestrates the entire pipeline:
//!
//! 1. Convert each token to a committed fact set.
//! 2. Compute fold deltas for each attenuation step.
//! 3. Evaluate the authorization request against the final state.
//! 4. Produce a circuit witness and generate the STARK proof.
//!
//! The resulting `BridgePresentationProof` can be verified without knowing
//! the token chain, capabilities, or any private data — only the public
//! inputs (federation root, request predicate, timestamp) are visible.

use pyana_circuit::binding::WideHash;
use pyana_circuit::derivation_air::{CircuitRule, DerivationWitness};
use pyana_circuit::fold_types::{FoldWitness, RemovedFact};
use pyana_circuit::merkle_air::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use pyana_circuit::poseidon2;
use pyana_circuit::stark;
use pyana_circuit::{
    BabyBear, PresentationAir, PresentationProof, PresentationVerification, PresentationWitness,
    RealPresentationProof,
};
use pyana_commit::merkle::{MerkleProof, MerkleTree};
use pyana_commit::{Fact, FieldElement, FoldDelta, SymbolTable, TokenState};
use pyana_dsl_runtime::fold::build_shared_tree;
use pyana_token::{Attenuation, AuthRequest, MacaroonToken};
use pyana_trace::{AuthorizationTrace, Conclusion, Term as TraceTerm, symbol_from_str};

use crate::authorize::{self, AuthError};
use crate::convert::macaroon_to_factset_secure;
use crate::delta::{further_attenuation_delta, initial_attenuation_delta};

/// Trait for resolving issuer membership in a federation.
///
/// A `FederationRegistry` provides real Merkle proofs from an externally-managed
/// federation tree. This is the production path for issuer membership: the tree
/// is maintained by the federation operator and the prover retrieves a proof for
/// its issuer key.
///
/// The synthetic/deterministic path in `build_issuer_membership()` is retained
/// as a **testing fallback only** and is clearly marked as such.
pub trait FederationRegistry {
    /// Look up the issuer's membership proof in the federation tree.
    ///
    /// Returns the Merkle proof (path indices + siblings at each level) and the
    /// current tree root, or `None` if the issuer is not a member.
    fn issuer_proof(&self, issuer_key: &[u8; 32]) -> Option<(MerkleProof, [u8; 32])>;
}

/// A step in the token chain: the token, its committed state, and the fold delta
/// from the previous state.
#[derive(Clone, Debug)]
pub struct ChainStep {
    /// The committed state at this step.
    pub state: TokenState,
    /// The fold delta from the previous step (None for the first step).
    pub delta: Option<FoldDelta>,
    /// Facts in the committed state.
    pub facts: Vec<Fact>,
}

/// Marker type that restricts access to the local-only constraint check path.
///
/// This type can only be constructed in test/benchmark code via
/// [`UnsafeLocalOnlyMarker::new_for_testing`]. Production code should never
/// hold an instance of this type.
pub struct UnsafeLocalOnlyMarker(());

impl UnsafeLocalOnlyMarker {
    /// Construct the marker. Only call this in tests or benchmarks.
    #[cfg(any(test, feature = "bench"))]
    pub fn new_for_testing() -> Self {
        Self(())
    }

    /// Escape hatch for non-test code that genuinely needs this (e.g., benchmarks
    /// in separate crates). Deliberately ugly name to discourage casual use.
    pub fn i_know_this_is_not_cryptographically_sound() -> Self {
        Self(())
    }
}

/// The high-level presentation builder that bridges plaintext tokens to ZK proofs.
///
/// Usage:
/// 1. Create with `new(issuer_key, federation_root)`.
/// 2. Call `set_root_token(token)` to set the initial (unrestricted) root token.
/// 3. Call `add_attenuation(attenuation)` for each attenuation step.
/// 4. Call `prove(request)` to generate the ZK presentation proof.
pub struct BridgePresentationBuilder {
    /// The issuer's key (used for federation membership proof).
    issuer_key: [u8; 32],
    /// The federation root of trust (raw bytes, for public input serialization).
    federation_root: [u8; 32],
    /// The federation root as a BabyBear field element (used for Merkle comparison).
    federation_root_bb: BabyBear,
    /// Chain of committed states and fold deltas.
    chain: Vec<ChainStep>,
    /// The accumulated symbol table.
    symbols: SymbolTable,
    /// The root token (first token in the chain).
    root_token: Option<MacaroonToken>,
    /// The authorization state: includes all semantic facts (app, service, feature, etc.)
    /// that are needed for policy evaluation. This is separate from the fold chain states
    /// because the fold chain only tracks structural narrowing.
    auth_state: TokenState,
    /// Optional external federation tree for real issuer membership proofs.
    /// When set, `build_issuer_membership` uses a real Merkle path from this tree
    /// instead of the synthetic/deterministic fallback.
    federation_tree: Option<MerkleTree>,
    /// Pre-generated federation membership proof (for delegated tokens).
    ///
    /// When set, `build_issuer_membership` and `build_issuer_membership_poseidon2` use
    /// this proof directly instead of looking up the issuer_key in the federation tree.
    /// This is the delegation architecture fix: the delegator (who has the real issuer key
    /// in the tree) pre-generates the proof and passes it to the delegatee.
    pre_generated_membership_proof: Option<MerkleProof>,
    /// Commitment to the set of facts being selectively disclosed.
    ///
    /// For selective disclosure mode, this is computed by the SDK before calling
    /// `prove()`. It is `poseidon2(hash(fact_1) || ... || hash(fact_n))` over the
    /// revealed facts. For fully private mode, this is `WideHash::ZERO`.
    revealed_facts_commitment: WideHash,
}

/// The complete bridge presentation proof.
///
/// Contains both the ZK proof (circuit-level) and the supporting metadata
/// needed for full verification.
///
/// # Zero-Knowledge Safety
///
/// The `trace` field contains the full authorization derivation trace (all derived
/// facts). This field is **never serialized** to prevent leaking private information
/// over the wire. It is only populated locally for debugging and off-chain verification.
#[derive(Clone, Debug)]
pub struct BridgePresentationProof {
    /// The circuit-level presentation proof (constraint-checked).
    pub circuit_proof: PresentationProof,
    /// Real STARK proof for issuer membership (generated by `prove()`).
    /// This is the proof that the wire protocol should extract and transmit.
    /// `None` when using the fast `prove_fast()` path.
    pub real_stark_proof: Option<RealPresentationProof>,
    /// IVC proof for the fold chain (constant-size, generated by `prove_ivc()`).
    /// This is the preferred proof for long attenuation chains where proof size matters.
    /// `None` when using the non-IVC prove paths.
    pub ivc_proof: Option<pyana_circuit::IvcPresentationProof>,
    /// Validated IVC proof for the fold chain: chain STARK + per-step fold membership STARKs.
    ///
    /// This is the fully STARK-proven fold chain proof that closes the fold-validity gap.
    /// When present, a remote verifier can cryptographically verify:
    /// 1. The hash-chain ordering (via the chain STARK)
    /// 2. Each fold step's removal was valid (via per-step Merkle membership STARKs)
    ///
    /// Generated by [`prove_validated_ivc()`](Self::prove_validated_ivc).
    /// `None` when using other prove paths.
    pub validated_ivc_proof: Option<pyana_circuit::ValidatedIvcProof>,
    /// The authorization trace (for debugging / off-chain verification).
    ///
    /// **SECURITY: This field MUST NOT be transmitted over the wire.** It contains
    /// the full derived fact set which would defeat the zero-knowledge property.
    /// Only available locally after proof generation.
    ///
    /// Use [`Self::into_wire_proof()`] to produce a wire-safe representation that
    /// strips the trace before transmission.
    pub trace: AuthorizationTrace,
    /// Number of attenuation steps in the chain.
    pub chain_length: usize,
    /// The final state root (public input).
    pub final_state_root: [u8; 32],
    /// The federation root (public input).
    pub federation_root: [u8; 32],
    /// Verification result from the circuit layer.
    pub verification: PresentationVerification,
    /// Commitment to the selectively revealed facts (BabyBear field element).
    ///
    /// For selective disclosure mode, this is the Poseidon2 hash over the revealed
    /// fact hashes. The verifier recomputes from the plaintext facts and checks equality.
    /// For fully private mode, this is `WideHash::ZERO`.
    pub revealed_facts_commitment: WideHash,
    /// Composition commitment binding all sub-proofs together.
    ///
    /// This is `poseidon2(fold_chain_commitment, derivation_state_root, presentation_tag)`.
    /// It is included as a public input in the issuer membership STARK, preventing
    /// an attacker from mixing sub-proofs across different presentations.
    /// The verifier recomputes this from the other sub-proofs and checks it matches
    /// the value committed in the STARK's public inputs.
    pub composition_commitment: WideHash,
}

impl BridgePresentationProof {
    /// Whether the proof is cryptographically valid.
    ///
    /// Returns `true` ONLY if a real STARK proof is present AND the circuit-level
    /// verification passed. Proofs generated via `prove_fast()` will return `false`
    /// because they have no cryptographic backing (no real STARK proof).
    ///
    /// For proofs from `prove_fast()`, use `is_constraint_checked()` to determine
    /// if the constraint system passed (useful for development, NOT for security).
    pub fn is_valid(&self) -> bool {
        if self.real_stark_proof.is_none()
            && self.ivc_proof.is_none()
            && self.validated_ivc_proof.is_none()
        {
            return false;
        }
        self.verification == PresentationVerification::Valid
    }

    /// Whether the proof passed local constraint checking.
    ///
    /// This indicates the circuit constraints were satisfied locally, which is
    /// useful for development and debugging. However, this provides NO security
    /// guarantee to a remote verifier because the prover runs the check themselves.
    ///
    /// For cryptographic verification across trust boundaries, use `is_valid()`
    /// which requires a real STARK proof.
    pub fn is_constraint_checked(&self) -> bool {
        matches!(
            self.verification,
            PresentationVerification::Valid | PresentationVerification::LocalOnly
        )
    }

    /// Get the proof size in bytes.
    pub fn proof_size_bytes(&self) -> usize {
        if let Some(real) = &self.real_stark_proof {
            real.total_proof_size_bytes()
        } else {
            self.circuit_proof.total_proof_size_bytes
        }
    }

    /// Human-readable proof size.
    pub fn proof_size_display(&self) -> String {
        if let Some(real) = &self.real_stark_proof {
            real.proof_size_display()
        } else {
            self.circuit_proof.proof_size_display()
        }
    }

    /// Whether this proof contains a real STARK issuer membership proof.
    pub fn has_real_stark_proof(&self) -> bool {
        self.real_stark_proof.is_some()
    }

    /// Extract the serialized STARK proof bytes for the issuer membership claim.
    ///
    /// This is the primary method for wire protocol integration: the returned bytes
    /// can be transmitted to a verifier which reconstructs them via
    /// `stark::proof_from_bytes()` and calls `stark::verify()` with the
    /// `MerkleStarkAir` and the public inputs `[leaf_hash, federation_root]`.
    ///
    /// Returns `None` if this proof was generated via the fast `prove_fast()` path.
    pub fn issuer_proof_bytes(&self) -> Option<Vec<u8>> {
        self.real_stark_proof
            .as_ref()
            .map(|real| stark::proof_to_bytes(&real.issuer_membership_stark_proof))
    }

    /// Verify the real STARK issuer membership proof (if present).
    ///
    /// This performs full cryptographic verification using the STARK verifier
    /// with Poseidon2 AIR (collision-resistant). Returns `None` if no real STARK
    /// proof is attached; returns `Some(Ok(()))` if verification succeeds, or
    /// `Some(Err(msg))` on failure.
    ///
    /// NOTE: The linear AIR fallback has been removed. Only Poseidon2 proofs are
    /// accepted. If you have legacy linear proofs, they must be re-generated.
    pub fn verify_issuer_stark(&self) -> Option<Result<(), String>> {
        self.real_stark_proof.as_ref().map(|real| {
            let pi: Vec<BabyBear> = real
                .issuer_membership_stark_proof
                .public_inputs
                .iter()
                .map(|&v| BabyBear::new(v))
                .collect();

            // Dispatch to DSL circuit based on AIR name (unified path).
            use pyana_dsl_runtime::descriptors;
            let air_name = &real.issuer_membership_stark_proof.air_name;
            if let Some(circuit) = descriptors::circuit_for_air_name(air_name) {
                stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi)
            } else {
                // Fallback: try blinded and standard merkle circuits for legacy air names.
                let blinded = descriptors::blinded_merkle_poseidon2_circuit();
                let standard = descriptors::merkle_poseidon2_circuit();
                if air_name.contains("blinded") {
                    stark::verify(&blinded, &real.issuer_membership_stark_proof, &pi)
                } else {
                    stark::verify(&standard, &real.issuer_membership_stark_proof, &pi)
                }
            }
        })
    }

    /// Convert this proof into a wire-safe representation that strips the private trace.
    ///
    /// **All wire protocol code MUST use this method** before transmitting a proof.
    /// The returned `WirePresentationProof` contains only the cryptographic proof data
    /// and public inputs, with the private authorization trace completely removed.
    ///
    /// Fields stripped for privacy (Phase 2):
    /// - `trace` (was always stripped — contains full derivation)
    /// - `chain_length` (leaks delegation depth)
    /// - `final_state_root` (deterministic per-token, enables linkage)
    /// - `federation_root` bytes (available from the STARK proof's public inputs)
    pub fn into_wire_proof(self) -> WirePresentationProof {
        WirePresentationProof {
            circuit_proof: self.circuit_proof,
            real_stark_proof: self.real_stark_proof,
            ivc_proof: self.ivc_proof,
            validated_ivc_proof: self.validated_ivc_proof,
            verification: self.verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: self.composition_commitment,
        }
    }
}

/// Wire-safe presentation proof (no private trace data).
///
/// This is the type that MUST be used for any network transmission of proofs.
/// It deliberately omits the `AuthorizationTrace` to preserve zero-knowledge.
///
/// # Privacy Design (Phase 2)
///
/// The `chain_length`, `final_state_root`, and raw `federation_root` bytes have been
/// removed because they leak delegation depth and enable cross-presentation linkage.
/// The IVC proof is self-contained; the verifier does not need to know the chain length.
/// The presentation_tag (in the circuit proof's public inputs) replaces the deterministic
/// final_state_root for unlinkable multi-show.
///
/// Obtain via [`BridgePresentationProof::into_wire_proof()`].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WirePresentationProof {
    /// The circuit-level presentation proof (constraint-checked).
    pub circuit_proof: PresentationProof,
    /// Real STARK proof for issuer membership.
    pub real_stark_proof: Option<RealPresentationProof>,
    /// IVC proof for the fold chain.
    pub ivc_proof: Option<pyana_circuit::IvcPresentationProof>,
    /// Validated IVC proof: chain STARK + per-step fold membership STARKs.
    ///
    /// When present, the remote verifier calls `verify_validated_ivc()` to
    /// cryptographically verify the entire attenuation chain without trusting
    /// the prover's local constraint checks.
    pub validated_ivc_proof: Option<pyana_circuit::ValidatedIvcProof>,
    /// Verification result from the circuit layer.
    pub verification: PresentationVerification,
    /// Commitment to the selectively revealed facts.
    pub revealed_facts_commitment: WideHash,
    /// Composition commitment binding all sub-proofs together.
    pub composition_commitment: WideHash,
}

impl BridgePresentationBuilder {
    /// Create a new presentation builder.
    ///
    /// # Arguments
    ///
    /// * `issuer_key` - The issuer's 32-byte key (hashed for federation membership).
    /// * `federation_root` - The 32-byte canonical encoding of the federation root
    ///   (produced by [`bb_to_bytes`]: u32 LE in bytes [0..4], zeros in [4..32]).
    pub fn new(issuer_key: [u8; 32], federation_root: [u8; 32]) -> Self {
        let federation_root_bb = bb_from_bytes(&federation_root);
        Self {
            issuer_key,
            federation_root,
            federation_root_bb,
            chain: Vec::new(),
            symbols: SymbolTable::new(),
            root_token: None,
            auth_state: TokenState::new(),
            federation_tree: None,
            pre_generated_membership_proof: None,
            revealed_facts_commitment: WideHash::ZERO,
        }
    }

    /// Create a new presentation builder with a pre-computed BabyBear federation root.
    ///
    /// This is used when the federation root is known as a field element (e.g., from
    /// a Merkle tree that already operates in BabyBear). The `federation_root` bytes
    /// are still stored for public input serialization.
    pub fn new_with_root_bb(
        issuer_key: [u8; 32],
        federation_root: [u8; 32],
        federation_root_bb: BabyBear,
    ) -> Self {
        Self {
            issuer_key,
            federation_root,
            federation_root_bb,
            chain: Vec::new(),
            symbols: SymbolTable::new(),
            root_token: None,
            auth_state: TokenState::new(),
            federation_tree: None,
            pre_generated_membership_proof: None,
            revealed_facts_commitment: WideHash::ZERO,
        }
    }

    /// Set the revealed facts commitment for selective disclosure mode.
    ///
    /// This must be called before `prove()` when generating a selective disclosure
    /// proof. The commitment binds the revealed facts to the STARK proof, ensuring
    /// the prover cannot lie about which facts were part of the derivation.
    ///
    /// The commitment is `poseidon2(hash(fact_1) || hash(fact_2) || ... || hash(fact_n))`
    /// where each fact_i is hashed with `poseidon2::hash_fact()`.
    pub fn set_revealed_facts_commitment(&mut self, commitment: WideHash) -> &mut Self {
        self.revealed_facts_commitment = commitment;
        self
    }

    /// Attach an external federation Merkle tree for real issuer membership proofs.
    ///
    /// When a federation tree is provided, `build_issuer_membership()` will look up
    /// the issuer key in this tree and use the real Merkle path. This is the production
    /// path that connects to an actual federation registry.
    ///
    /// Without this, the builder falls back to a synthetic/deterministic path that is
    /// only suitable for testing.
    pub fn with_federation_tree(&mut self, tree: MerkleTree) -> &mut Self {
        // Recompute the federation root from the actual tree.
        // The tree root is a full 32-byte BLAKE3 hash; compress it to BabyBear
        // via Poseidon2, then store the canonical bb_to_bytes encoding so that
        // verifiers can recover it with bb_from_bytes.
        let mut tree_clone = tree.clone();
        let root_bytes = tree_clone.root();
        self.federation_root_bb = bytes_to_babybear(&root_bytes);
        self.federation_root = bb_to_bytes(self.federation_root_bb);
        self.federation_tree = Some(tree);
        self
    }

    /// Attach a pre-generated federation membership proof for delegation scenarios.
    ///
    /// Federation tree leaves are BLAKE3-derived proof keys (not raw root keys).
    /// The delegator pre-generates the membership proof at delegation time using the
    /// derived key, and the delegatee passes it here for direct use during proving.
    ///
    /// When this is set, `build_issuer_membership` and `build_issuer_membership_poseidon2`
    /// use this proof directly instead of querying the federation tree.
    ///
    /// The `federation_root` on this builder must still be set correctly (matching the
    /// root the proof was generated against) for the proof to verify.
    pub fn with_pre_generated_membership_proof(&mut self, proof: MerkleProof) -> &mut Self {
        self.pre_generated_membership_proof = Some(proof);
        self
    }

    /// Set the root (unrestricted) token.
    ///
    /// This is the initial token minted by the issuer. It has no caveats
    /// and represents unlimited access.
    pub fn set_root_token(&mut self, token: MacaroonToken) {
        let (factset, syms) = macaroon_to_factset_secure(&token);
        self.symbols.merge(&syms);

        let facts: Vec<Fact> = factset.iter().copied().collect();
        let mut state = TokenState::new();
        for &fact in &facts {
            state.add_fact(fact);
        }

        // Initialize the authorization state with the same facts.
        self.auth_state = TokenState::new();
        for &fact in &facts {
            self.auth_state.add_fact(fact);
        }

        self.chain.push(ChainStep {
            state,
            delta: None,
            facts,
        });
        self.root_token = Some(token);
    }

    /// Add an attenuation step to the chain.
    ///
    /// This takes the `Attenuation` spec (the restrictions being applied)
    /// and computes the fold delta from the current state to the new state.
    ///
    /// # Returns
    ///
    /// `true` if the attenuation was successfully applied, `false` if it
    /// was invalid (e.g., trying to attenuate an empty chain).
    pub fn add_attenuation(&mut self, attenuation: &Attenuation) -> bool {
        let current_step = match self.chain.last() {
            Some(step) => step,
            None => return false,
        };

        // SOUNDNESS: Reject delegation chains deeper than MAX_FOLD_DEPTH.
        // The chain length includes the root step, so fold count = chain.len() - 1.
        // After adding this attenuation it would be chain.len(), so the fold count
        // would be chain.len(). Reject if that exceeds the limit.
        if self.chain.len() as u32 >= pyana_circuit::MAX_FOLD_DEPTH {
            return false;
        }

        let current_state = &current_step.state;

        // Convert attenuation to new restriction facts.
        let new_facts = crate::convert::attenuation_to_facts(attenuation, &mut self.symbols);

        if new_facts.is_empty() {
            return false;
        }

        // If this is the first attenuation (from unrestricted root), we remove
        // the unrestricted fact and add checks.
        let is_first_attenuation = current_step.facts.len() == 1
            && current_step.facts[0].predicate == FieldElement::from_symbol("unrestricted");

        if is_first_attenuation {
            let result = initial_attenuation_delta(attenuation, &mut self.symbols);
            match result {
                Some((_old_state, new_state, delta)) => {
                    // SECURITY: The auth_state and the fold chain's fact set must be
                    // bound together. The circuit's DerivationWitness uses the Poseidon2
                    // root of `ChainStep.facts` as its state_root, and the authorization
                    // evaluator uses auth_state. By using the SAME semantic facts for
                    // both, we ensure the authorization decision IS what gets proven.
                    //
                    // The new_facts (semantic: app, service, feature, etc.) are used for
                    // auth_state AND stored as the chain step's facts (for Poseidon2 root).
                    // The new_state (structural: check-prefixed) is only for fold delta
                    // continuity.
                    self.auth_state = TokenState::new();
                    for fact in &new_facts {
                        self.auth_state.add_fact(*fact);
                    }

                    self.chain.push(ChainStep {
                        state: new_state,
                        delta: Some(delta),
                        facts: new_facts.clone(),
                    });
                    true
                }
                None => false,
            }
        } else {
            // Subsequent attenuation: add restrictions as checks.
            let result = further_attenuation_delta(current_state, &new_facts, &self.symbols);
            match result {
                Some((new_state, delta)) => {
                    // SECURITY: Accumulate semantic facts and use them for both
                    // auth_state and the chain step's Poseidon2 root computation.
                    // This ensures the derivation witness's state_root covers exactly
                    // the facts that the authorization evaluator used.
                    for fact in &new_facts {
                        if !self.auth_state.contains(fact) {
                            self.auth_state.add_fact(*fact);
                        }
                    }

                    // The chain step facts = all semantic facts accumulated so far.
                    let all_semantic_facts = self.auth_state.all_facts();

                    self.chain.push(ChainStep {
                        state: new_state,
                        delta: Some(delta),
                        facts: all_semantic_facts,
                    });
                    true
                }
                None => false,
            }
        }
    }

    /// Get the current chain length (number of states, including root).
    pub fn chain_length(&self) -> usize {
        self.chain.len()
    }

    /// Get the current (final) state, if any.
    pub fn final_state(&self) -> Option<&TokenState> {
        self.chain.last().map(|s| &s.state)
    }

    /// Get the symbol table.
    pub fn symbols(&self) -> &SymbolTable {
        &self.symbols
    }

    /// Verify the fold chain integrity.
    ///
    /// Checks that all fold deltas in the chain are valid and properly linked.
    pub fn verify_chain(&self) -> bool {
        let deltas: Vec<&FoldDelta> = self
            .chain
            .iter()
            .filter_map(|step| step.delta.as_ref())
            .collect();

        if deltas.is_empty() {
            return true; // Only the root, no attenuations.
        }

        // Each delta must individually verify.
        for delta in &deltas {
            if !delta.apply_and_verify() {
                return false;
            }
        }

        // Chain continuity: each delta's new_root must equal the next delta's old_root.
        for i in 0..deltas.len() - 1 {
            if deltas[i].new_root != deltas[i + 1].old_root {
                return false;
            }
        }

        true
    }

    /// Generate a real STARK-backed presentation proof for the given authorization request.
    ///
    /// This is the main entry point that:
    /// 1. Verifies the fold chain.
    /// 2. Evaluates the authorization request against the final state.
    /// 3. Converts the trace to circuit witnesses.
    /// 4. Generates a real Poseidon2 STARK proof for issuer membership.
    ///
    /// For the fast development path that skips real STARK proof generation,
    /// use [`prove_local_constraint_check_only()`](Self::prove_local_constraint_check_only) instead.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by a real STARK issuer membership proof,
    /// or an error if authorization fails or the proof cannot be generated.
    pub fn prove(&mut self, request: &AuthRequest) -> Result<BridgePresentationProof, AuthError> {
        self.prove_real(request)
    }

    /// Generate a local constraint-check-only presentation proof.
    ///
    /// **WARNING: NOT CRYPTOGRAPHICALLY SOUND.** This validates circuit constraints
    /// locally without producing a STARK proof. The resulting proof's `is_valid()`
    /// returns `false` because it has no cryptographic backing. Use
    /// `is_constraint_checked()` to query the local constraint result.
    ///
    /// This is suitable ONLY for:
    /// - Development iteration and debugging
    /// - Benchmarking constraint evaluation overhead
    /// - Scenarios where prover == verifier (co-located, trusted)
    ///
    /// **Do NOT use for untrusted provers or cross-trust-boundary verification.**
    /// For production use, call [`prove`](Self::prove) which generates a real STARK proof.
    ///
    /// # Arguments
    ///
    /// * `_unsafe_marker` - Proof that the caller acknowledges this is not cryptographically sound.
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` with `is_valid() == false` (no cryptographic proof).
    /// Use `is_constraint_checked()` to check if constraints passed locally.
    pub fn prove_local_constraint_check_only(
        &mut self,
        _unsafe_marker: &UnsafeLocalOnlyMarker,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state which contains the
        //    actual semantic facts (app, service, feature, etc.) needed by policy rules.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root (from the fold chain state).
        let mut final_state_clone = final_state.clone();
        let final_root_bytes = final_state_clone.root();

        // 4. Build the circuit witness.
        let circuit_witness = self.build_circuit_witness(&trace, request)?;

        // 5. Generate the presentation proof.
        let air = PresentationAir::new(circuit_witness.clone());
        let constraint_result = air.verify_all();

        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        // SECURITY: prove_fast() produces NO cryptographic proof. Even if constraints
        // pass locally, we report `LocalOnly` to prevent callers from mistaking this
        // for a cryptographically verified proof. Only `prove()` (with a real STARK)
        // sets `Valid`.
        let verification = if constraint_result == PresentationVerification::Valid {
            PresentationVerification::LocalOnly
        } else {
            constraint_result
        };

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: None,
            ivc_proof: None,
            validated_ivc_proof: None,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: WideHash::ZERO, // local constraint check has no STARK binding
        })
    }

    /// Deprecated: use [`prove_local_constraint_check_only`](Self::prove_local_constraint_check_only).
    #[deprecated(
        note = "Use prove_local_constraint_check_only() with an explicit UnsafeLocalOnlyMarker"
    )]
    pub fn prove_fast(
        &mut self,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        let marker = UnsafeLocalOnlyMarker::i_know_this_is_not_cryptographically_sound();
        self.prove_local_constraint_check_only(&marker, request)
    }

    /// Generate a STARK-backed presentation proof using Poseidon2 hashing.
    ///
    /// This is the internal implementation of [`prove`](Self::prove). It calls
    /// `PresentationAir::prove_stark_poseidon2()` to produce a real STARK proof
    /// for the issuer membership sub-circuit using collision-resistant Poseidon2
    /// hashing.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by a real STARK issuer membership proof
    /// with Poseidon2 hash constraints (collision-resistant), or an error if
    /// authorization fails or the proof cannot be generated.
    fn prove_real(&mut self, request: &AuthRequest) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root.
        let mut final_state_clone = final_state.clone();
        let final_root_bytes = final_state_clone.root();

        // 4. Build the circuit witness with Poseidon2-compatible issuer membership.
        let circuit_witness = self.build_circuit_witness_poseidon2(&trace, request)?;

        // 5. Generate the presentation proof using the Poseidon2 STARK path.
        //    The STARK proof for issuer membership is stored in the result so the
        //    wire protocol can extract it via `issuer_proof_bytes()`.
        let air = PresentationAir::new(circuit_witness.clone());
        let verification = air.verify_all();

        // Generate the real STARK proof with Poseidon2 hash constraints.
        // This is the cryptographically-sound, collision-resistant proof of
        // issuer membership that is transmitted over the wire.
        let stark_proof = air.prove_stark_poseidon2().ok_or_else(|| {
            AuthError::InvalidRequest("Poseidon2 STARK proof generation failed".into())
        })?;

        // Also generate the constraint proof for the circuit_proof field.
        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        // The composition_commitment was computed in build_circuit_witness_poseidon2
        // and is now embedded in the STARK proof's public inputs via the witness.
        let composition_commitment = circuit_witness.composition_commitment;

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: Some(stark_proof),
            ivc_proof: None,
            validated_ivc_proof: None,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment,
        })
    }

    /// Generate a STARK-backed presentation proof using the LINEAR AIR.
    ///
    /// **SECURITY WARNING: The linear AIR (`MerkleStarkAir`) uses a trivially
    /// forgeable algebraic binding (parent = current + sib0 + sib1 + sib2 + position).
    /// An adversary can find collisions in polynomial time. This method is retained
    /// ONLY for internal benchmarking of proof generation throughput.**
    ///
    /// For production use, call [`prove`](Self::prove) which uses Poseidon2.
    ///
    /// This method is intentionally NOT public to prevent misuse by external callers.
    #[cfg(any(test, feature = "test-utils"))]
    #[deprecated(
        note = "prove_linear uses a trivially forgeable AIR (linear sum). NEVER use in production. Use prove() with Poseidon2 instead."
    )]
    pub fn prove_linear(
        &mut self,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root.
        let mut final_state_clone = final_state.clone();
        let final_root_bytes = final_state_clone.root();

        // 4. Build the circuit witness (linear binding).
        let circuit_witness = self.build_circuit_witness(&trace, request)?;

        // 5. Generate the presentation proof using the linear STARK path.
        let air = PresentationAir::new(circuit_witness.clone());
        let verification = air.verify_all();

        let stark_proof = air
            .prove_stark()
            .ok_or_else(|| AuthError::InvalidRequest("STARK proof generation failed".into()))?;

        // Also generate the constraint proof for the circuit_proof field.
        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: Some(stark_proof),
            ivc_proof: None,
            validated_ivc_proof: None,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: WideHash::ZERO, // Linear AIR (legacy, test-only)
        })
    }

    /// Generate an IVC-based presentation proof for the given authorization request.
    ///
    /// This uses `PresentationAir::prove_ivc()` to accumulate the entire fold chain
    /// into a single constant-size IVC proof instead of N separate fold proofs.
    /// This is the preferred path for long attenuation chains where proof size matters.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by an IVC fold chain proof,
    /// or an error if authorization fails or the proof cannot be generated.
    pub fn prove_ivc(
        &mut self,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root.
        let mut final_state_clone = final_state.clone();
        let final_root_bytes = final_state_clone.root();

        // 4. Build the circuit witness with Poseidon2 hashing.
        //    SECURITY: Must use poseidon2 witness to compute a real composition_commitment
        //    that binds the IVC proof to the issuer membership proof. Without this,
        //    an attacker could substitute sub-proofs from different tokens.
        let circuit_witness = self.build_circuit_witness_poseidon2(&trace, request)?;
        let composition_commitment = circuit_witness.composition_commitment;

        // 5. Generate the IVC presentation proof.
        let air = PresentationAir::new(circuit_witness.clone());
        let verification = air.verify_all();

        let ivc_proof = air
            .prove_ivc()
            .ok_or_else(|| AuthError::InvalidRequest("IVC proof generation failed".into()))?;

        // Generate the standard circuit_proof for API compatibility.
        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: None,
            ivc_proof: Some(ivc_proof),
            validated_ivc_proof: None,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment,
        })
    }

    /// Generate a STARK-backed presentation proof with per-fact disclosure control.
    ///
    /// This extends `prove()` with predicate proof generation for specified facts.
    /// For each fact in `predicate_facts`, a `BridgePredicateProof` is generated
    /// proving the fact's value satisfies the given predicate without revealing it.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    /// * `predicate_facts` - List of (fact_value, fact_hash, predicate) tuples.
    ///   Each entry generates an independent predicate proof bound to the token state.
    ///
    /// # Returns
    ///
    /// A tuple of (BridgePresentationProof, Vec<BridgePredicateProof>) where the
    /// presentation proof covers the full authorization and the predicate proofs
    /// cover individual fact predicates.
    pub fn prove_with_disclosure(
        &mut self,
        request: &AuthRequest,
        predicate_facts: &[(u32, BabyBear, &Predicate)],
    ) -> Result<(BridgePresentationProof, Vec<BridgePredicateProof>), AuthError> {
        // Generate the main STARK proof.
        let main_proof = self.prove_real(request)?;

        // Compute state root from the final state for fact commitment binding.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let mut final_state_clone = final_step.state.clone();
        let state_root_bytes = final_state_clone.root();
        let state_root = bytes_to_babybear(&state_root_bytes);

        // Generate predicate proofs for each specified fact.
        let mut pred_proofs = Vec::with_capacity(predicate_facts.len());
        for &(value, fact_hash, ref predicate) in predicate_facts {
            let proof = prove_predicate_for_fact(value, fact_hash, state_root, predicate)
                .ok_or_else(|| {
                    AuthError::InvalidRequest(format!(
                        "predicate proof generation failed for value {} with {:?}",
                        value, predicate
                    ))
                })?;
            pred_proofs.push(proof);
        }

        Ok((main_proof, pred_proofs))
    }

    /// Generate a STARK-proven presentation proof with validated fold chain.
    ///
    /// This is the strongest proving path: it produces real STARK proofs for:
    /// 1. **Issuer membership** (ring membership STARK, same as `prove()`)
    /// 2. **Fold chain hash-chain ordering** (StateTransitionAir STARK)
    /// 3. **Per-step fold validity** (Merkle membership STARK for each removed fact)
    ///
    /// A remote verifier trusting only the STARKs gets cryptographic guarantees on
    /// the entire attenuation history, not just issuer membership.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by both a real STARK issuer membership proof
    /// AND a `ValidatedIvcProof` covering the fold chain, or an error if authorization
    /// fails or the proof cannot be generated.
    pub fn prove_validated_ivc(
        &mut self,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        use pyana_circuit::ivc::prove_validated_ivc;

        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root.
        let mut final_state_clone = final_state.clone();
        let final_root_bytes = final_state_clone.root();

        // 4. Build the circuit witness with Poseidon2-compatible issuer membership.
        let circuit_witness = self.build_circuit_witness_poseidon2(&trace, request)?;

        // 5. Generate the Poseidon2 STARK proof for issuer membership.
        let air = PresentationAir::new(circuit_witness.clone());
        let verification = air.verify_all();

        let stark_proof = air.prove_stark_poseidon2().ok_or_else(|| {
            AuthError::InvalidRequest("Poseidon2 STARK proof generation failed".into())
        })?;

        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        // 6. Build the fold chain and extract FoldStepWitnesses for validated IVC.
        let fold_step_witnesses = self.build_fold_step_witnesses()?;

        // 7. Generate the validated IVC proof (chain STARK + per-step membership STARKs).
        let validated_ivc = if fold_step_witnesses.is_empty() {
            // No fold steps (unrestricted token) — no validated IVC needed.
            None
        } else {
            let initial_root = fold_step_witnesses[0].old_root;
            match prove_validated_ivc(initial_root, &fold_step_witnesses) {
                Ok(proof) => Some(proof),
                Err(e) => {
                    return Err(AuthError::InvalidRequest(format!(
                        "Validated IVC proof generation failed: {}",
                        e
                    )));
                }
            }
        };

        // The composition_commitment was computed in build_circuit_witness_poseidon2
        // and is now embedded in the STARK proof's public inputs via the witness.
        let composition_commitment = circuit_witness.composition_commitment;

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: Some(stark_proof),
            ivc_proof: None,
            validated_ivc_proof: validated_ivc,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment,
        })
    }

    /// Build `FoldStepWitness` instances for the validated IVC path.
    ///
    /// Each `FoldStepWitness` contains the Merkle proof (siblings + positions) that
    /// the removed fact existed in the tree at the step's old_root. This is the data
    /// needed by `prove_validated_ivc()` to generate per-step membership STARKs.
    fn build_fold_step_witnesses(
        &self,
    ) -> Result<Vec<pyana_circuit::ivc::FoldStepWitness>, AuthError> {
        use pyana_circuit::ivc::FoldStepWitness;
        use pyana_circuit::poseidon2::hash_fact;

        let mut witnesses = Vec::new();

        for i in 1..self.chain.len() {
            let delta = match &self.chain[i].delta {
                Some(d) => d,
                None => continue,
            };

            let old_facts = &self.chain[i - 1].facts;
            let new_facts = &self.chain[i].facts;

            // Compute fact hashes in the Poseidon2 domain for the old state.
            let old_leaf_hashes: Vec<BabyBear> = old_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();

            // Build a Poseidon2 Merkle tree over the old state's fact hashes.
            let tree_depth = 4;
            let (old_root, old_proofs) = build_shared_tree(&old_leaf_hashes, tree_depth);

            // Compute the new state's Poseidon2 root.
            let new_leaf_hashes: Vec<BabyBear> = new_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();
            let (new_root, _) = build_shared_tree(&new_leaf_hashes, tree_depth);

            // For each removed fact, build its FoldStepWitness.
            // The validated IVC expects ONE removed fact per step. If there are multiple
            // removals in a single fold delta, we produce one witness per removal and
            // chain the roots accordingly.
            for (fact, _commit_proof) in &delta.removed {
                let pred_bb = bytes_to_babybear(&fact.predicate.0);
                let terms = [
                    bytes_to_babybear(&fact.terms[0].0),
                    bytes_to_babybear(&fact.terms[1].0),
                    bytes_to_babybear(&fact.terms[2].0),
                ];
                let fact_hash = hash_fact(pred_bb, &terms);

                // Find this fact's index in the old state to get its Merkle proof.
                let proof_idx = old_leaf_hashes
                    .iter()
                    .position(|&h| h == fact_hash)
                    .ok_or_else(|| {
                        AuthError::InvalidRequest(
                            "removed fact not found in old state for validated IVC".into(),
                        )
                    })?;

                let merkle_witness = &old_proofs[proof_idx];

                // Convert MerkleWitness levels to the flat (siblings, positions) format.
                let merkle_siblings: Vec<[BabyBear; 3]> = merkle_witness
                    .levels
                    .iter()
                    .map(|level| level.siblings)
                    .collect();
                let merkle_positions: Vec<u8> = merkle_witness
                    .levels
                    .iter()
                    .map(|level| level.position)
                    .collect();

                witnesses.push(FoldStepWitness {
                    old_root,
                    new_root,
                    removed_fact_hash: fact_hash,
                    merkle_siblings,
                    merkle_positions,
                });
            }
        }

        Ok(witnesses)
    }

    /// Build the circuit-level presentation witness from the authorization trace.
    /// Uses linear algebraic binding for the issuer membership (legacy path).
    fn build_circuit_witness(
        &self,
        trace: &AuthorizationTrace,
        request: &AuthRequest,
    ) -> Result<PresentationWitness, AuthError> {
        // Compute the canonical action binding commitment from (action, resource).
        // Resource = app_id OR service (whichever is present), matching the wire
        // verifier's expectation. This ensures service-scoped tokens produce the
        // same binding that the verifier will recompute.
        let action_str = request.action.as_deref().unwrap_or("");
        let resource_str = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let request_pred_bb = pyana_circuit::compute_action_binding(action_str, resource_str);

        // Timestamp.
        let timestamp = request.now.unwrap_or(0);
        let timestamp_bb = BabyBear::from_u64(timestamp as u64);

        // Build fold witnesses from the chain deltas.
        let fold_chain = self.build_fold_witnesses();

        // Compute the Poseidon2 state root for the derivation witness.
        let derivation_state_root = self.final_state_poseidon2_root(&fold_chain);

        // Build the derivation witness from the trace.
        let derivation = self.build_derivation_witness(trace, derivation_state_root)?;

        // Build the issuer membership witness.
        let issuer_key_hash = bytes_to_babybear(&self.issuer_key);
        let issuer_membership = self.build_issuer_membership(issuer_key_hash)?;

        // Generate fresh presentation randomness for the presentation tag.
        let presentation_randomness = generate_presentation_randomness();

        // Assemble the presentation witness.
        // We need the federation_root to match the issuer_membership.expected_root
        // for the proof to verify.
        // NOTE: Legacy path uses blinding_factor=ZERO (no ring membership).
        // NOTE: Legacy path uses composition_commitment=ZERO (no sub-proof binding).
        let witness = PresentationWitness {
            federation_root: issuer_membership.expected_root,
            request_predicate: request_pred_bb,
            timestamp: timestamp_bb,
            fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash,
            revealed_facts_commitment: self.revealed_facts_commitment,
            blinding_factor: BabyBear::ZERO,
            presentation_randomness,
            composition_commitment: WideHash::ZERO,
            verifier_nonce: BabyBear::ZERO,
            verifier_block_height: BabyBear::ZERO,
        };

        Ok(witness)
    }

    /// Build the circuit-level presentation witness using Poseidon2 hashing
    /// for the issuer membership proof (collision-resistant, production path).
    ///
    /// This uses ring membership (blinded issuer proof) by default: a fresh
    /// random blinding factor is generated per presentation, making the proof
    /// unlinkable. The public inputs expose `blinded_leaf = hash_2_to_1(leaf_hash, blinding)`
    /// instead of the raw `leaf_hash`, so the verifier cannot determine which
    /// federation member issued the token.
    fn build_circuit_witness_poseidon2(
        &self,
        trace: &AuthorizationTrace,
        request: &AuthRequest,
    ) -> Result<PresentationWitness, AuthError> {
        // Compute the canonical action binding commitment from (action, resource).
        // Resource = app_id OR service (whichever is present), matching the wire
        // verifier's expectation. This ensures service-scoped tokens produce the
        // same binding that the verifier will recompute.
        let action_str = request.action.as_deref().unwrap_or("");
        let resource_str = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let request_pred_bb = pyana_circuit::compute_action_binding(action_str, resource_str);

        // Timestamp: use the request's `now` field if provided, otherwise default to
        // the current system time. A non-zero timestamp is essential for proof freshness;
        // verifiers can reject proofs with stale timestamps.
        let timestamp = request.now.unwrap_or_else(|| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64
        });
        let timestamp_bb = BabyBear::from_u64(timestamp as u64);

        // Build fold witnesses from the chain deltas.
        let fold_chain = self.build_fold_witnesses();

        // Compute the Poseidon2 state root for the derivation witness.
        let derivation_state_root = self.final_state_poseidon2_root(&fold_chain);

        // Build the derivation witness from the trace.
        let derivation = self.build_derivation_witness(trace, derivation_state_root)?;

        // Build the issuer membership witness with Poseidon2 hashing.
        let issuer_key_hash = bytes_to_babybear(&self.issuer_key);
        let issuer_membership = self.build_issuer_membership_poseidon2(issuer_key_hash)?;

        // Generate a fresh random blinding factor for ring membership (unlinkability).
        // Each presentation gets a new blinding factor, so the public `blinded_leaf`
        // is different each time — even for the same issuer.
        let blinding_factor = generate_blinding_factor();

        // Generate fresh presentation randomness for the presentation tag.
        // This ensures the tag `Poseidon2(final_root, randomness, nonce)` is different each show.
        let presentation_randomness = generate_presentation_randomness();

        // Compute the presentation tag (same formula as the circuit uses).
        // The verifier_nonce is included to cryptographically bind the proof to a
        // specific verifier challenge, preventing replay attacks.
        let verifier_nonce = BabyBear::ZERO; // TODO: accept from verifier challenge
        let final_root = if let Some(last_fold) = fold_chain.last() {
            last_fold.new_root
        } else {
            derivation_state_root
        };
        let presentation_tag = pyana_circuit::binding::compute_presentation_tag(
            final_root,
            presentation_randomness,
            verifier_nonce,
        );

        // Compute the fold chain commitment: Poseidon2 over all fold step roots.
        // This summarizes the entire fold chain into a single field element.
        let fold_chain_commitment = if fold_chain.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = fold_chain
                .iter()
                .flat_map(|f| [f.old_root, f.new_root])
                .collect();
            poseidon2::hash_many(&fold_roots)
        };

        // SECURITY: Composition commitment binds all sub-proofs together.
        // This is included as a public input in the issuer membership STARK.
        // If an attacker swaps ANY sub-proof (e.g., attaches a valid membership
        // STARK from one token to a forged fold chain from another), the
        // composition_commitment will not match, and STARK verification fails.
        // Use the narrow (single-element) tag for the composition hash since
        // the composition commitment is itself a single BabyBear element.
        let presentation_tag_narrow = poseidon2::hash_many(&presentation_tag);
        let composition_commitment = WideHash::from_poseidon2(
            "pyana-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag_narrow,
            ],
        );

        // Assemble the presentation witness.
        let witness = PresentationWitness {
            federation_root: issuer_membership.expected_root,
            request_predicate: request_pred_bb,
            timestamp: timestamp_bb,
            fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash,
            revealed_facts_commitment: self.revealed_facts_commitment,
            blinding_factor,
            presentation_randomness,
            composition_commitment,
            verifier_nonce,
            verifier_block_height: BabyBear::ZERO,
        };

        Ok(witness)
    }

    /// Build FoldWitness instances for the circuit from our chain deltas.
    ///
    /// This builds Poseidon2-based Merkle trees over the fact hashes at each step
    /// and produces membership proofs in the circuit's hash domain. The commit layer's
    /// BLAKE3-based roots/proofs are not directly usable in the circuit.
    pub fn build_fold_witnesses(&self) -> Vec<FoldWitness> {
        use pyana_circuit::poseidon2::hash_fact;

        let mut witnesses = Vec::new();

        for i in 1..self.chain.len() {
            let delta = match &self.chain[i].delta {
                Some(d) => d,
                None => continue,
            };

            // The "old" state is the previous step's facts.
            let old_facts = &self.chain[i - 1].facts;
            let new_facts = &self.chain[i].facts;

            // Compute fact hashes in the Poseidon2 domain for the old state.
            let old_leaf_hashes: Vec<BabyBear> = old_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();

            // Build a Poseidon2 Merkle tree over the old state's fact hashes.
            let tree_depth = 4; // Match the circuit's tree depth.
            let (old_root, old_proofs) = build_shared_tree(&old_leaf_hashes, tree_depth);

            // Compute the new state's Poseidon2 root.
            let new_leaf_hashes: Vec<BabyBear> = new_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();
            let (new_root, _) = build_shared_tree(&new_leaf_hashes, tree_depth);

            // For each removed fact, find its index in the old state and get its proof.
            let removed_facts: Vec<RemovedFact> = delta
                .removed
                .iter()
                .map(|(fact, _commit_proof)| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    let fact_hash = hash_fact(pred_bb, &terms);

                    // Find this fact's index in the old state to get its Merkle proof.
                    let proof_idx = old_leaf_hashes
                        .iter()
                        .position(|&h| h == fact_hash)
                        .expect("removed fact must exist in old state");

                    RemovedFact {
                        predicate: pred_bb,
                        terms,
                        membership_proof: Some(old_proofs[proof_idx].clone()),
                    }
                })
                .collect();

            // Compute the cryptographic commitment to added checks.
            // This binds the actual check content to the fold proof, preventing
            // a prover from claiming checks they didn't actually add.
            let added_checks_commitment = if delta.added_checks.is_empty() {
                WideHash::ZERO
            } else {
                let check_hashes: Vec<BabyBear> = delta
                    .added_checks
                    .iter()
                    .map(|check| {
                        let pred_bb = bytes_to_babybear(&check.predicate.0);
                        let terms = [
                            bytes_to_babybear(&check.terms[0].0),
                            bytes_to_babybear(&check.terms[1].0),
                            bytes_to_babybear(&check.terms[2].0),
                        ];
                        hash_fact(pred_bb, &terms)
                    })
                    .collect();
                WideHash::from_poseidon2("pyana-checks-v1", &check_hashes)
            };

            witnesses.push(FoldWitness {
                old_root,
                new_root,
                removed_facts,
                num_added_checks: delta.added_checks.len(),
                added_checks_commitment,
            });
        }

        witnesses
    }

    /// Compute the Poseidon2-domain state root for the derivation witness.
    ///
    /// If there are fold steps, this is the last fold's `new_root`. Otherwise,
    /// we compute it from the final (and only) state's facts.
    fn final_state_poseidon2_root(&self, fold_chain: &[FoldWitness]) -> BabyBear {
        use pyana_circuit::poseidon2::hash_fact;

        if let Some(last_fold) = fold_chain.last() {
            last_fold.new_root
        } else {
            // No folds — compute from the single state's facts.
            let final_step = match self.chain.last() {
                Some(step) => step,
                None => return BabyBear::ZERO,
            };
            let leaf_hashes: Vec<BabyBear> = final_step
                .facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();
            let (root, _) = build_shared_tree(&leaf_hashes, 4);
            root
        }
    }

    /// Build the DerivationWitness from the authorization trace.
    ///
    /// `state_root_bb` is the Poseidon2-domain root of the final state, matching
    /// the fold chain's last `new_root` (or the initial root if no folds).
    fn build_derivation_witness(
        &self,
        trace: &AuthorizationTrace,
        state_root_bb: BabyBear,
    ) -> Result<DerivationWitness, AuthError> {
        // The derivation witness proves that the final state authorizes the request.
        // We need to pick the rule that fired (from the trace conclusion).

        let rule_id = match &trace.conclusion {
            Conclusion::Allow { policy_rule_id } => *policy_rule_id,
            Conclusion::Deny => return Err(AuthError::Denied),
        };

        // Reconstruct the evaluator's fact set so we can look up body facts
        // by index. The evaluator builds: base facts + request facts + derived facts.
        let reconstructed_facts = self.reconstruct_evaluator_facts(trace);

        // Build body fact hashes from the derivation steps.
        // Use the last step that derived "allow".
        let allow_step = trace
            .steps
            .iter()
            .find(|s| s.derived_fact.predicate == symbol_from_str("allow"));

        let (body_fact_hashes, substitution, derived_pred, derived_terms) =
            if let Some(step) = allow_step {
                let body_hashes: Vec<BabyBear> = step
                    .body_fact_indices
                    .iter()
                    .map(|&idx| {
                        // Hash the actual body fact using Poseidon2 for circuit compatibility.
                        if let Some(fact) = reconstructed_facts.get(idx) {
                            let pred_bb = bytes_to_babybear(&fact.predicate);
                            let mut term_bbs = [BabyBear::ZERO; 3];
                            for (i, term) in fact.terms.iter().take(3).enumerate() {
                                term_bbs[i] = match term {
                                    TraceTerm::Const(sym) => bytes_to_babybear(sym),
                                    TraceTerm::Int(v) => BabyBear::from_u64(*v as u64),
                                    TraceTerm::Var(_) => BabyBear::ZERO,
                                };
                            }
                            poseidon2::hash_fact(pred_bb, &term_bbs)
                        } else {
                            // Index out of range — use a non-zero sentinel.
                            BabyBear::new(1)
                        }
                    })
                    .collect();

                let subst: Vec<BabyBear> = step
                    .substitution
                    .bindings
                    .iter()
                    .map(|(_, term)| match term {
                        TraceTerm::Const(sym) => bytes_to_babybear(sym),
                        TraceTerm::Int(i) => BabyBear::from_u64(*i as u64),
                        TraceTerm::Var(_) => BabyBear::ZERO,
                    })
                    .collect();

                let pred = bytes_to_babybear(&step.derived_fact.predicate);
                let mut terms = [BabyBear::ZERO; 4];
                for (i, term) in step.derived_fact.terms.iter().take(4).enumerate() {
                    terms[i] = match term {
                        TraceTerm::Const(sym) => bytes_to_babybear(sym),
                        TraceTerm::Int(v) => BabyBear::from_u64(*v as u64),
                        TraceTerm::Var(_) => BabyBear::ZERO,
                    };
                }

                (body_hashes, subst, pred, terms)
            } else {
                // No derivation step found — this shouldn't happen for Allow conclusions.
                // Fall back to a minimal witness.
                let allow_sym = symbol_from_str("allow");
                (
                    vec![BabyBear::new(rule_id)],
                    vec![],
                    bytes_to_babybear(&allow_sym),
                    [BabyBear::ZERO; 4],
                )
            };

        // Ensure we have at least one body hash.
        let body_fact_hashes = if body_fact_hashes.is_empty() {
            vec![BabyBear::new(1)]
        } else {
            body_fact_hashes
        };

        // Build the circuit rule representation.
        // The "allow" rule's head has no terms (it's just "allow()"),
        // so all head_terms are literal zeros.
        let circuit_rule = CircuitRule {
            id: rule_id,
            num_body_atoms: body_fact_hashes.len(),
            num_variables: substitution.len(),
            head_predicate: derived_pred,
            head_terms: [
                (false, derived_terms[0]),
                (false, derived_terms[1]),
                (false, derived_terms[2]),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };

        Ok(DerivationWitness {
            rule: circuit_rule,
            state_root: state_root_bb,
            body_fact_hashes,
            substitution,
            derived_predicate: derived_pred,
            derived_terms,
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        })
    }

    /// Reconstruct the evaluator's fact set from the authorization trace.
    ///
    /// The evaluator builds facts as: base committed facts (from auth_state) +
    /// request facts (injected by the evaluator) + derived facts from prior steps.
    /// The `body_fact_indices` in each DerivationStep index into this growing list.
    fn reconstruct_evaluator_facts(&self, trace: &AuthorizationTrace) -> Vec<pyana_trace::Fact> {
        use pyana_trace::{Fact as TraceFact, Term, symbol_from_bytes, symbol_from_str};

        let mut facts: Vec<TraceFact> = Vec::new();

        // 1. Base facts from the committed auth_state.
        // Use the same conversion as committed_facts_to_trace: symbol_from_str for
        // predicates (matches policy rule predicates), symbol_from_bytes for terms
        // (enables Contains check and matches what the evaluator used).
        for fact in self.auth_state.all_facts() {
            let pred_symbol = if let Some(name) = self.symbols.resolve(fact.predicate) {
                symbol_from_str(name)
            } else {
                fact.predicate.0
            };
            let mut terms = Vec::new();
            for term_fe in &fact.terms {
                if term_fe.is_zero() {
                    break;
                }
                if let Some(name) = self.symbols.resolve(*term_fe) {
                    terms.push(Term::Const(symbol_from_bytes(name.as_bytes())));
                } else {
                    terms.push(Term::Const(term_fe.0));
                }
            }
            facts.push(TraceFact::new(pred_symbol, terms));
        }

        // 2. Request facts (same injection as the evaluator performs).
        let req = &trace.request;
        if let Some(app_id) = &req.app_id {
            facts.push(TraceFact::new(
                symbol_from_str("request_app"),
                vec![Term::Const(*app_id)],
            ));
        }
        if let Some(service) = &req.service {
            facts.push(TraceFact::new(
                symbol_from_str("request_service"),
                vec![Term::Const(*service)],
            ));
        }
        if let Some(action) = &req.action {
            facts.push(TraceFact::new(
                symbol_from_str("request_action"),
                vec![Term::Const(*action)],
            ));
        }
        for feature in &req.features {
            facts.push(TraceFact::new(
                symbol_from_str("request_feature"),
                vec![Term::Const(*feature)],
            ));
        }
        if let Some(user_id) = &req.user_id {
            facts.push(TraceFact::new(
                symbol_from_str("request_user"),
                vec![Term::Const(*user_id)],
            ));
        }
        facts.push(TraceFact::new(
            symbol_from_str("request_time"),
            vec![Term::Int(req.now)],
        ));

        // 3. Derived facts from prior steps (in order).
        for step in &trace.steps {
            facts.push(step.derived_fact.clone());
        }

        facts
    }

    /// Build the issuer membership Merkle witness.
    ///
    /// If a federation tree was attached via `with_federation_tree()`, this uses
    /// a real Merkle proof from the tree. In test/test-utils builds, it falls back
    /// to a synthetic deterministic path.
    ///
    /// In production builds without a federation tree, returns
    /// `Err(AuthError::IssuerNotInFederation)`.
    pub fn build_issuer_membership(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Delegation path: use pre-generated membership proof if available.
        // The delegator pre-generated this proof using the BLAKE3-derived proof key
        // (which IS the tree leaf). The delegatee passes this proof directly.
        if let Some(proof) = &self.pre_generated_membership_proof {
            return self.build_issuer_membership_from_proof(proof, issuer_key_hash);
        }

        // Production path: use real federation tree if available.
        if let Some(tree) = &self.federation_tree {
            return self.build_issuer_membership_from_tree(tree, issuer_key_hash);
        }

        // TESTING FALLBACK: synthetic/deterministic Merkle path.
        // Only available in test builds or with the `test-utils` feature.
        #[cfg(any(test, feature = "test-utils"))]
        {
            self.build_issuer_membership_synthetic(issuer_key_hash)
        }

        #[cfg(not(any(test, feature = "test-utils")))]
        {
            Err(AuthError::IssuerNotInFederation)
        }
    }

    /// Build issuer membership from a real federation Merkle tree.
    ///
    /// Looks up the issuer key's leaf hash in the tree and converts the resulting
    /// `MerkleProof` (with `[u8; 32]` siblings) into the circuit's `MerkleWitness`
    /// (with `BabyBear` field element siblings).
    fn build_issuer_membership_from_tree(
        &self,
        tree: &MerkleTree,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // The federation tree stores issuer keys as leaf data.
        // Look up the issuer key's membership proof.
        let proof = tree
            .membership_proof(&self.issuer_key)
            .ok_or(AuthError::IssuerNotInFederation)?;

        // Convert the MerkleProof (byte-level) to a circuit MerkleWitness (field-level).
        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = issuer_key_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            // Convert 32-byte siblings to BabyBear via Poseidon2 hash compression.
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];
            let parent = MerkleAir::compute_parent(current, position, &siblings);
            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        // The computed root must match the federation root we were configured with.
        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }

    /// Build issuer membership from a pre-generated MerkleProof (linear binding).
    ///
    /// This is used in the delegation path: the delegator pre-generated the proof
    /// using the REAL issuer key. The delegatee converts it to a circuit witness
    /// using the `issuer_key_hash` (which is derived from their proof_key) for the
    /// leaf computation, but uses the pre-generated path (siblings/positions) directly.
    ///
    /// Note: the `issuer_key_hash` here is computed from the proof_key (the BLAKE3
    /// derivation). The proof's path is valid for the REAL issuer key in the tree.
    /// The circuit witness uses the path from the pre-generated proof but recomputes
    /// parents from the leaf hash of the real issuer key's Poseidon2 encoding.
    fn build_issuer_membership_from_proof(
        &self,
        proof: &MerkleProof,
        _issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Convert the pre-generated proof's leaf_hash to a BabyBear field element.
        // This is the hash of the REAL issuer key, not the proof_key.
        let real_leaf_hash = bytes_to_babybear(&proof.leaf_hash);

        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = real_leaf_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];
            let parent = MerkleAir::compute_parent(current, position, &siblings);
            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        // The computed root must match the federation root.
        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: real_leaf_hash,
            levels,
            expected_root: current,
        })
    }

    /// Synthetic/deterministic issuer membership proof (TESTING ONLY).
    ///
    /// Constructs a Merkle path from BLAKE3-derived sibling values. This is NOT
    /// connected to any real federation registry. The "membership" it proves is
    /// purely that the path was built targeting the configured `federation_root_bb`.
    ///
    /// Use `with_federation_tree()` for production proofs.
    #[cfg(any(test, feature = "test-utils"))]
    fn build_issuer_membership_synthetic(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        let depth = 8;
        let mut current = issuer_key_hash;
        let mut levels = Vec::with_capacity(depth);

        // Derive sibling values deterministically from the issuer key.
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &self.issuer_key)),
                BabyBear::new(hash_index(i, 1, &self.issuer_key)),
                BabyBear::new(hash_index(i, 2, &self.issuer_key)),
            ];
            let parent = MerkleAir::compute_parent(current, position, &siblings);
            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        // Verify that the computed root matches the expected federation root.
        // This prevents the tautological construction from silently passing:
        // the builder cannot fabricate membership if the federation_root is a
        // real, externally-provided public parameter.
        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }

    /// Build the issuer membership Merkle witness using Poseidon2 hashing.
    ///
    /// This produces a witness compatible with the DSL `merkle_poseidon2_circuit()` where
    /// parent = hash_fact(current, [sib0, sib1, sib2, position]). The resulting proof
    /// is collision-resistant (unlike the linear binding which has weaker security).
    ///
    /// If a federation tree is available, it uses real tree proofs with Poseidon2
    /// hashing. In test/test-utils builds, falls back to a synthetic path.
    /// In production builds without a federation tree, returns an error.
    pub fn build_issuer_membership_poseidon2(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Delegation path: use pre-generated membership proof if available.
        // Uses Poseidon2 hashing to convert the byte-level proof to a field-level witness.
        if let Some(proof) = &self.pre_generated_membership_proof {
            return self.build_issuer_membership_poseidon2_from_proof(proof, issuer_key_hash);
        }

        // Production path: use real federation tree if available.
        if let Some(tree) = &self.federation_tree {
            return self.build_issuer_membership_poseidon2_from_tree(tree, issuer_key_hash);
        }

        // TESTING FALLBACK: synthetic Poseidon2 Merkle path.
        #[cfg(any(test, feature = "test-utils"))]
        {
            self.build_issuer_membership_poseidon2_synthetic(issuer_key_hash)
        }

        #[cfg(not(any(test, feature = "test-utils")))]
        {
            Err(AuthError::IssuerNotInFederation)
        }
    }

    /// Build Poseidon2 issuer membership from a real federation Merkle tree.
    fn build_issuer_membership_poseidon2_from_tree(
        &self,
        tree: &MerkleTree,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        let proof = tree
            .membership_proof(&self.issuer_key)
            .ok_or(AuthError::IssuerNotInFederation)?;

        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = issuer_key_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];

            // Use Poseidon2 hashing: arrange children by position, hash with hash_4_to_1
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
            let parent = poseidon2::hash_4_to_1(&children);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }

    /// Build Poseidon2 issuer membership from a pre-generated MerkleProof.
    ///
    /// This is the Poseidon2 variant of the delegation path. The delegator pre-generated
    /// the proof using the REAL issuer key. We convert the byte-level siblings to BabyBear
    /// field elements and use Poseidon2 hashing (hash_4_to_1) to compute parents.
    ///
    /// The leaf_hash in the proof corresponds to the REAL issuer key, so we use it
    /// (converted to BabyBear) as the starting leaf for the witness computation.
    fn build_issuer_membership_poseidon2_from_proof(
        &self,
        proof: &MerkleProof,
        _issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Use the pre-generated proof's leaf_hash (the REAL issuer key hash from the tree).
        let real_leaf_hash = bytes_to_babybear(&proof.leaf_hash);

        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = real_leaf_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];

            // Use Poseidon2 hashing: arrange children by position, hash with hash_4_to_1
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
            let parent = poseidon2::hash_4_to_1(&children);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: real_leaf_hash,
            levels,
            expected_root: current,
        })
    }

    /// Synthetic/deterministic Poseidon2 issuer membership proof (TESTING ONLY).
    ///
    /// Constructs a Merkle path using real Poseidon2 hashing at each level,
    /// with BLAKE3-derived sibling values. Compatible with the DSL `merkle_poseidon2_circuit()`.
    #[cfg(any(test, feature = "test-utils"))]
    fn build_issuer_membership_poseidon2_synthetic(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        let depth = 8;
        let mut current = issuer_key_hash;
        let mut levels = Vec::with_capacity(depth);

        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &self.issuer_key)),
                BabyBear::new(hash_index(i, 1, &self.issuer_key)),
                BabyBear::new(hash_index(i, 2, &self.issuer_key)),
            ];

            // Use Poseidon2 hashing (collision-resistant) instead of linear sum
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
            let parent = poseidon2::hash_4_to_1(&children);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        // Verify that the computed root matches the expected federation root.
        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }
}

/// Encode a 32-byte value as 8 BabyBear field elements (4 bytes each, mod p).
/// This preserves full 256-bit distinguishability across the limb vector.
pub fn bytes_to_babybear_vec(bytes: &[u8; 32]) -> [BabyBear; 8] {
    BabyBear::encode_hash(bytes)
}

/// Compress a 32-byte value into a single BabyBear element by encoding as
/// 8 limbs and hashing them together with Poseidon2. This preserves collision
/// resistance up to the ~31-bit field size while using all 256 input bits.
pub fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = bytes_to_babybear_vec(bytes);
    poseidon2::hash_many(&limbs)
}

/// Encode a BabyBear field element as a 32-byte array (canonical encoding).
///
/// The u32 value is stored in bytes [0..4] as little-endian, with bytes [4..32]
/// zeroed. This is the canonical wire encoding used by the wallet, engine, and
/// verifier. Use [`bb_from_bytes`] to decode.
pub fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&bb.as_u32().to_le_bytes());
    bytes
}

/// Decode a BabyBear field element from its canonical 32-byte encoding.
///
/// Reads bytes [0..4] as a little-endian u32 and constructs a canonical BabyBear
/// element (reduced mod p). This is the inverse of [`bb_to_bytes`] and is used by
/// all verification paths to recover a federation root from its wire representation.
pub fn bb_from_bytes(bytes: &[u8; 32]) -> BabyBear {
    let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    BabyBear::new_canonical(val)
}

/// Generate a fresh random blinding factor for ring membership proofs.
///
/// This produces a non-zero BabyBear field element from OS randomness.
/// A fresh blinding factor is generated per presentation to ensure unlinkability:
/// `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)` is different each time.
fn generate_blinding_factor() -> BabyBear {
    let mut buf = [0u8; 4];
    getrandom::fill(&mut buf).expect("OS randomness unavailable");
    let raw = u32::from_le_bytes(buf) % pyana_circuit::field::BABYBEAR_P;
    // Ensure non-zero (zero blinding would reveal the raw leaf_hash via hash_2_to_1(x, 0))
    let val = if raw == 0 { 1 } else { raw };
    BabyBear::new(val)
}

/// Generate fresh randomness for the presentation tag.
///
/// This produces a non-zero BabyBear field element from OS randomness.
/// A fresh value is generated per presentation to ensure unlinkability:
/// `presentation_tag = Poseidon2(final_root, presentation_randomness)` is different each time.
/// The final_root remains private; only the blinded tag is public.
fn generate_presentation_randomness() -> BabyBear {
    let mut buf = [0u8; 4];
    getrandom::fill(&mut buf).expect("OS randomness unavailable");
    let raw = u32::from_le_bytes(buf) % pyana_circuit::field::BABYBEAR_P;
    // Ensure non-zero (zero randomness would expose final_root directly via hash_2_to_1(x, 0))
    let val = if raw == 0 { 1 } else { raw };
    BabyBear::new(val)
}

/// Compute the revealed facts commitment for selective disclosure.
///
/// Given a set of `TraceFact`s that the prover chooses to reveal, this function
/// computes `poseidon2(hash(fact_1) || hash(fact_2) || ... || hash(fact_n))`.
/// Each fact is hashed by converting its predicate and terms into BabyBear field
/// elements and applying `poseidon2::hash_fact`.
///
/// The verifier recomputes this from the plaintext revealed facts and checks it
/// matches the commitment in the proof's public inputs. This cryptographically
/// binds the revealed facts to the STARK proof.
///
/// Returns `BabyBear::ZERO` if no facts are provided (fully private mode).
pub fn compute_revealed_facts_commitment(facts: &[pyana_trace::Fact]) -> WideHash {
    if facts.is_empty() {
        return WideHash::ZERO;
    }

    let fact_hashes: Vec<BabyBear> = facts
        .iter()
        .map(|fact| {
            let pred_bb = bytes_to_babybear(&fact.predicate);
            let mut term_bbs = [BabyBear::ZERO; 3];
            for (i, term) in fact.terms.iter().take(3).enumerate() {
                term_bbs[i] = match term {
                    pyana_trace::Term::Const(sym) => bytes_to_babybear(sym),
                    pyana_trace::Term::Int(v) => BabyBear::from_u64(*v as u64),
                    pyana_trace::Term::Var(_) => BabyBear::ZERO,
                };
            }
            poseidon2::hash_fact(pred_bb, &term_bbs)
        })
        .collect();

    WideHash::from_poseidon2("pyana-revealed-facts-v1", &fact_hashes)
}

/// Verify that a set of revealed facts matches the commitment in a proof.
///
/// This is the verifier-side counterpart to [`compute_revealed_facts_commitment`].
/// It recomputes the commitment from the plaintext facts and checks it matches
/// the value committed in the proof's public inputs.
///
/// Returns `true` if the commitment matches (the prover did not lie about revealed facts).
pub fn verify_revealed_facts_commitment(
    revealed_facts: &[pyana_trace::Fact],
    proof_commitment: WideHash,
) -> bool {
    let recomputed = compute_revealed_facts_commitment(revealed_facts);
    recomputed == proof_commitment
}

/// Derive a deterministic sibling hash for Merkle path construction.
/// Only available in test builds or with `test-utils` feature.
/// This is part of the synthetic membership proof infrastructure and
/// MUST NOT be used in production.
#[cfg(any(test, feature = "test-utils"))]
pub fn hash_index(level: usize, sibling_idx: usize, key: &[u8; 32]) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&level.to_le_bytes());
    hasher.update(&sibling_idx.to_le_bytes());
    hasher.update(key);
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
        % (pyana_circuit::field::BABYBEAR_P)
}

/// Default maximum proof age in seconds (5 minutes).
///
/// Proofs older than this are rejected by `verify_presentation` and
/// `verify_presentation_full`. Callers who need a different window should use
/// `verify_presentation_full` with an explicit `max_proof_age`.
pub const DEFAULT_MAX_PROOF_AGE_SECS: i64 = 300;

/// Verify a presentation proof cryptographically with full authorization checks.
///
/// This is the primary verification entry point. It checks:
/// 1. **Issuer membership**: The STARK proof for federation membership is valid.
/// 2. **Federation binding**: The proof's federation root matches `federation_root`.
/// 3. **Timestamp freshness**: The proof's timestamp is within `max_proof_age` seconds of `now`.
/// 4. **Request predicate**: The proof's committed `request_predicate` matches `expected_action`.
///
/// # Arguments
///
/// * `proof` - The presentation proof to verify.
/// * `federation_root` - The federation root of trust from an **external, trusted source**.
///   **SECURITY WARNING**: This MUST NOT come from the proof itself (e.g., `proof.federation_root`).
///   Using the proof's own federation root is circular and provides no security — an attacker
///   can forge a proof for any federation root they choose.
/// * `expected_action` - The action string the verifier expects the proof to authorize.
///   If `None`, the request predicate check is skipped (only safe when the action is
///   already authenticated by other means, e.g., TLS channel binding).
/// * `now` - Current Unix timestamp in seconds for freshness checking.
/// * `max_proof_age` - Maximum age of the proof in seconds. Use `DEFAULT_MAX_PROOF_AGE_SECS`
///   (300s / 5min) for typical interactive authorization.
///
/// # Returns
///
/// `true` if all checks pass, `false` otherwise.
pub fn verify_presentation_full(
    proof: &BridgePresentationProof,
    federation_root: &[u8; 32],
    expected_action: Option<&str>,
    now: i64,
    max_proof_age: i64,
) -> bool {
    // A real STARK proof is required for cryptographic verification.
    let real = match proof.real_stark_proof.as_ref() {
        Some(r) => r,
        None => return false,
    };

    let pi: Vec<BabyBear> = real
        .issuer_membership_stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new(v))
        .collect();

    if pi.len() < 2 {
        return false;
    }

    // 1. Verify that the proof's federation root matches what we expect (EXTERNAL trust anchor).
    let expected_root = bb_from_bytes(federation_root);
    if pi[1] != expected_root {
        return false;
    }

    // 2. Timestamp freshness: reject stale proofs.
    let proof_timestamp = proof.circuit_proof.public_inputs.timestamp;
    let proof_ts_val = proof_timestamp.0 as i64;
    if proof_ts_val == 0 {
        // A zero timestamp means no timestamp was set — reject as stale.
        return false;
    }
    let age = now.saturating_sub(proof_ts_val);
    if age > max_proof_age || age < -max_proof_age {
        // Proof is too old OR has a future timestamp beyond tolerance.
        return false;
    }

    // 3. Request predicate authorization: verify the proof actually authorizes
    //    the action being requested, not just any action.
    //    The action binding is a 4-element commitment with 124-bit security.
    if let Some(action) = expected_action {
        let expected_binding = pyana_circuit::compute_action_binding(action, "");
        if proof.circuit_proof.public_inputs.request_predicate != expected_binding {
            return false;
        }
    }

    // 4. Verify composition commitment (sub-proof binding).
    //    If the STARK proof contains a composition_commitment (pi[3] for blinded,
    //    pi[3] for non-blinded), verify it matches the locally recomputed value
    //    from the fold chain and derivation sub-proofs. This prevents an attacker
    //    from attaching a valid membership STARK from one token to a forged fold
    //    chain from another.
    if !proof.composition_commitment.is_zero() {
        // Recompute the composition commitment from the sub-proof data.
        let fold_chain_commitment = if real.fold_proofs.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = real
                .fold_proofs
                .iter()
                .filter(|fp| fp.public_inputs.len() >= 2)
                .flat_map(|fp| [fp.public_inputs[0], fp.public_inputs[1]])
                .collect();
            if fold_roots.is_empty() {
                BabyBear::ZERO
            } else {
                poseidon2::hash_many(&fold_roots)
            }
        };
        let derivation_state_root = if real.derivation_proof.public_inputs.is_empty() {
            BabyBear::ZERO
        } else {
            real.derivation_proof.public_inputs[0]
        };
        let presentation_tag = proof.circuit_proof.public_inputs.presentation_tag;
        // The circuit PI already stores the narrow (single-element) presentation tag,
        // which is compute_presentation_tag_narrow(). Use it directly — no re-hashing.
        let recomputed = WideHash::from_poseidon2(
            "pyana-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag,
            ],
        );

        if recomputed != proof.composition_commitment {
            return false;
        }

        // Also verify the composition_commitment is present in the STARK's public inputs.
        // Public input layout: [leaf, root, action[4], composition[4]]
        let expected_cc_idx = 6; // After leaf, root, action[4]
        if pi.len() <= expected_cc_idx + 3 {
            return false;
        }
        for i in 0..4 {
            if pi[expected_cc_idx + i] != proof.composition_commitment[i] {
                return false;
            }
        }
    }

    // 5. Verify the real STARK proof.
    //    Dispatch to DSL circuit based on AIR name.
    let air_name = &real.issuer_membership_stark_proof.air_name;
    let circuit =
        pyana_dsl_runtime::descriptors::circuit_for_air_name(air_name).unwrap_or_else(|| {
            if air_name.contains("blinded") {
                pyana_dsl_runtime::descriptors::blinded_merkle_poseidon2_circuit()
            } else {
                pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit()
            }
        });
    stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi).is_ok()
}

/// Verify that a proof's verifier nonce matches the expected challenge.
///
/// In a challenge-response protocol, the verifier issues a random nonce BEFORE
/// the prover generates the proof. This function checks that the proof was generated
/// for the specific challenge the verifier issued, preventing replay attacks.
///
/// Returns `true` if:
/// - The proof's `verifier_nonce` matches `expected_nonce`, OR
/// - `expected_nonce` is `BabyBear::ZERO` (nonce check disabled, non-interactive mode)
///
/// Returns `false` if the nonces do not match (potential replay).
///
/// # Security
///
/// Verifiers operating in challenge-response mode SHOULD:
/// 1. Generate a fresh random nonce per session (at least 31 bits of entropy).
/// 2. Send the nonce to the prover.
/// 3. Call this function with the same nonce after receiving the proof.
/// 4. Reject proofs where this returns `false`.
pub fn verify_presentation_nonce(
    proof: &BridgePresentationProof,
    expected_nonce: BabyBear,
) -> bool {
    // Non-interactive mode: skip nonce check when expected_nonce is zero.
    if expected_nonce == BabyBear::ZERO {
        return true;
    }

    // The nonce is stored in the circuit proof's public inputs.
    proof.circuit_proof.public_inputs.verifier_nonce == expected_nonce
}

// =============================================================================
// Canonical production verifier — ALL production paths MUST use this
// =============================================================================

/// Error type for the canonical proof verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The federation root was all zeros (not configured).
    NoFederationRoot,
    /// Proof deserialization failed.
    DeserializeFailed(String),
    /// STARK verification failed.
    StarkInvalid(String),
    /// Federation root in proof does not match expected root.
    RootMismatch,
    /// Action/resource binding in proof does not match expected values.
    ActionMismatch,
    /// Proof timestamp is too old or missing.
    Expired,
    /// Composition commitment is zero (missing sub-proof binding).
    MissingComposition,
    /// Composition commitment does not match recomputed value.
    CompositionMismatch,
    /// No real STARK proof present (structural/mock proof).
    NoStarkProof,
    /// Proof has fewer public inputs than required.
    MalformedPublicInputs,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoFederationRoot => write!(f, "federation root is zero (not configured)"),
            Self::DeserializeFailed(e) => write!(f, "deserialization failed: {e}"),
            Self::StarkInvalid(e) => write!(f, "STARK verification failed: {e}"),
            Self::RootMismatch => write!(f, "federation root mismatch"),
            Self::ActionMismatch => write!(f, "action/resource binding mismatch"),
            Self::Expired => write!(f, "proof expired or missing timestamp"),
            Self::MissingComposition => write!(f, "composition commitment is zero"),
            Self::CompositionMismatch => write!(f, "composition commitment mismatch"),
            Self::NoStarkProof => write!(f, "no real STARK proof present"),
            Self::MalformedPublicInputs => write!(f, "malformed public inputs"),
        }
    }
}

impl std::error::Error for VerifyError {}

/// Result of successful verification from [`verify_proof_complete`].
#[derive(Clone, Debug)]
pub struct VerifiedPresentation {
    /// The proof tier (informational only — not used for acceptance decisions).
    /// A proof that passes `verify_proof_complete` is always accepted regardless of tier.
    /// The tier is retained for logging, metrics, and diagnostics.
    pub tier: pyana_circuit::ProofTier,
    /// The action the proof was verified against.
    pub action: String,
    /// The resource the proof was verified against.
    pub resource: String,
    /// The federation root the proof was verified against.
    pub federation_root: [u8; 32],
}

/// Configuration for the verification policy.
///
/// This replaces tier-based gating with explicit policy configuration.
/// Devnet accepts all AIRs. Production might restrict to Poseidon2-backed AIRs only.
///
/// # Example
///
/// ```
/// use pyana_bridge::present::VerifierConfig;
///
/// // Production: only accept Poseidon2-backed AIRs.
/// let production = VerifierConfig::production();
///
/// // Devnet: accept any cryptographically valid AIR.
/// let devnet = VerifierConfig::devnet();
/// ```
#[derive(Clone, Debug)]
pub struct VerifierConfig {
    /// Which AIR names are acceptable. Empty means "accept all known AIRs".
    pub accepted_air_names: Vec<String>,
    /// Maximum proof age in seconds. 0 disables freshness check.
    pub max_proof_age_secs: i64,
    /// Whether composition commitment is required (binds sub-proofs together).
    /// Set to `false` for single-step proofs that have no fold chain.
    pub require_composition: bool,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self::production()
    }
}

impl VerifierConfig {
    /// Production config: accepts only Poseidon2-backed AIRs, requires composition,
    /// and enforces a 5-minute freshness window.
    pub fn production() -> Self {
        Self {
            accepted_air_names: vec![
                pyana_dsl_runtime::descriptors::BLINDED_MERKLE_AIR_NAME.to_string(),
                pyana_dsl_runtime::descriptors::MERKLE_POSEIDON2_AIR_NAME.to_string(),
            ],
            max_proof_age_secs: 300,
            require_composition: true,
        }
    }

    /// Devnet config: accepts any cryptographically valid AIR (including the legacy
    /// MerkleStarkAir), with a generous freshness window and relaxed composition.
    pub fn devnet() -> Self {
        Self {
            accepted_air_names: Vec::new(), // empty = accept all known AIRs
            max_proof_age_secs: 3600,
            require_composition: false,
        }
    }

    /// Returns true if the given AIR name is accepted by this config.
    /// An empty `accepted_air_names` list means all known AIRs are accepted.
    pub fn accepts_air(&self, air_name: &str) -> bool {
        self.accepted_air_names.is_empty() || self.accepted_air_names.iter().any(|a| a == air_name)
    }
}

/// The ONLY verification function that should be called in production.
///
/// Checks ALL of:
/// 1. Reject zero federation root
/// 2. Real STARK proof presence
/// 3. STARK validity (issuer membership, cryptographic verification)
/// 4. Federation root binding (proof's root == expected root)
/// 5. Action binding (proof's request_predicate == compute_action_binding(action, resource))
/// 6. Timestamp freshness (proof not older than max_age_secs)
/// 7. Composition commitment (non-zero AND correctly recomputed from sub-proofs)
///
/// Tier is NOT checked for acceptance. If a proof passes cryptographic STARK
/// verification for a known AIR, it is valid. The tier is retained in the
/// returned `VerifiedPresentation` as informational metadata for logging/metrics.
/// Structural stubs cannot produce valid STARK proofs, so they are naturally
/// rejected by step 3 without needing a separate tier gate.
///
/// For deployment-specific policy (restricting which AIRs are accepted), use
/// [`VerifierConfig`] to filter at the caller level.
///
/// # Arguments
///
/// * `wire_proof` - The deserialized wire presentation proof.
/// * `expected_action` - The action string the proof must be bound to.
/// * `expected_resource` - The resource string the proof must be bound to.
/// * `federation_root` - The federation root from an EXTERNAL trusted source.
/// * `current_timestamp` - Current Unix timestamp in seconds.
/// * `max_age_secs` - Maximum age of proof in seconds. 0 disables freshness check.
///
/// # Returns
///
/// `Ok(VerifiedPresentation)` if ALL checks pass.
/// `Err(VerifyError)` with a specific reason on any failure.
pub fn verify_proof_complete(
    wire_proof: &WirePresentationProof,
    expected_action: &str,
    expected_resource: &str,
    federation_root: &[u8; 32],
    current_timestamp: i64,
    max_age_secs: i64,
) -> Result<VerifiedPresentation, VerifyError> {
    // 1. Reject zero federation root.
    if *federation_root == [0u8; 32] {
        return Err(VerifyError::NoFederationRoot);
    }

    // 2. Require a real STARK proof (no structural/mock proofs).
    let real = wire_proof
        .real_stark_proof
        .as_ref()
        .ok_or(VerifyError::NoStarkProof)?;

    // 3. Extract public inputs from the STARK proof.
    let pi: Vec<BabyBear> = real
        .issuer_membership_stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    if pi.len() < 2 + pyana_circuit::ACTION_BINDING_WIDTH {
        return Err(VerifyError::MalformedPublicInputs);
    }

    // 4. Federation root binding: proof's root must match expected.
    // Decode using the canonical bb_from_bytes (inverse of bb_to_bytes).
    let expected_root = bb_from_bytes(federation_root);
    if pi[1] != expected_root {
        return Err(VerifyError::RootMismatch);
    }

    // 5. Action binding: proof must be bound to (expected_action, expected_resource).
    let expected_binding =
        pyana_circuit::compute_action_binding(expected_action, expected_resource);
    if wire_proof.circuit_proof.public_inputs.request_predicate != expected_binding {
        return Err(VerifyError::ActionMismatch);
    }

    // Also verify in STARK public inputs (pi[2..6]).
    for i in 0..pyana_circuit::ACTION_BINDING_WIDTH {
        if pi[2 + i] != expected_binding[i] {
            return Err(VerifyError::ActionMismatch);
        }
    }

    // 6. Timestamp freshness.
    if max_age_secs > 0 {
        let proof_ts = wire_proof.circuit_proof.public_inputs.timestamp.0 as i64;
        if proof_ts == 0 {
            return Err(VerifyError::Expired);
        }
        let age = current_timestamp.saturating_sub(proof_ts);
        if age > max_age_secs || age < -max_age_secs {
            return Err(VerifyError::Expired);
        }
    }

    // 7. Composition commitment (non-zero AND correctly recomputed).
    if wire_proof.composition_commitment.is_zero() {
        // For single-step tokens (no attenuation chain), a zero composition is acceptable
        // only if there are no fold proofs. Multi-step proofs MUST have a non-zero
        // composition commitment to bind the sub-proofs together.
        if !real.fold_proofs.is_empty() {
            return Err(VerifyError::MissingComposition);
        }
    } else {
        // Recompute the composition commitment from the sub-proof data.
        let fold_chain_commitment = if real.fold_proofs.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = real
                .fold_proofs
                .iter()
                .filter(|fp| fp.public_inputs.len() >= 2)
                .flat_map(|fp| [fp.public_inputs[0], fp.public_inputs[1]])
                .collect();
            if fold_roots.is_empty() {
                BabyBear::ZERO
            } else {
                poseidon2::hash_many(&fold_roots)
            }
        };
        let derivation_state_root = if real.derivation_proof.public_inputs.is_empty() {
            BabyBear::ZERO
        } else {
            real.derivation_proof.public_inputs[0]
        };
        let presentation_tag = wire_proof.circuit_proof.public_inputs.presentation_tag;

        let recomputed = WideHash::from_poseidon2(
            "pyana-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag,
            ],
        );

        if recomputed != wire_proof.composition_commitment {
            return Err(VerifyError::CompositionMismatch);
        }

        // Verify the composition_commitment is present in the STARK's public inputs.
        let expected_cc_idx = 6; // After leaf, root, action[4]
        if pi.len() <= expected_cc_idx + 3 {
            return Err(VerifyError::MalformedPublicInputs);
        }
        for i in 0..4 {
            if pi[expected_cc_idx + i] != wire_proof.composition_commitment[i] {
                return Err(VerifyError::CompositionMismatch);
            }
        }
    }

    // 8. STARK cryptographic verification.
    // Dispatches on air_name to select the correct AIR for verification.
    // Any AIR that passes cryptographic verification is accepted — the tier is
    // informational only (per verification-policy-design.md).
    let air_name = &real.issuer_membership_stark_proof.air_name;
    let (stark_result, proof_tier) =
        if let Some(circuit) = pyana_dsl_runtime::descriptors::circuit_for_air_name(air_name) {
            (
                stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi),
                pyana_circuit::ProofTier::Production,
            )
        } else if air_name.contains("blinded") {
            let circuit = pyana_dsl_runtime::descriptors::blinded_merkle_poseidon2_circuit();
            (
                stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi),
                pyana_circuit::ProofTier::Production,
            )
        } else {
            let circuit = pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit();
            (
                stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi),
                pyana_circuit::ProofTier::Production,
            )
        };

    if let Err(e) = stark_result {
        return Err(VerifyError::StarkInvalid(e));
    }

    // Tier is informational only. If the STARK verified cryptographically, the
    // proof is valid. Structural stubs cannot reach this point because they cannot
    // produce valid STARK proofs for any known AIR.

    Ok(VerifiedPresentation {
        tier: proof_tier,
        action: expected_action.to_string(),
        resource: expected_resource.to_string(),
        federation_root: *federation_root,
    })
}

/// Verify a presentation proof cryptographically (convenience wrapper).
///
/// Equivalent to `verify_presentation_full` with:
/// - No action predicate check (`expected_action = None`)
/// - No timestamp freshness check (uses timestamp 0 and max_age of i64::MAX)
///
/// **DEPRECATED**: This function skips action binding and freshness checks.
/// Use [`verify_proof_complete`] instead, which checks EVERYTHING.
///
/// **SECURITY WARNING**: The `federation_root` parameter MUST come from an external
/// trusted source (e.g., the verifier's own configuration, a pinned trust anchor,
/// or a federation registry the verifier operates). It MUST NOT be extracted from
/// the proof being verified (e.g., `proof.federation_root`), as that is circular
/// and provides no security guarantee.
#[deprecated(
    note = "Use verify_proof_complete() which checks action binding, freshness, and composition. This function skips critical security checks."
)]
pub fn verify_presentation(proof: &BridgePresentationProof, federation_root: &[u8; 32]) -> bool {
    // A real STARK proof is required for cryptographic verification.
    if let Some(ref real) = proof.real_stark_proof {
        let pi: Vec<BabyBear> = real
            .issuer_membership_stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new(v))
            .collect();

        if pi.len() < 2 {
            return false;
        }

        // Verify that the proof's federation root matches what we expect.
        let expected_root = bb_from_bytes(federation_root);
        if pi[1] != expected_root {
            return false;
        }

        // Dispatch to DSL circuit based on AIR name.
        let air_name = &real.issuer_membership_stark_proof.air_name;
        let circuit = pyana_dsl_runtime::descriptors::circuit_for_air_name(air_name)
            .unwrap_or_else(|| {
                if air_name.contains("blinded") {
                    pyana_dsl_runtime::descriptors::blinded_merkle_poseidon2_circuit()
                } else {
                    pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit()
                }
            });
        stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi).is_ok()
    } else {
        // No real proof = not verified. Mock proofs provide no security guarantee.
        false
    }
}

/// Verify a presentation proof against a BabyBear-encoded federation root.
///
/// This is the lower-level verification function used when the federation root
/// is already known as a BabyBear field element (e.g., computed from a synthetic
/// Merkle path in tests, or stored directly alongside the federation tree).
///
/// **SECURITY WARNING**: The `expected_root` MUST come from an external trusted source.
/// Do NOT pass a value derived from the proof itself.
pub fn verify_presentation_bb(proof: &BridgePresentationProof, expected_root: BabyBear) -> bool {
    if let Some(ref real) = proof.real_stark_proof {
        let pi: Vec<BabyBear> = real
            .issuer_membership_stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new(v))
            .collect();

        if pi.len() < 2 {
            return false;
        }

        if pi[1] != expected_root {
            return false;
        }

        // Dispatch to DSL circuit based on AIR name.
        let air_name = &real.issuer_membership_stark_proof.air_name;
        let circuit = pyana_dsl_runtime::descriptors::circuit_for_air_name(air_name)
            .unwrap_or_else(|| {
                if air_name.contains("blinded") {
                    pyana_dsl_runtime::descriptors::blinded_merkle_poseidon2_circuit()
                } else {
                    pyana_dsl_runtime::descriptors::merkle_poseidon2_circuit()
                }
            });
        stark::verify(&circuit, &real.issuer_membership_stark_proof, &pi).is_ok()
    } else {
        false
    }
}

/// Verify a presentation proof (legacy API, checks only structural validity).
///
/// **DEPRECATED**: This only checks the prover-set `verification` field and provides
/// no cryptographic guarantee. Use `verify_presentation()` with a federation root instead.
#[deprecated(
    note = "Use verify_presentation(proof, federation_root) for cryptographic verification"
)]
pub fn verify_presentation_structural(proof: &BridgePresentationProof) -> bool {
    proof.is_valid()
}

/// Verify the validated IVC fold chain proof in a presentation.
///
/// This is the verifier-side entry point for validated fold chain proofs.
/// When a `BridgePresentationProof` contains a `validated_ivc_proof`, this
/// function cryptographically verifies:
/// 1. The hash-chain STARK (sequential ordering of root transitions).
/// 2. Each per-step Merkle membership STARK (each removed fact existed in the tree).
/// 3. Root continuity across all steps.
///
/// Returns `true` if the validated IVC proof is present and verifies successfully.
/// Returns `false` if no validated IVC proof is present or verification fails.
///
/// # Arguments
///
/// * `proof` - The presentation proof to verify.
///
/// # Security
///
/// A remote verifier SHOULD call this in addition to `verify_presentation()` (which
/// checks issuer membership). Together they provide full cryptographic guarantees:
/// - Issuer membership STARK: token originated from a federated issuer
/// - Validated IVC: the entire attenuation chain is valid (no fabricated steps)
pub fn verify_fold_chain(proof: &BridgePresentationProof) -> bool {
    match &proof.validated_ivc_proof {
        Some(validated) => {
            pyana_circuit::verify_validated_ivc(validated)
                == pyana_circuit::ValidatedIvcVerification::Valid
        }
        None => false,
    }
}

/// Verify a fold chain with an expected initial root anchor.
///
/// This is the secure variant of [`verify_fold_chain`] that ensures the IVC proof's
/// initial state corresponds to the expected root (e.g., derived from the issuer's
/// original token state). Without this check, a valid IVC proof could start from
/// an arbitrary initial state, allowing an attacker to fabricate the beginning of
/// the attenuation chain.
///
/// # Arguments
///
/// * `proof` - The presentation proof containing the validated IVC proof.
/// * `expected_initial_root` - The expected initial state root (before any attenuations).
///
/// # Security
///
/// Callers MUST provide `expected_initial_root` from a trusted source (e.g., the
/// issuer's committed original state root). If this value comes from the proof itself,
/// the check provides no security.
pub fn verify_fold_chain_anchored(
    proof: &BridgePresentationProof,
    expected_initial_root: BabyBear,
) -> bool {
    match &proof.validated_ivc_proof {
        Some(validated) => {
            // First verify the IVC proof itself is structurally valid.
            if pyana_circuit::verify_validated_ivc(validated)
                != pyana_circuit::ValidatedIvcVerification::Valid
            {
                return false;
            }
            // Then verify the initial root matches the expected anchor.
            validated.initial_root == expected_initial_root
        }
        None => false,
    }
}

/// Verify a wire presentation proof's fold chain (validated IVC).
///
/// Same as [`verify_fold_chain`] but operates on the wire-safe representation.
pub fn verify_wire_fold_chain(proof: &WirePresentationProof) -> bool {
    match &proof.validated_ivc_proof {
        Some(validated) => {
            pyana_circuit::verify_validated_ivc(validated)
                == pyana_circuit::ValidatedIvcVerification::Valid
        }
        None => false,
    }
}

/// Full cryptographic verification of a presentation proof: issuer + fold chain.
///
/// This combines `verify_presentation()` (issuer membership STARK) with
/// `verify_fold_chain()` (validated IVC fold chain STARKs) to provide complete
/// cryptographic verification of the entire proof.
///
/// Returns `true` only if BOTH:
/// 1. The issuer membership STARK verifies against `federation_root`
/// 2. The validated IVC fold chain STARKs verify (if a fold chain is present)
///
/// For proofs without a fold chain (unrestricted tokens), only issuer membership
/// is checked.
///
/// # Arguments
///
/// * `proof` - The presentation proof to verify.
/// * `federation_root` - The 32-byte federation root of trust (external trust anchor).
#[allow(deprecated)] // verify_presentation is deprecated in favor of verify_proof_complete
pub fn verify_presentation_complete(
    proof: &BridgePresentationProof,
    federation_root: &[u8; 32],
) -> bool {
    // 1. Verify issuer membership STARK.
    if !verify_presentation(proof, federation_root) {
        return false;
    }

    // 2. Verify the fold chain if a validated IVC proof is present.
    if proof.validated_ivc_proof.is_some() {
        return verify_fold_chain(proof);
    }

    // 3. No validated IVC proof. Check whether the proof is still complete:
    //    - chain_length <= 1: no fold chain to prove (single-step token).
    //    - real_stark_proof with non-zero composition_commitment: the issuer STARK
    //      cryptographically binds the fold chain via the composition_commitment
    //      public input. This is the standard prove() path for multi-step chains
    //      that don't use IVC recursion. The composition_commitment ensures no
    //      sub-proof substitution is possible.
    if proof.chain_length <= 1 {
        return true;
    }

    // For multi-step chains without IVC, accept if we have a real STARK proof
    // with a valid (non-zero) composition commitment binding the fold chain.
    // SECURITY: We MUST recompute the composition commitment from the sub-proof
    // data and verify it matches the claimed value. Without this, an attacker
    // could forge an arbitrary non-zero commitment that passes the non-zero check.
    let real = match proof.real_stark_proof.as_ref() {
        Some(r) => r,
        None => return false,
    };

    if proof.composition_commitment.is_zero() {
        return false;
    }

    // Recompute composition commitment from the sub-proof data.
    let fold_chain_commitment = if real.fold_proofs.is_empty() {
        BabyBear::ZERO
    } else {
        let fold_roots: Vec<BabyBear> = real
            .fold_proofs
            .iter()
            .filter(|fp| fp.public_inputs.len() >= 2)
            .flat_map(|fp| [fp.public_inputs[0], fp.public_inputs[1]])
            .collect();
        if fold_roots.is_empty() {
            BabyBear::ZERO
        } else {
            poseidon2::hash_many(&fold_roots)
        }
    };
    let derivation_state_root = if real.derivation_proof.public_inputs.is_empty() {
        BabyBear::ZERO
    } else {
        real.derivation_proof.public_inputs[0]
    };
    let presentation_tag = proof.circuit_proof.public_inputs.presentation_tag;
    // The circuit PI already stores the narrow (single-element) presentation tag,
    // which is compute_presentation_tag_narrow(). Use it directly — no re-hashing.
    let recomputed = WideHash::from_poseidon2(
        "pyana-composition-v1",
        &[
            fold_chain_commitment,
            derivation_state_root,
            presentation_tag,
        ],
    );

    if recomputed != proof.composition_commitment {
        return false;
    }

    // Verify the composition_commitment is present in the STARK's public inputs.
    // Public input layout: [leaf, root, action[4], composition[4]]
    let pi: Vec<BabyBear> = real
        .issuer_membership_stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new(v))
        .collect();
    let expected_cc_idx = 6; // After leaf, root, action[4]
    if pi.len() <= expected_cc_idx + 3 {
        return false;
    }
    for i in 0..4 {
        if pi[expected_cc_idx + i] != proof.composition_commitment[i] {
            return false;
        }
    }

    true
}

// =============================================================================
// Predicate Proofs
// =============================================================================

/// A predicate that can be proven about a private token attribute.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Predicate {
    /// Prove `attribute >= threshold`.
    Gte(u32),
    /// Prove `attribute <= threshold`.
    Lte(u32),
    /// Prove `attribute > threshold`.
    Gt(u32),
    /// Prove `attribute < threshold`.
    Lt(u32),
    /// Prove `attribute != target`.
    Neq(u32),
    /// Prove `low <= attribute <= high`.
    InRange(u32, u32),
}

/// A predicate proof over a token attribute, ready for verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BridgePredicateProof {
    /// The predicate that was proven.
    pub predicate: Predicate,
    /// The underlying circuit proof(s).
    pub proof: BridgePredicateProofInner,
    /// The fact commitment (public input -- binds the proof to a specific token state).
    pub fact_commitment: BabyBear,
}

/// Inner proof representation -- single proof for simple predicates, pair for InRange.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BridgePredicateProofInner {
    /// A single predicate proof (GTE, LTE, GT, LT, NEQ).
    Single(pyana_circuit::PredicateProof),
    /// A pair of proofs for InRange (lower bound + upper bound).
    Range(pyana_circuit::PredicateProof, pyana_circuit::PredicateProof),
    /// A committed-threshold proof where both value and threshold are hidden.
    CommittedThreshold(pyana_circuit::CommittedThresholdProof),
}

/// Generate a predicate proof for a specific fact attribute in a token state.
///
/// This is the primary predicate proof entry point. The prover specifies:
/// - `private_value`: The actual value of the attribute (kept private).
/// - `fact_hash`: The Poseidon2 hash of the fact containing the attribute.
/// - `state_root`: The Poseidon2 root of the token state containing the fact.
/// - `predicate`: The statement to prove.
///
/// The verifier will receive only:
/// - The predicate type and threshold (public).
/// - The fact_commitment = Poseidon2(fact_hash, state_root) (public).
/// - The proof (cryptographic).
///
/// They learn that "some value in the committed fact satisfies the predicate"
/// without learning the actual value.
///
/// # Returns
///
/// `Some(BridgePredicateProof)` if the statement is true and the proof generates
/// successfully, `None` if the statement is false or proof generation fails.
pub fn prove_predicate_for_fact(
    private_value: u32,
    fact_hash: BabyBear,
    state_root: BabyBear,
    predicate: &Predicate,
) -> Option<BridgePredicateProof> {
    let value_bb = BabyBear::new(private_value);
    let fact_commitment = pyana_circuit::compute_fact_commitment(fact_hash, state_root);

    match predicate {
        Predicate::InRange(low, high) => {
            let (low_proof, high_proof) = pyana_circuit::prove_in_range(
                value_bb,
                BabyBear::new(*low),
                BabyBear::new(*high),
                fact_commitment,
            )?;
            Some(BridgePredicateProof {
                predicate: predicate.clone(),
                proof: BridgePredicateProofInner::Range(low_proof, high_proof),
                fact_commitment,
            })
        }
        _ => {
            let (threshold, predicate_type) = match predicate {
                Predicate::Gte(t) => (*t, pyana_circuit::PredicateType::Gte),
                Predicate::Lte(t) => (*t, pyana_circuit::PredicateType::Lte),
                Predicate::Gt(t) => (*t, pyana_circuit::PredicateType::Gt),
                Predicate::Lt(t) => (*t, pyana_circuit::PredicateType::Lt),
                Predicate::Neq(t) => (*t, pyana_circuit::PredicateType::Neq),
                Predicate::InRange(..) => unreachable!(),
            };

            let witness = pyana_circuit::PredicateWitness {
                private_value: value_bb,
                threshold: BabyBear::new(threshold),
                predicate_type,
                fact_commitment,
                blinding: None,
                fact_hash: Some(fact_hash),
                state_root: Some(state_root),
            };

            let proof = pyana_circuit::prove_predicate(witness)?;
            Some(BridgePredicateProof {
                predicate: predicate.clone(),
                proof: BridgePredicateProofInner::Single(proof),
                fact_commitment,
            })
        }
    }
}

/// Verify a predicate proof.
///
/// The verifier provides:
/// - The proof to verify.
/// - The expected fact_commitment (which the verifier must independently derive
///   from the token state they trust).
///
/// Returns `true` if the proof is valid for the given commitment.
pub fn verify_predicate_proof(
    proof: &BridgePredicateProof,
    expected_fact_commitment: BabyBear,
) -> bool {
    if proof.fact_commitment != expected_fact_commitment {
        return false;
    }

    match &proof.proof {
        BridgePredicateProofInner::Single(inner) => {
            let threshold = match &proof.predicate {
                Predicate::Gte(t)
                | Predicate::Lte(t)
                | Predicate::Gt(t)
                | Predicate::Lt(t)
                | Predicate::Neq(t) => BabyBear::new(*t),
                Predicate::InRange(..) => return false,
            };
            pyana_circuit::verify_predicate(inner, threshold, expected_fact_commitment)
        }
        BridgePredicateProofInner::Range(low_proof, high_proof) => {
            let (low, high) = match &proof.predicate {
                Predicate::InRange(l, h) => (BabyBear::new(*l), BabyBear::new(*h)),
                _ => return false,
            };
            pyana_circuit::verify_in_range(
                low_proof,
                high_proof,
                low,
                high,
                expected_fact_commitment,
            )
        }
        BridgePredicateProofInner::CommittedThreshold(ct_proof) => {
            // For committed-threshold proofs, verify against the threshold commitment
            // embedded in the proof. The verifier must independently check the
            // threshold_commitment against their expected value.
            pyana_circuit::verify_committed_threshold(
                ct_proof,
                ct_proof.threshold_commitment,
                expected_fact_commitment,
            )
        }
    }
}

// =============================================================================
// Committed-Threshold Proofs (private threshold from verifier)
// =============================================================================

/// A committed-threshold proof: proves `value >= threshold` without revealing
/// either value or threshold to third-party verifiers.
///
/// The verifier commits to their threshold: `Poseidon2(threshold, blinding)`.
/// The prover proves: value >= threshold AND the commitment is correct.
/// Public inputs are only the two commitments (threshold + fact).
#[derive(Clone, Debug)]
pub struct BridgeCommittedThresholdProof {
    /// The circuit-level proof.
    pub proof: pyana_circuit::CommittedThresholdProof,
    /// The threshold commitment (for verifier cross-check).
    pub threshold_commitment: BabyBear,
    /// The fact commitment (binding to token state).
    pub fact_commitment: BabyBear,
}

/// Generate a committed-threshold proof for a specific fact attribute.
///
/// This is the primary entry point for the committed-threshold protocol.
///
/// # Arguments
///
/// - `private_value`: The prover's private attribute value (kept hidden from verifier).
/// - `threshold`: The verifier's threshold (received from verifier via secure channel).
/// - `blinding`: The verifier's blinding factor (received from verifier via secure channel).
/// - `fact_hash`: Poseidon2 hash of the fact containing the attribute.
/// - `state_root`: Poseidon2 root of the token state containing the fact.
///
/// # Returns
///
/// `Some(BridgeCommittedThresholdProof)` if value >= threshold and proof succeeds,
/// `None` if the statement is false or proof generation fails.
///
/// # Privacy
///
/// Third-party verifiers see only:
/// - `threshold_commitment = Poseidon2(threshold, blinding)` — hides the threshold.
/// - `fact_commitment = Poseidon2(fact_hash, state_root)` — hides the value.
///
/// They learn ONLY that "the committed value satisfies the committed threshold."
pub fn prove_committed_threshold(
    private_value: u32,
    threshold: u32,
    blinding: u32,
    fact_hash: BabyBear,
    state_root: BabyBear,
) -> Option<BridgeCommittedThresholdProof> {
    let value_bb = BabyBear::new(private_value);
    let threshold_bb = BabyBear::new(threshold);
    let blinding_bb = BabyBear::new(blinding);
    let fact_commitment = pyana_circuit::compute_fact_commitment(fact_hash, state_root);

    let witness = pyana_circuit::CommittedThresholdWitness {
        private_value: value_bb,
        threshold: threshold_bb,
        blinding: blinding_bb,
        fact_commitment,
    };

    let threshold_commitment = witness.compute_threshold_commitment();
    let proof = pyana_circuit::prove_committed_threshold(witness)?;

    Some(BridgeCommittedThresholdProof {
        proof,
        threshold_commitment,
        fact_commitment,
    })
}

/// Verify a committed-threshold proof.
///
/// # For the verifier (who knows their threshold):
///
/// ```ignore
/// let expected_commitment = pyana_circuit::compute_threshold_commitment(
///     BabyBear::new(my_threshold), BabyBear::new(my_blinding)
/// );
/// let valid = verify_committed_threshold_proof(&proof, expected_commitment, fact_commitment);
/// ```
///
/// # For third-party auditors (who know neither value nor threshold):
///
/// They verify against the commitments they received from the protocol participants.
/// They learn only: "this proof is valid for these commitments" (1 bit).
pub fn verify_committed_threshold_proof(
    proof: &BridgeCommittedThresholdProof,
    expected_threshold_commitment: BabyBear,
    expected_fact_commitment: BabyBear,
) -> bool {
    pyana_circuit::verify_committed_threshold(
        &proof.proof,
        expected_threshold_commitment,
        expected_fact_commitment,
    )
}

// =============================================================================
// Programmable Predicate Programs
// =============================================================================

/// Error from the predicate program proving pipeline.
#[derive(Clone, Debug)]
pub enum ProgramProveError {
    /// Compilation failed.
    CompileError(pyana_circuit::predicate_program::CompileError),
    /// Proof generation failed.
    ProveError(pyana_circuit::predicate_program::ProveError),
}

impl std::fmt::Display for ProgramProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CompileError(e) => write!(f, "compile error: {e}"),
            Self::ProveError(e) => write!(f, "prove error: {e}"),
        }
    }
}

impl From<pyana_circuit::predicate_program::CompileError> for ProgramProveError {
    fn from(e: pyana_circuit::predicate_program::CompileError) -> Self {
        Self::CompileError(e)
    }
}

impl From<pyana_circuit::predicate_program::ProveError> for ProgramProveError {
    fn from(e: pyana_circuit::predicate_program::ProveError) -> Self {
        Self::ProveError(e)
    }
}

/// Compile and prove a predicate program in one step.
///
/// This is the primary bridge-level entry point for the programmable predicates
/// pipeline. It takes a high-level program specification and private values,
/// compiles the program to AIR(s), and generates the appropriate proof(s).
///
/// # Arguments
///
/// * `program` - The predicate program to prove.
/// * `private_values` - Map from attribute names to private values.
/// * `state_root` - The Poseidon2 root of the current token state.
///
/// # Returns
///
/// A `ProgramProof` that can be verified by anyone knowing the public inputs,
/// or a `ProgramProveError` if compilation or proof generation fails.
///
/// # Example
///
/// ```ignore
/// use pyana_circuit::predicate_program::{PredicateExpr, PredicateProgram};
/// use pyana_circuit::predicate_air::PredicateType;
/// use pyana_circuit::BabyBear;
/// use std::collections::HashMap;
///
/// let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
///     attribute: "balance".to_string(),
///     predicate_type: PredicateType::Gte,
///     threshold: 1000,
/// });
///
/// let mut values = HashMap::new();
/// values.insert("balance".to_string(), 5000u64);
///
/// let proof = pyana_bridge::prove_predicate_program(
///     &program, &values, BabyBear::new(99999),
/// ).unwrap();
/// ```
pub fn prove_predicate_program(
    program: &pyana_circuit::predicate_program::PredicateProgram,
    private_values: &std::collections::HashMap<String, u64>,
    state_root: BabyBear,
) -> Result<pyana_circuit::predicate_program::ProgramProof, ProgramProveError> {
    use pyana_circuit::predicate_program::{PrivateState, compile_predicate, prove_program};

    // Compile the program to a proof plan.
    let compiled = compile_predicate(program)?;

    // Build the private state from the provided values.
    let mut private_state = PrivateState::default();
    private_state.values = private_values.clone();

    // Generate the proof.
    let proof = prove_program(&compiled, &private_state, state_root)?;
    Ok(proof)
}

/// Compile and prove a predicate program with full private state (including temporal history).
///
/// This is the extended version of [`prove_predicate_program`] that supports
/// temporal predicates by accepting full [`PrivateState`] including historical
/// values and state roots.
pub fn prove_predicate_program_full(
    program: &pyana_circuit::predicate_program::PredicateProgram,
    private_state: &pyana_circuit::predicate_program::PrivateState,
    state_root: BabyBear,
) -> Result<pyana_circuit::predicate_program::ProgramProof, ProgramProveError> {
    use pyana_circuit::predicate_program::{compile_predicate, prove_program};

    let compiled = compile_predicate(program)?;
    let proof = prove_program(&compiled, private_state, state_root)?;
    Ok(proof)
}

/// Verify a predicate program proof.
///
/// The verifier provides:
/// - The program (they know what was proven).
/// - The proof to verify.
/// - Expected fact commitments for each attribute.
/// - The state root the proofs are bound to.
///
/// Returns `true` if the proof is valid.
pub fn verify_predicate_program(
    program: &pyana_circuit::predicate_program::PredicateProgram,
    proof: &pyana_circuit::predicate_program::ProgramProof,
    expected_commitments: &std::collections::HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    use pyana_circuit::predicate_program::{compile_predicate, verify_program};

    let compiled = match compile_predicate(program) {
        Ok(c) => c,
        Err(_) => return false,
    };

    verify_program(proof, &compiled, expected_commitments, state_root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_circuit::ConstraintProver;

    fn test_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[1] = 0x13;
        key[31] = 0xFF;
        key
    }

    fn test_federation_root() -> [u8; 32] {
        let mut root = [0u8; 32];
        root[0] = 0xFE;
        root[1] = 0xDE;
        root[31] = 0x01;
        root
    }

    #[test]
    fn test_builder_new() {
        let builder = BridgePresentationBuilder::new(test_key(), test_federation_root());
        assert_eq!(builder.chain_length(), 0);
    }

    #[test]
    fn test_builder_set_root_token() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        builder.set_root_token(token);
        assert_eq!(builder.chain_length(), 1);
        assert!(builder.final_state().is_some());
    }

    #[test]
    fn test_builder_add_attenuation() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        builder.set_root_token(token);

        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };

        let result = builder.add_attenuation(&att);
        assert!(result);
        assert_eq!(builder.chain_length(), 2);
    }

    #[test]
    fn test_builder_multiple_attenuations() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        builder.set_root_token(token);

        // First attenuation: restrict to an app.
        let att1 = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };
        assert!(builder.add_attenuation(&att1));
        assert_eq!(builder.chain_length(), 2);

        // Second attenuation: add user confinement.
        let att2 = Attenuation {
            confine_user: Some("alice".into()),
            ..Default::default()
        };
        assert!(builder.add_attenuation(&att2));
        assert_eq!(builder.chain_length(), 3);
    }

    #[test]
    fn test_builder_verify_chain() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        builder.set_root_token(token);

        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };
        builder.add_attenuation(&att);

        assert!(builder.verify_chain());
    }

    #[test]
    fn test_builder_empty_attenuation_fails() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        builder.set_root_token(token);

        let att = Attenuation::default();
        assert!(!builder.add_attenuation(&att));
    }

    #[test]
    fn test_builder_attenuation_without_root_fails() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());

        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };
        assert!(!builder.add_attenuation(&att));
    }

    #[test]
    fn test_bytes_to_babybear_vec() {
        // Multi-limb encoding should preserve all 32 bytes.
        let mut bytes = [0u8; 32];
        bytes[0] = 1;
        bytes[31] = 0xFF;
        let limbs = bytes_to_babybear_vec(&bytes);
        assert_eq!(limbs.len(), 8);
        // First limb encodes bytes[0..4]: value 1
        assert_eq!(limbs[0], BabyBear::new(1));
        // Last limb encodes bytes[28..32]: 0xFF000000 = 4278190080, mod p
        let expected_last = BabyBear::new(0xFF000000u32);
        assert_eq!(limbs[7], expected_last);
    }

    #[test]
    fn test_bytes_to_babybear_hash() {
        // Poseidon2-compressed hash should be deterministic and non-trivial.
        let bytes = [0u8; 32];
        let h1 = bytes_to_babybear(&bytes);
        let h2 = bytes_to_babybear(&bytes);
        assert_eq!(h1, h2);

        // Different inputs should produce different hashes.
        let mut bytes2 = [0u8; 32];
        bytes2[16] = 1; // Change a byte in the middle (was invisible to old 4-byte truncation).
        let h3 = bytes_to_babybear(&bytes2);
        assert_ne!(
            h1, h3,
            "bytes differing only beyond byte 3 must produce different hashes"
        );
    }

    #[test]
    fn test_hash_index_deterministic() {
        let key = test_key();
        let h1 = hash_index(0, 0, &key);
        let h2 = hash_index(0, 0, &key);
        assert_eq!(h1, h2);

        let h3 = hash_index(0, 1, &key);
        assert_ne!(h1, h3); // Different sibling index should give different hash.
    }

    #[test]
    fn test_build_issuer_membership_rejects_wrong_root() {
        // With an arbitrary federation_root that doesn't match the synthetic
        // Merkle path, the builder should return IssuerNotInFederation.
        let key = test_key();
        let builder = BridgePresentationBuilder::new(key, test_federation_root());
        let issuer_hash = bytes_to_babybear(&key);

        let result = builder.build_issuer_membership(issuer_hash);
        assert!(
            result.is_err(),
            "Synthetic proof should fail against an unrelated federation root"
        );
        assert_eq!(result.unwrap_err(), AuthError::IssuerNotInFederation);
    }

    #[test]
    fn test_build_issuer_membership_accepts_matching_root() {
        // Compute the "correct" federation root from the synthetic path,
        // then verify the builder accepts it when using new_with_root_bb.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // First, compute what root the synthetic path produces.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = MerkleAir::compute_parent(current, position, &siblings);
        }
        let expected_root_bb = current;

        // Use new_with_root_bb so the federation root check passes.
        let builder = BridgePresentationBuilder::new_with_root_bb(
            key,
            test_federation_root(),
            expected_root_bb,
        );
        let result = builder.build_issuer_membership(issuer_hash);
        assert!(result.is_ok(), "Should succeed with matching root");

        let witness = result.unwrap();
        assert_eq!(witness.leaf_hash, issuer_hash);
        assert_eq!(witness.levels.len(), 8);
        assert_eq!(witness.expected_root, expected_root_bb);

        // The Merkle AIR should verify this witness.
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Issuer membership Merkle proof should verify"
        );
    }

    #[test]
    fn test_with_federation_tree() {
        // Create a federation tree and insert an issuer key.
        let key = test_key();
        let mut tree = MerkleTree::new();
        tree.insert(&key);

        let mut builder = BridgePresentationBuilder::new(key, [0u8; 32]);
        builder.with_federation_tree(tree);

        // The builder's federation_root should now match the tree's root.
        assert_ne!(builder.federation_root, [0u8; 32]);
    }

    #[test]
    fn test_build_issuer_membership_poseidon2_rejects_wrong_root() {
        let key = test_key();
        let builder = BridgePresentationBuilder::new(key, test_federation_root());
        let issuer_hash = bytes_to_babybear(&key);

        let result = builder.build_issuer_membership_poseidon2(issuer_hash);
        assert!(
            result.is_err(),
            "Poseidon2 synthetic proof should fail against an unrelated federation root"
        );
        assert_eq!(result.unwrap_err(), AuthError::IssuerNotInFederation);
    }

    #[test]
    fn test_build_issuer_membership_poseidon2_accepts_matching_root() {
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // Compute the Poseidon2-based federation root.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
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
            current = poseidon2::hash_4_to_1(&children);
        }
        let expected_root_bb = current;

        let builder = BridgePresentationBuilder::new_with_root_bb(
            key,
            test_federation_root(),
            expected_root_bb,
        );
        let result = builder.build_issuer_membership_poseidon2(issuer_hash);
        assert!(
            result.is_ok(),
            "Poseidon2 proof should succeed with matching root"
        );

        let witness = result.unwrap();
        assert_eq!(witness.leaf_hash, issuer_hash);
        assert_eq!(witness.levels.len(), 8);
        assert_eq!(witness.expected_root, expected_root_bb);
    }

    #[test]
    fn test_prove_real_poseidon2() {
        // Compute the Poseidon2-based federation root for the test key.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
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
            current = poseidon2::hash_4_to_1(&children);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-p2", "pyana.dev");
        builder.set_root_token(token);

        // Use unrestricted token (no attenuations) to avoid pre-existing
        // fold chain constraint failures. The UNRESTRICTED rule (rule 3)
        // will fire, allowing authorization without fold steps.
        let request = AuthRequest {
            action: Some("anything".into()),
            ..Default::default()
        };

        let proof = builder.prove(&request);
        assert!(
            proof.is_ok(),
            "prove() with Poseidon2 should succeed: {:?}",
            proof.err()
        );

        let proof = proof.unwrap();
        assert!(
            proof.has_real_stark_proof(),
            "Should have a real STARK proof"
        );

        // Verify the STARK proof cryptographically
        let stark_verify = proof.verify_issuer_stark();
        assert!(
            stark_verify.is_some(),
            "Should have a STARK proof to verify"
        );
        assert!(
            stark_verify.unwrap().is_ok(),
            "Poseidon2 STARK proof should verify"
        );

        // Check proof size is reasonable
        let proof_bytes = proof.issuer_proof_bytes().unwrap();
        assert!(
            proof_bytes.len() > 1000,
            "Real Poseidon2 STARK proof should be > 1KB, got {} bytes",
            proof_bytes.len()
        );
    }

    #[test]
    fn test_ring_membership_unlinkable() {
        // Same issuer, two presentations: verify blinded_leaf is different (unlinkable).
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // Compute the Poseidon2-based federation root.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
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
            current = poseidon2::hash_4_to_1(&children);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        // Generate two proofs from the same issuer.
        let mut builder1 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token1 = MacaroonToken::mint(key, b"kid-ring1", "pyana.dev");
        builder1.set_root_token(token1);

        let mut builder2 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token2 = MacaroonToken::mint(key, b"kid-ring2", "pyana.dev");
        builder2.set_root_token(token2);

        let request = AuthRequest {
            action: Some("ring-test".into()),
            ..Default::default()
        };

        let proof1 = builder1.prove(&request).expect("proof1 should succeed");
        let proof2 = builder2.prove(&request).expect("proof2 should succeed");

        // Both should have real STARK proofs.
        assert!(proof1.has_real_stark_proof());
        assert!(proof2.has_real_stark_proof());

        // Both should verify successfully.
        let v1 = proof1.verify_issuer_stark().unwrap();
        let v2 = proof2.verify_issuer_stark().unwrap();
        assert!(v1.is_ok(), "proof1 should verify: {:?}", v1.err());
        assert!(v2.is_ok(), "proof2 should verify: {:?}", v2.err());

        // The blinded_leaf (pi[0]) should be DIFFERENT between the two proofs.
        // This is the unlinkability property!
        let pi1 = &proof1
            .real_stark_proof
            .as_ref()
            .unwrap()
            .issuer_membership_stark_proof
            .public_inputs;
        let pi2 = &proof2
            .real_stark_proof
            .as_ref()
            .unwrap()
            .issuer_membership_stark_proof
            .public_inputs;
        assert_ne!(
            pi1[0], pi2[0],
            "Same issuer's two presentations must have different blinded_leaf (unlinkable)"
        );

        // But the federation root (pi[1]) should be the SAME.
        assert_eq!(
            pi1[1], pi2[1],
            "Both proofs should have the same federation root"
        );

        // The AIR name should indicate blinded mode.
        assert_eq!(
            proof1
                .real_stark_proof
                .as_ref()
                .unwrap()
                .issuer_membership_stark_proof
                .air_name,
            pyana_dsl_runtime::descriptors::BLINDED_MERKLE_AIR_NAME,
            "Proof should use blinded AIR"
        );
    }

    #[test]
    fn test_ring_membership_verifies_against_federation_root() {
        // A blinded proof should verify against the correct federation root.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
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
            current = poseidon2::hash_4_to_1(&children);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-verify", "pyana.dev");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("verify-test".into()),
            ..Default::default()
        };

        let proof = builder.prove(&request).expect("proof should succeed");

        // Verify against correct root succeeds.
        assert!(
            verify_presentation_bb(&proof, fed_root_bb),
            "Blinded proof should verify against correct federation root"
        );

        // Verify against wrong root fails.
        assert!(
            !verify_presentation_bb(&proof, BabyBear::new(99999)),
            "Blinded proof should fail against wrong federation root"
        );
    }

    #[test]
    fn test_ring_membership_invalid_issuer_fails() {
        // An issuer NOT in the tree should fail proof generation.
        let key = test_key();
        let wrong_root = test_federation_root(); // This won't match the synthetic path

        let mut builder = BridgePresentationBuilder::new(key, wrong_root);
        let token = MacaroonToken::mint(key, b"kid-invalid", "pyana.dev");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("invalid-test".into()),
            ..Default::default()
        };

        // prove() should fail because the issuer is not in the federation
        // (wrong_root doesn't match the synthetic Poseidon2 path).
        let result = builder.prove(&request);
        assert!(
            result.is_err(),
            "Proof generation should fail for non-member issuer"
        );
    }

    #[test]
    fn test_compute_revealed_facts_commitment_empty() {
        // Empty facts should produce ZERO commitment.
        let commitment = super::compute_revealed_facts_commitment(&[]);
        assert!(commitment.is_zero());
    }

    #[test]
    fn test_compute_revealed_facts_commitment_deterministic() {
        use pyana_trace::{Fact, Term, symbol_from_str};

        let facts = vec![
            Fact::new(
                symbol_from_str("service"),
                vec![Term::Const(symbol_from_str("dns"))],
            ),
            Fact::new(
                symbol_from_str("action"),
                vec![Term::Const(symbol_from_str("read"))],
            ),
        ];

        let c1 = super::compute_revealed_facts_commitment(&facts);
        let c2 = super::compute_revealed_facts_commitment(&facts);
        assert_eq!(c1, c2, "commitment must be deterministic");
        assert!(
            !c1.is_zero(),
            "non-empty facts must produce non-zero commitment"
        );
    }

    #[test]
    fn test_compute_revealed_facts_commitment_different_facts_differ() {
        use pyana_trace::{Fact, Term, symbol_from_str};

        let facts_a = vec![Fact::new(
            symbol_from_str("service"),
            vec![Term::Const(symbol_from_str("dns"))],
        )];
        let facts_b = vec![Fact::new(
            symbol_from_str("service"),
            vec![Term::Const(symbol_from_str("storage"))],
        )];

        let ca = super::compute_revealed_facts_commitment(&facts_a);
        let cb = super::compute_revealed_facts_commitment(&facts_b);
        assert_ne!(ca, cb, "different facts must produce different commitments");
    }

    #[test]
    fn test_verify_revealed_facts_commitment_matches() {
        use pyana_trace::{Fact, Term, symbol_from_str};

        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];

        let commitment = super::compute_revealed_facts_commitment(&facts);
        assert!(
            super::verify_revealed_facts_commitment(&facts, commitment),
            "same facts should verify against their own commitment"
        );
    }

    #[test]
    fn test_verify_revealed_facts_commitment_rejects_wrong_facts() {
        use pyana_trace::{Fact, Term, symbol_from_str};

        let real_facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];
        let fake_facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("evil"))],
        )];

        let commitment = super::compute_revealed_facts_commitment(&real_facts);
        assert!(
            !super::verify_revealed_facts_commitment(&fake_facts, commitment),
            "different facts must NOT verify against the original commitment"
        );
    }

    #[test]
    fn test_verify_revealed_facts_commitment_order_sensitive() {
        use pyana_trace::{Fact, Term, symbol_from_str};

        let facts_ab = vec![
            Fact::new(
                symbol_from_str("a"),
                vec![Term::Const(symbol_from_str("x"))],
            ),
            Fact::new(
                symbol_from_str("b"),
                vec![Term::Const(symbol_from_str("y"))],
            ),
        ];
        let facts_ba = vec![
            Fact::new(
                symbol_from_str("b"),
                vec![Term::Const(symbol_from_str("y"))],
            ),
            Fact::new(
                symbol_from_str("a"),
                vec![Term::Const(symbol_from_str("x"))],
            ),
        ];

        let ca = super::compute_revealed_facts_commitment(&facts_ab);
        let cb = super::compute_revealed_facts_commitment(&facts_ba);
        // Order matters since Poseidon2 sponge is sequential.
        assert_ne!(
            ca, cb,
            "different ordering should produce different commitments"
        );
    }

    #[test]
    fn test_presentation_tag_unlinkable_multi_show() {
        // Phase 2 unlinkability test: same wallet, same token, two presentations
        // must produce different presentation_tags. Both proofs must verify.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // Compute the Poseidon2-based federation root.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
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
            current = poseidon2::hash_4_to_1(&children);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        // Generate two presentations from the SAME token (same wallet, same key).
        let mut builder1 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token1 = MacaroonToken::mint(key, b"kid-tag-test", "pyana.dev");
        builder1.set_root_token(token1);

        let mut builder2 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token2 = MacaroonToken::mint(key, b"kid-tag-test", "pyana.dev");
        builder2.set_root_token(token2);

        let request = AuthRequest {
            action: Some("tag-unlinkable".into()),
            ..Default::default()
        };

        let proof1 = builder1.prove(&request).expect("proof1 should succeed");
        let proof2 = builder2.prove(&request).expect("proof2 should succeed");

        // Both proofs should be cryptographically valid.
        assert!(proof1.has_real_stark_proof());
        assert!(proof2.has_real_stark_proof());
        let v1 = proof1.verify_issuer_stark().unwrap();
        let v2 = proof2.verify_issuer_stark().unwrap();
        assert!(v1.is_ok(), "proof1 should verify: {:?}", v1.err());
        assert!(v2.is_ok(), "proof2 should verify: {:?}", v2.err());

        // Both should verify against the federation root.
        assert!(
            verify_presentation_bb(&proof1, fed_root_bb),
            "proof1 should verify against federation root"
        );
        assert!(
            verify_presentation_bb(&proof2, fed_root_bb),
            "proof2 should verify against federation root"
        );

        // UNLINKABILITY: The presentation_tags must be DIFFERENT.
        // Same token, same action, but fresh randomness per presentation.
        let tag1 = proof1.circuit_proof.public_inputs.presentation_tag;
        let tag2 = proof2.circuit_proof.public_inputs.presentation_tag;
        assert_ne!(
            tag1, tag2,
            "Same token, two presentations must produce different presentation_tags (unlinkable)"
        );

        // ALSO: the blinded_leaf in the STARK proof should differ (ring membership unlinkability).
        let stark_pi1 = &proof1
            .real_stark_proof
            .as_ref()
            .unwrap()
            .issuer_membership_stark_proof
            .public_inputs;
        let stark_pi2 = &proof2
            .real_stark_proof
            .as_ref()
            .unwrap()
            .issuer_membership_stark_proof
            .public_inputs;
        assert_ne!(
            stark_pi1[0], stark_pi2[0],
            "Same issuer's two presentations must have different blinded_leaf"
        );

        // But the federation root (pi[1]) should be the same.
        assert_eq!(
            stark_pi1[1], stark_pi2[1],
            "Both proofs should have the same federation root"
        );
    }
}
