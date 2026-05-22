//! Alternative proof backends for pyana circuits.
//!
//! While the primary STARK backend (`crate::stark`) uses BabyBear + FRI,
//! these backends provide alternative proof systems with different tradeoffs:
//!
//! - **Binius** (binary field towers): Operates natively over GF(2) tower extensions,
//!   producing very small proofs for hash-intensive circuits. Uses Groestl-256 (AES-based)
//!   which is native to the binary tower. Post-quantum secure. Expected ~1-4 KiB proofs
//!   for Merkle membership. Always compiled; structural validation without feature flag.
//!
//! - **Mina/Kimchi** (Plonk variant over Pasta curves with IPA): Experimental
//!   Pickles-style IVC over the Pasta cycle. This path generates Kimchi proofs
//!   and verifies base-step proofs with Kimchi, but multi-step standalone
//!   transitivity still requires the in-circuit IPA verifier gadget. NOT
//!   post-quantum secure.
//!
//! # Trait Hierarchy
//!
//! The backend capability surface is organized as a set of focused traits:
//!
//! ```text
//! ProofBackend (membership + fold — original, backward-compatible)
//!     │
//!     ├── DerivationBackend (rule application proofs)
//!     ├── PredicateBackend (arithmetic, relational, temporal, compound)
//!     ├── AccumulatorBackend (non-membership / non-revocation)
//!     ├── IvcBackend (fold chain composition into constant-size proof)
//!     ├── PresentationBackend (full composed authorization statement)
//!     └── CrossStateBackend (cross-state derivation composition)
//!
//! FullProofBackend: ProofBackend + DerivationBackend + PredicateBackend
//!                 + AccumulatorBackend + IvcBackend + PresentationBackend
//!                 + CrossStateBackend
//! ```
//!
//! Backends implement whichever traits they support. The `FullProofBackend`
//! supertrait is a convenience bound for code that requires the complete surface
//! (e.g., the Kimchi/Pickles recursive pipeline).

#[cfg(feature = "mina")]
pub mod mina;

/// Native Kimchi circuit backend: implements pyana's core proof statements
/// (derivation, non-membership) as native Kimchi circuits over Fp.
///
/// Uses Mina-native Poseidon hashing (different commitments from the BabyBear
/// STARK backend). Cross-backend interop requires commitment translation.
/// Enables: recursive STARK composition via Pickles, FOR-ALL quantification
/// over committed sets, native L1 verification on Mina.
#[cfg(feature = "mina")]
pub mod kimchi_native;

/// SP1 backend: Succinct's RISC-V zkVM for provable Datalog evaluation.
///
/// Always compiled. When the `sp1` feature is enabled, uses sp1-sdk for real
/// proof generation via the zkVM. Without the feature, provides structural
/// stubs that validate circuit logic and produce simulated proofs (same pattern
/// as the binius backend).
pub mod sp1;

/// Binius backend: binary field tower proof system using Groestl-256 hashing.
///
/// Always compiled. When the `binius` feature is enabled, provides full proof
/// generation and verification using the Binius binary tower library from
/// IrreducibleOSS. Without the feature, provides structural validation that
/// verifies circuit logic and produces structurally-correct proofs.
pub mod binius;

// ============================================================================
// Field-agnostic abstract types for backend trait boundaries.
//
// These are opaque wrappers that let trait signatures remain independent of
// BabyBear or any specific field. Backends convert to/from their native field
// at the trait boundary.
// ============================================================================

/// A field element represented as a canonical u64 value.
///
/// Backends interpret this in their native field. For BabyBear (p = 2^31 - 2^27 + 1),
/// values are always < p. For Pasta curves, values are < their respective prime
/// and require `WideFieldElement` for the full representation — this type is used
/// only for elements that fit in 64 bits.
pub type FieldElement = u64;

/// A 32-byte hash digest, field-agnostic.
pub type HashDigest = [u8; 32];

/// A variable-width field element for curves with > 64-bit moduli (e.g., Pasta).
/// Represented as little-endian bytes.
pub type WideFieldElement = [u8; 32];

// ============================================================================
// Core trait: ProofBackend (backward-compatible, unchanged)
// ============================================================================

/// Unified trait for proof backends.
///
/// Implementors provide both membership proofs (leaf in tree) and fold-step
/// proofs (IVC accumulation of attenuation steps).
pub trait ProofBackend: Send + Sync {
    /// The proof type produced by this backend.
    type Proof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove that `leaf` is a member of a Merkle tree with given `root`,
    /// where `siblings` contains the sibling hashes at each level.
    ///
    /// Each element in `siblings` is a vector of sibling hashes at that level
    /// (for a 4-ary tree, each level has 3 siblings).
    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String>;

    /// Verify a membership proof against a given root.
    fn verify_membership(proof: &Self::Proof, root: &[u8; 32]) -> Result<bool, String>;

    /// Prove a single fold step: transition from `old_root` to `new_root`
    /// by removing the specified facts (whose hashes are in `removals`).
    ///
    /// This is the building block for IVC: each fold step removes capabilities
    /// from the token's fact set.
    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String>;

    /// Verify a fold proof.
    fn verify_fold(proof: &Self::Proof) -> Result<bool, String>;

    /// Get the serialized size of a proof in bytes.
    fn proof_size(proof: &Self::Proof) -> usize;

    /// The human-readable name of this backend.
    fn backend_name() -> &'static str;
}

// ============================================================================
// Extended trait: DerivationBackend
// ============================================================================

/// Witness for a derivation proof in the backend-agnostic representation.
///
/// A derivation proves: "Given rule R and body facts F_1..F_n committed under
/// state_root, the rule correctly derives fact F_out under substitution sigma."
#[derive(Clone, Debug)]
pub struct DerivationInput {
    /// Rule identifier.
    pub rule_id: u32,
    /// Number of body atoms the rule references.
    pub num_body_atoms: usize,
    /// Hashes of the body facts (as field elements).
    pub body_fact_hashes: Vec<FieldElement>,
    /// The state root all body facts are committed under.
    pub state_root: FieldElement,
    /// Substitution bindings (variable index -> value).
    pub substitution: Vec<FieldElement>,
    /// The derived fact's predicate identifier.
    pub derived_predicate: FieldElement,
    /// The derived fact's terms (up to 4).
    pub derived_terms: [FieldElement; 4],
    /// Optional: expiry height commitment (0 = no expiry).
    pub not_after_height: FieldElement,
    /// Optional: organization identity binding (0 = unrestricted).
    pub org_id_hash: FieldElement,
    /// Optional: remaining budget (0 = unlimited).
    pub budget_remaining: FieldElement,
}

/// Output of a derivation proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DerivationOutput {
    /// The derived fact hash (public output).
    pub derived_fact_hash: FieldElement,
    /// The state root the derivation is bound to (public input).
    pub state_root: FieldElement,
}

/// Backend capability: derivation proofs (rule application).
///
/// Proves that a Datalog rule was correctly applied: given body facts in the
/// committed state, the rule derives a new fact under a valid substitution.
pub trait DerivationBackend: ProofBackend {
    /// The derivation proof type (may differ from the base `Proof` type).
    type DerivationProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove a single derivation step.
    ///
    /// The backend proves that rule `input.rule_id` with the given substitution
    /// correctly derives the output fact from the body facts, all committed
    /// under `input.state_root`.
    fn prove_derivation(input: &DerivationInput) -> Result<Self::DerivationProof, String>;

    /// Verify a derivation proof.
    ///
    /// Returns the public outputs (derived_fact_hash, state_root) on success.
    fn verify_derivation(proof: &Self::DerivationProof) -> Result<DerivationOutput, String>;
}

// ============================================================================
// Extended trait: PredicateBackend
// ============================================================================

/// The kind of predicate comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PredicateKind {
    /// Greater than or equal: value >= threshold.
    Gte,
    /// Less than or equal: value <= threshold.
    Lte,
    /// Greater than: value > threshold.
    Gt,
    /// Less than: value < threshold.
    Lt,
    /// Not equal: value != threshold.
    Neq,
}

/// Input for a single-point predicate proof.
#[derive(Clone, Debug)]
pub struct PredicateInput {
    /// The attribute value (private witness).
    pub value: FieldElement,
    /// The threshold (public).
    pub threshold: FieldElement,
    /// The comparison kind.
    pub kind: PredicateKind,
    /// Commitment to the value (for binding to external state).
    pub value_commitment: FieldElement,
}

/// Input for a temporal predicate proof (property held over N consecutive steps).
#[derive(Clone, Debug)]
pub struct TemporalPredicateInput {
    /// The attribute values at each step (private witness).
    pub values: Vec<FieldElement>,
    /// The state roots at each step (binding to IVC/receipt chain).
    pub state_roots: Vec<FieldElement>,
    /// The comparison kind.
    pub kind: PredicateKind,
    /// The threshold (public).
    pub threshold: FieldElement,
}

/// Output of a temporal predicate proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TemporalPredicateOutput {
    /// Number of steps over which the predicate held.
    pub num_steps: u32,
    /// Initial state root (binding).
    pub initial_state_root: FieldElement,
    /// Final state root (binding).
    pub final_state_root: FieldElement,
    /// The threshold that was proven.
    pub threshold: FieldElement,
}

/// Input for a compound predicate proof (boolean combination of sub-predicates).
#[derive(Clone, Debug)]
pub struct CompoundPredicateInput {
    /// Sub-predicate inputs (up to 8).
    pub sub_predicates: Vec<PredicateInput>,
    /// Boolean formula combining the sub-predicate results.
    /// Encoded as a serialized expression (backend-specific interpretation).
    pub formula: Vec<u8>,
}

/// Input for a relational predicate proof (comparison between two parties).
#[derive(Clone, Debug)]
pub struct RelationalPredicateInput {
    /// My attribute value (private).
    pub my_value: FieldElement,
    /// My value commitment (public).
    pub my_commitment: FieldElement,
    /// Their value commitment (public, provided by the other party).
    pub their_commitment: FieldElement,
    /// The relation to prove (e.g., my_value >= their_value).
    pub kind: PredicateKind,
}

/// Backend capability: predicate proofs (arithmetic, relational, temporal, compound).
///
/// Covers range checks, temporal continuity proofs, relational comparisons between
/// committed values, and boolean compositions of sub-predicates.
pub trait PredicateBackend: ProofBackend {
    /// Proof type for single-point predicates.
    type PredicateProof: serde::Serialize + for<'de> serde::Deserialize<'de>;
    /// Proof type for temporal predicates (multi-step continuity).
    type TemporalProof: serde::Serialize + for<'de> serde::Deserialize<'de>;
    /// Proof type for compound predicates (boolean combination).
    type CompoundProof: serde::Serialize + for<'de> serde::Deserialize<'de>;
    /// Proof type for relational predicates (cross-party comparison).
    type RelationalProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove a single-point predicate (e.g., "my balance >= 1000").
    fn prove_predicate(input: &PredicateInput) -> Result<Self::PredicateProof, String>;

    /// Verify a single-point predicate proof.
    fn verify_predicate(proof: &Self::PredicateProof) -> Result<bool, String>;

    /// Prove a temporal predicate (e.g., "balance >= 1000 for 30 consecutive blocks").
    fn prove_temporal(input: &TemporalPredicateInput) -> Result<Self::TemporalProof, String>;

    /// Verify a temporal predicate proof, returning the public output on success.
    fn verify_temporal(proof: &Self::TemporalProof) -> Result<TemporalPredicateOutput, String>;

    /// Prove a compound predicate (boolean formula over sub-predicates).
    fn prove_compound(input: &CompoundPredicateInput) -> Result<Self::CompoundProof, String>;

    /// Verify a compound predicate proof.
    fn verify_compound(proof: &Self::CompoundProof) -> Result<bool, String>;

    /// Prove a relational predicate (comparison between two committed values).
    fn prove_relational(input: &RelationalPredicateInput) -> Result<Self::RelationalProof, String>;

    /// Verify a relational predicate proof.
    fn verify_relational(proof: &Self::RelationalProof) -> Result<bool, String>;
}

// ============================================================================
// Extended trait: AccumulatorBackend
// ============================================================================

/// Input for an accumulator-based non-membership (non-revocation) proof.
///
/// Proves: "None of my capability's ancestor hashes appear in the revocation set"
/// using a polynomial-evaluation accumulator over an extension field.
#[derive(Clone, Debug)]
pub struct AccumulatorInput {
    /// Ancestor hashes to prove non-membership for (private witness, up to 8).
    pub ancestor_hashes: Vec<FieldElement>,
    /// The accumulator value (public, computed from the revocation set).
    /// Represented as 4 base-field elements (extension field element).
    pub accumulator: [FieldElement; 4],
    /// The evaluation challenge alpha (public).
    /// Represented as 4 base-field elements (extension field element).
    pub alpha: [FieldElement; 4],
}

/// Backend capability: accumulator-based non-membership proofs.
///
/// Proves that a set of ancestor hashes do NOT appear in a committed revocation
/// set, using polynomial-evaluation accumulators. This is the O(1)-verifier
/// replacement for sorted-Merkle non-revocation circuits.
pub trait AccumulatorBackend: ProofBackend {
    /// Proof type for accumulator non-membership.
    type AccumulatorProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove non-membership of all ancestor hashes in the revocation accumulator.
    ///
    /// Returns `Err` if any ancestor IS in the revocation set (cannot prove a
    /// false non-membership statement).
    fn prove_non_membership(input: &AccumulatorInput) -> Result<Self::AccumulatorProof, String>;

    /// Verify an accumulator non-membership proof.
    ///
    /// The verifier only needs the accumulator value, alpha challenge, number of
    /// ancestors, and the proof. The ancestor hashes remain private.
    fn verify_non_membership(
        proof: &Self::AccumulatorProof,
        accumulator: &[FieldElement; 4],
        alpha: &[FieldElement; 4],
        num_ancestors: usize,
    ) -> Result<bool, String>;
}

// ============================================================================
// Extended trait: IvcBackend
// ============================================================================

/// A single fold delta for IVC accumulation.
#[derive(Clone, Debug)]
pub struct IvcFoldStep {
    /// The old state root before this fold.
    pub old_root: FieldElement,
    /// The new state root after this fold.
    pub new_root: FieldElement,
    /// Hashes of facts removed in this step.
    pub removed_fact_hashes: Vec<FieldElement>,
    /// Number of checks added (for checks commitment binding).
    pub num_added_checks: usize,
}

/// Output of an IVC proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct IvcOutput {
    /// The initial root (before any attenuation).
    pub initial_root: FieldElement,
    /// The final root (after all attenuations).
    pub final_root: FieldElement,
    /// Number of fold steps accumulated.
    pub step_count: u32,
    /// The accumulated hash committing to the chain history.
    /// 4 elements for 124-bit collision resistance.
    pub accumulated_hash: [FieldElement; 4],
}

/// Backend capability: IVC chain composition.
///
/// Accumulates N fold steps into a single constant-size proof. This is the
/// recursive proof composition that makes attenuation chains verifiable in O(1).
///
/// Without real recursion, backends may implement this as a hash-chain with
/// constraint checking. With recursion (e.g., Pickles over Pasta), each step
/// verifies the prior proof inside the circuit.
pub trait IvcBackend: ProofBackend {
    /// The IVC proof type (constant size regardless of chain length).
    type IvcProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Accumulate a sequence of fold steps into a single IVC proof.
    ///
    /// `initial_root` is the state root before any folds. `steps` is the ordered
    /// sequence of fold deltas. Returns a constant-size proof covering the entire chain.
    fn prove_ivc(
        initial_root: FieldElement,
        steps: &[IvcFoldStep],
    ) -> Result<Self::IvcProof, String>;

    /// Verify an IVC proof.
    ///
    /// Returns the public output (initial_root, final_root, step_count, accumulated_hash)
    /// on success, allowing the caller to bind the IVC result to other proof components.
    fn verify_ivc(proof: &Self::IvcProof) -> Result<IvcOutput, String>;

    /// Maximum supported chain depth (backend-specific limit).
    ///
    /// Returns the maximum number of fold steps that can be accumulated in a
    /// single IVC proof. Exceeding this should be handled by the caller
    /// (e.g., by splitting into segments).
    fn max_chain_depth() -> u32;
}

// ============================================================================
// Extended trait: PresentationBackend
// ============================================================================

/// Input for a complete presentation proof.
///
/// A presentation proves the full authorization statement:
/// "I hold a valid attenuated token chain whose final state authorizes action X"
/// without revealing the chain, capabilities, or issuer identity.
#[derive(Clone, Debug)]
pub struct PresentationInput {
    /// The federation root of trust (public).
    pub federation_root: FieldElement,
    /// The action binding commitment (public, 4 elements for 124-bit security).
    pub request_predicate: [FieldElement; 4],
    /// Timestamp for freshness (public).
    pub timestamp: FieldElement,
    /// Verifier-issued nonce for replay protection (public).
    pub verifier_nonce: FieldElement,
    /// Verifier-declared current block height for freshness binding (public).
    pub verifier_block_height: FieldElement,
    /// Fold chain: sequence of fold steps (private witness).
    pub fold_steps: Vec<IvcFoldStep>,
    /// Derivation input for the final authorization (private witness).
    pub derivation: DerivationInput,
    /// Issuer membership: leaf hash (private).
    pub issuer_leaf: FieldElement,
    /// Issuer membership: sibling hashes at each Merkle level (private).
    /// Each inner vec has 3 siblings for a 4-ary tree.
    pub issuer_siblings: Vec<Vec<FieldElement>>,
    /// Blinding factor for ring membership (private, 0 = non-blinded).
    pub blinding_factor: FieldElement,
    /// Fresh randomness for the presentation tag (private).
    pub presentation_randomness: FieldElement,
    /// Commitment to selectively revealed facts (public, 0 = fully private).
    pub revealed_facts_commitment: FieldElement,
}

/// Output of a presentation proof verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationOutput {
    /// The federation root (public).
    pub federation_root: FieldElement,
    /// The action binding commitment (public).
    pub request_predicate: [FieldElement; 4],
    /// Timestamp (public).
    pub timestamp: FieldElement,
    /// Blinded presentation tag (public, different each show).
    pub presentation_tag: FieldElement,
    /// Revealed facts commitment (public).
    pub revealed_facts_commitment: FieldElement,
    /// Composition commitment binding sub-proofs (public).
    pub composition_commitment: FieldElement,
    /// Verifier nonce (public).
    pub verifier_nonce: FieldElement,
    /// Verifier block height (public).
    pub verifier_block_height: FieldElement,
}

/// Backend capability: full presentation proofs.
///
/// A presentation proof is the complete zero-knowledge authorization proof that
/// combines: issuer membership, fold chain (attenuation), derivation (authorization),
/// and optionally temporal predicates and non-revocation. This is the top-level
/// proof that a verifier checks.
pub trait PresentationBackend: ProofBackend + DerivationBackend + IvcBackend {
    /// The presentation proof type.
    type PresentationProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Generate a complete presentation proof.
    ///
    /// This composes:
    /// 1. IVC proof of the fold chain (attenuation validity)
    /// 2. Derivation proof (authorization from final state)
    /// 3. Issuer membership proof (issuer in federation)
    /// 4. Presentation tag computation (unlinkability)
    /// 5. Composition commitment (sub-proof binding)
    fn prove_presentation(input: &PresentationInput) -> Result<Self::PresentationProof, String>;

    /// Verify a presentation proof.
    ///
    /// Returns the public outputs on success, allowing the verifier to check:
    /// - Federation root matches expected
    /// - Action binding matches the request
    /// - Timestamp is fresh
    /// - Verifier nonce matches the challenge issued
    /// - Block height freshness binding
    fn verify_presentation(proof: &Self::PresentationProof) -> Result<PresentationOutput, String>;

    /// Get the total serialized proof size in bytes.
    fn presentation_proof_size(proof: &Self::PresentationProof) -> usize;
}

// ============================================================================
// Extended trait: CrossStateBackend
// ============================================================================

/// A single source's contribution to a cross-state derivation.
#[derive(Clone, Debug)]
pub struct CrossStateSource {
    /// The state root this source operates under.
    pub source_root: FieldElement,
    /// The derivation input under this source root.
    pub derivation: DerivationInput,
}

/// The combining rule for cross-state derivation.
#[derive(Clone, Debug)]
pub struct CrossStateCombiningRule {
    /// Rule ID for the combining step.
    pub rule_id: u32,
    /// The final derived predicate.
    pub head_predicate: FieldElement,
    /// Head term patterns: (is_variable, value_or_var_index).
    pub head_terms: [(bool, FieldElement); 4],
    /// Substitution for the combining rule.
    pub substitution: Vec<FieldElement>,
    /// The final derived terms.
    pub derived_terms: [FieldElement; 4],
}

/// Output of a cross-state derivation proof.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct CrossStateOutput {
    /// The composition root (Poseidon2 tree of intermediate derived facts).
    pub composition_root: FieldElement,
    /// Source roots (one per source).
    pub source_roots: Vec<FieldElement>,
    /// The final derived fact hash.
    pub final_derived_hash: FieldElement,
}

/// Backend capability: cross-state derivation composition.
///
/// When an authorization decision depends on facts from multiple independent state
/// roots (e.g., different organizations), a single derivation proof is insufficient.
/// This trait composes per-source derivation proofs with a final composition proof
/// under a merged root.
///
/// Architecture:
/// ```text
/// Source 1 (R_1) ──STARK──► F_1 ─┐
/// Source 2 (R_2) ──STARK──► F_2 ─┼──► composition_root ──STARK──► final_fact
/// Source N (R_N) ──STARK──► F_N ─┘
/// ```
pub trait CrossStateBackend: ProofBackend + DerivationBackend {
    /// The cross-state derivation proof type.
    type CrossStateProof: serde::Serialize + for<'de> serde::Deserialize<'de>;

    /// Prove a cross-state derivation.
    ///
    /// Each source produces an independent derivation proof under its own state root.
    /// The intermediate derived facts are combined via a Merkle tree into a composition
    /// root, and a final derivation proof operates under that composition root.
    fn prove_cross_state(
        sources: &[CrossStateSource],
        combining_rule: &CrossStateCombiningRule,
    ) -> Result<Self::CrossStateProof, String>;

    /// Verify a cross-state derivation proof.
    ///
    /// The verifier checks:
    /// 1. Each source derivation is valid under its declared root.
    /// 2. The composition root correctly commits to the intermediate facts.
    /// 3. The final derivation is valid under the composition root.
    fn verify_cross_state(proof: &Self::CrossStateProof) -> Result<CrossStateOutput, String>;
}

// ============================================================================
// Supertrait: FullProofBackend
// ============================================================================

/// The complete proof surface required for Pickles recursion over the full
/// authorization pipeline.
///
/// A backend implementing `FullProofBackend` supports the entire pyana proof
/// lifecycle: membership, fold, derivation, predicates, non-revocation, IVC
/// composition, presentation, and cross-state derivation.
///
/// This is the trait bound used by the Kimchi/Pickles recursive backend, which
/// needs to verify every sub-circuit type inside a recursive step.
pub trait FullProofBackend:
    ProofBackend
    + DerivationBackend
    + PredicateBackend
    + AccumulatorBackend
    + IvcBackend
    + PresentationBackend
    + CrossStateBackend
{
}
