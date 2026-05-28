//! Trustless intent solving protocol: fully decentralized fair matching.
//!
//! This module implements a 7-layer protocol that provides verifiably fair intent
//! solving without any trusted executor. The key properties:
//!
//! 1. **Front-running prevention**: Intents are encrypted to a threshold key; no party
//!    can read them before the collective decryption ceremony.
//! 2. **Fairness**: Batch boundaries are determined by consensus (blocklace finality),
//!    so no party can manipulate which intents enter a batch.
//! 3. **Provable validity**: Solvers produce STARK proofs of solution validity.
//! 4. **Incentive-compatible**: Open competition with challenge windows ensures solvers
//!    submit their best solutions (bond slashing for under-performance).
//! 5. **Atomic settlement**: The winning solution generates a single compound turn.
//!
//! # Protocol layers
//!
//! ```text
//! 1. SUBMIT   - Encrypted intent broadcast via gossip
//! 2. BATCH    - Consensus-determined batch boundary
//! 3. DECRYPT  - Threshold decryption ceremony
//! 4. SOLVE    - Open solver competition
//! 5. PROVE    - STARK proof of solution validity
//! 6. SELECT   - Best provably-valid solution wins (with challenge window)
//! 7. SETTLE   - Atomic compound turn committed to blocklace
//! ```
//!
//! # Comparison to existing approaches
//!
//! - **Anoma solver market**: Similar open competition, but our intents are encrypted
//!   during submission (Anoma's are visible to solvers immediately).
//! - **Flashbots SUAVE**: Our threshold decryption replaces SGX enclaves (no hardware
//!   trust assumption). Challenge window replaces block builder ordering.
//! - **CoW Protocol**: We share the batch auction model, but add STARK proofs and
//!   threshold encryption (CoW relies on a trusted solver with reputation).

use std::collections::HashMap;
use std::sync::Arc;

use dregg_cell::CellId;
use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry,
};
use dregg_federation::threshold_decrypt::{
    ThresholdCiphertext, ThresholdDecryptError, combine_shares,
};
use dregg_turn::action::Authorization;
use serde::{Deserialize, Serialize};

use crate::bond::{BondEscrow, BondKey};
use crate::lowering::{self, LoweringContext, SealedTurn};
use crate::solver::RingTrade;
use crate::{CommitmentId, Intent, IntentId};

/// Canonical decryption share type, re-exported from
/// `dregg_federation::threshold_decrypt`. The intent engine no longer
/// carries its own opaque-bytes placeholder; shares are real Shamir-
/// over-GF(256) values whose MACs are verified at combine time.
///
/// The federation type is keyed by `ciphertext_id` (BLAKE3 of the
/// `ThresholdCiphertext`), not by `batch_id`. The engine validates
/// that every contributed share's `ciphertext_id` matches one of the
/// submitted encrypted intents in the current batch.
pub use dregg_federation::threshold_decrypt::DecryptionShare;

// =============================================================================
// Configuration constants
// =============================================================================

/// Default number of blocklace waves between batch boundaries.
pub const DEFAULT_BATCH_INTERVAL: u64 = 10;

/// Default challenge window duration (in waves) after a winning solution is selected.
pub const DEFAULT_CHALLENGE_WINDOW: u64 = 5;

/// Minimum bond a solver must post to submit a solution.
pub const DEFAULT_MIN_SOLVER_BOND: u64 = 1000;

/// Maximum number of encrypted intents per batch before auto-closing.
pub const MAX_INTENTS_PER_BATCH: usize = 256;

/// Maximum number of solver submissions per solving round.
pub const MAX_SOLVER_SUBMISSIONS: usize = 32;

// =============================================================================
// Error types
// =============================================================================

/// Errors from the trustless intent engine.
#[derive(Clone, Debug, PartialEq)]
pub enum EngineError {
    /// Batch is not in the expected state for this operation.
    WrongState {
        expected: BatchState,
        actual: BatchState,
    },
    /// The batch is full (max intents reached).
    BatchFull,
    /// Decryption share from unknown or duplicate validator.
    InvalidDecryptionShare { reason: String },
    /// The threshold has not been reached for decryption.
    InsufficientDecryptionShares { have: usize, need: usize },
    /// Solution proof failed verification.
    InvalidProof { reason: String },
    /// Solution score is not higher than current winner (for challenges).
    ScoreNotHigher { submitted: f64, current: f64 },
    /// Solver bond is below the minimum required.
    InsufficientBond { provided: u64, required: u64 },
    /// No winning solution to finalize.
    NoWinningSolution,
    /// The batch height does not match the expected closing height.
    HeightMismatch { expected: u64, actual: u64 },
    /// Duplicate intent (same ciphertext already submitted).
    DuplicateIntent,
    /// Maximum solver submissions reached for this batch.
    TooManySubmissions,
    /// Challenge window has expired.
    ChallengeWindowExpired,
    /// Solution references an intent not in this batch.
    IntentNotInBatch { intent_id: IntentId },
    /// An intent is used in more than one ring within the solution.
    DuplicateIntentUsage { intent_id: IntentId },
    /// Settlement generation failed.
    SettlementFailed { reason: String },
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongState { expected, actual } => {
                write!(
                    f,
                    "wrong batch state: expected {:?}, got {:?}",
                    expected, actual
                )
            }
            Self::BatchFull => write!(f, "batch is full"),
            Self::InvalidDecryptionShare { reason } => {
                write!(f, "invalid decryption share: {}", reason)
            }
            Self::InsufficientDecryptionShares { have, need } => {
                write!(f, "insufficient shares: have {}, need {}", have, need)
            }
            Self::InvalidProof { reason } => write!(f, "invalid proof: {}", reason),
            Self::ScoreNotHigher { submitted, current } => {
                write!(
                    f,
                    "submitted score {} not higher than current {}",
                    submitted, current
                )
            }
            Self::InsufficientBond { provided, required } => {
                write!(f, "bond {} below minimum {}", provided, required)
            }
            Self::NoWinningSolution => write!(f, "no winning solution to finalize"),
            Self::HeightMismatch { expected, actual } => {
                write!(f, "height mismatch: expected {}, got {}", expected, actual)
            }
            Self::DuplicateIntent => write!(f, "duplicate encrypted intent"),
            Self::TooManySubmissions => write!(f, "maximum solver submissions reached"),
            Self::ChallengeWindowExpired => write!(f, "challenge window has expired"),
            Self::IntentNotInBatch { intent_id } => {
                write!(
                    f,
                    "intent {:02x}{:02x}... not in batch",
                    intent_id[0], intent_id[1]
                )
            }
            Self::DuplicateIntentUsage { intent_id } => {
                write!(
                    f,
                    "intent {:02x}{:02x}... used in multiple rings",
                    intent_id[0], intent_id[1]
                )
            }
            Self::SettlementFailed { reason } => {
                write!(f, "settlement failed: {}", reason)
            }
        }
    }
}

impl std::error::Error for EngineError {}

// =============================================================================
// Core types
// =============================================================================

/// The lifecycle state of an intent batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BatchState {
    /// Accepting encrypted intents.
    Collecting,
    /// Batch closed, waiting for threshold decryption shares.
    AwaitingDecrypt,
    /// Decrypted, open for solver submissions.
    Solving,
    /// Winning solution chosen, challenge window open.
    Challenging,
    /// Compound turn committed, batch is complete.
    Settled,
}

/// An encrypted intent submitted before decryption.
///
/// The `ciphertext` carries the federation's real
/// [`ThresholdCiphertext`] — a ChaCha20-Poly1305-style sealed payload
/// keyed to the epoch's threshold encryption key. Validators each
/// hold a Shamir share of the decryption key; t-of-n contributed
/// shares reconstruct the key, after which the ciphertext decrypts
/// to a postcard-serialized [`Intent`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedIntent {
    /// The threshold-encrypted serialized [`Intent`].
    pub ciphertext: ThresholdCiphertext,
    /// Anonymous creator commitment (visible even before decryption for dedup).
    pub creator_commitment: CommitmentId,
    /// Blocklace height at which this was submitted.
    pub submitted_at: u64,
}

impl EncryptedIntent {
    /// Compute a content-addressed ID for deduplication. Includes the
    /// ciphertext's own id (epoch + nonce + ciphertext bytes) so two
    /// different encryptions of the same intent get distinct content
    /// ids — the inner [`ThresholdCiphertext::ciphertext_id`] alone
    /// is sufficient but we also bind the creator + submission height
    /// for additional uniqueness when the same ciphertext is replayed.
    pub fn content_id(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-intent-id-v2");
        hasher.update(&self.ciphertext.ciphertext_id());
        hasher.update(&self.creator_commitment.0);
        hasher.update(&self.submitted_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Convenience: the ciphertext id used by decryption shares to
    /// bind to a specific encrypted payload.
    pub fn ciphertext_id(&self) -> [u8; 32] {
        self.ciphertext.ciphertext_id()
    }
}

/// A solver's proposed solution to the batch.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SolverSubmission {
    /// Solver identity (public key hash or commitment).
    pub solver_id: [u8; 32],
    /// The discovered ring trades forming this solution.
    pub solution: Vec<RingTrade>,
    /// The total score (sum of individual ring scores).
    pub total_score: f64,
    /// STARK proof of validity: all rings valid, score correctly computed, no
    /// intent used twice. The proof binds to the batch's decrypted intent set.
    pub validity_proof: Vec<u8>,
    /// Optional witnessed-predicate declaration naming the verifier kind
    /// for `validity_proof`.
    ///
    /// When present, the engine routes proof verification through the
    /// canonical [`WitnessedPredicateRegistry`] keyed on
    /// `witnessed_predicate.kind`. The predicate's `commitment` binds the
    /// solution's audience (typically the batch's decrypted-intent-set
    /// commitment); the `proof_bytes` come from `validity_proof`.
    ///
    /// When `None`, the verifier falls back to the structural-only
    /// [`MockProofVerifier`] semantics — accepted for legacy / smoke
    /// tests but flagged on real deployments. Production callers should
    /// always set this field and register a real verifier in the
    /// registry handed to [`WitnessedProofVerifier::new`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witnessed_predicate: Option<WitnessedPredicate>,
    /// Bond posted by the solver (slashed if challenged successfully).
    pub bond: u64,
    /// Blocklace height at which this submission arrived.
    pub submitted_at: u64,
}

/// The output of finalizing a batch: a sealed `Turn` ready for the
/// executor, plus the batch metadata needed to correlate with the
/// originating intent batch.
///
/// Replaces the legacy `CompoundTurn` (P2.G). The settlement actions
/// now live as `Effect::Transfer`s inside `sealed.turn.call_forest`,
/// authorized through `lowering::seal_plan_uniform` rather than carrying
/// a parallel ad-hoc settlement type.
#[derive(Clone, Debug)]
pub struct SettlementOutput {
    /// The batch this settlement resolves.
    pub batch_id: u64,
    /// The sealed turn carrying every leg as a typed `Effect::Transfer`.
    pub sealed: SealedTurn,
    /// Hash of the winning solution's validity proof (binding).
    pub proof_hash: [u8; 32],
    /// The solver who produced the winning solution.
    pub solver_id: [u8; 32],
}

/// A batch of encrypted intents going through the solving pipeline.
#[derive(Clone, Debug)]
pub struct IntentBatch {
    /// Monotonically increasing batch identifier.
    pub batch_id: u64,
    /// Encrypted intents collected during the Collecting phase.
    pub encrypted_intents: Vec<EncryptedIntent>,
    /// The blocklace height at which this batch was closed.
    pub batch_boundary_height: u64,
    /// Decrypted intents (populated after threshold ceremony completes).
    pub decrypted: Option<Vec<Intent>>,
    /// Solver submissions received during the Solving phase.
    pub solutions: Vec<SolverSubmission>,
    /// The current winning solution (highest score among valid submissions).
    pub winning_solution: Option<SolverSubmission>,
    /// Current lifecycle state.
    pub state: BatchState,
    /// Decryption shares collected so far, indexed by `ciphertext_id`.
    /// Each ciphertext is independently decryptable once t-of-n shares
    /// referencing it have arrived.
    pub decrypt_shares: HashMap<[u8; 32], Vec<DecryptionShare>>,
    /// Height at which the challenge window opened.
    pub challenge_start_height: Option<u64>,
    /// Content IDs of submitted intents (for deduplication).
    seen_intent_ids: HashMap<[u8; 32], ()>,
    /// Ciphertext IDs of submitted intents (for share-binding validation).
    seen_ciphertext_ids: HashMap<[u8; 32], ()>,
}

impl IntentBatch {
    /// Create a new batch in the Collecting state.
    pub fn new(batch_id: u64) -> Self {
        Self {
            batch_id,
            encrypted_intents: Vec::new(),
            batch_boundary_height: 0,
            decrypted: None,
            solutions: Vec::new(),
            winning_solution: None,
            state: BatchState::Collecting,
            decrypt_shares: HashMap::new(),
            challenge_start_height: None,
            seen_intent_ids: HashMap::new(),
            seen_ciphertext_ids: HashMap::new(),
        }
    }
}

// =============================================================================
// Proof verification (trait for pluggable verification backends)
// =============================================================================

/// Trait for verifying solver solution proofs.
///
/// Implementations may use STARK verification, witnessed-predicate
/// dispatch through the canonical registry, or mock structural checks.
///
/// The trait offers two entry points:
///
/// - [`verify`](Self::verify) — the legacy proof-bytes-only signature.
///   Kept for backwards compatibility with stub callers; the default
///   path now flows through [`verify_submission`](Self::verify_submission).
/// - [`verify_submission`](Self::verify_submission) — the canonical
///   entry point. Receives the full [`SolverSubmission`] so the verifier
///   can route the proof through the
///   [`WitnessedPredicateRegistry`] when
///   `submission.witnessed_predicate` is set.
///
/// Implementations should override `verify_submission`; the default
/// `verify` impl forwards to it with a synthetic submission that lacks
/// the witnessed-predicate declaration — fine for legacy mock paths,
/// inadequate for real verification. Real implementations expose
/// `verify_submission` directly.
pub trait ProofVerifier: Send + Sync {
    /// Verify that a proof is valid for the given solution and intent set.
    ///
    /// The verifier checks:
    /// 1. All rings in the solution are valid (quantities match, constraints satisfied)
    /// 2. The total_score is correctly computed from individual ring scores
    /// 3. No intent_id appears in more than one ring
    /// 4. All referenced intent_ids exist in `decrypted_intents`
    fn verify(
        &self,
        proof: &[u8],
        solution: &[RingTrade],
        total_score: f64,
        decrypted_intents: &[Intent],
    ) -> Result<(), String>;

    /// Verify a full [`SolverSubmission`] against the batch's decrypted
    /// intent set. Default impl forwards to [`Self::verify`] using the
    /// raw `validity_proof` bytes, discarding any
    /// `witnessed_predicate` declaration the submission carries.
    ///
    /// Production verifiers ([`WitnessedProofVerifier`]) override this
    /// to route through the canonical
    /// [`WitnessedPredicateRegistry`].
    fn verify_submission(
        &self,
        submission: &SolverSubmission,
        decrypted_intents: &[Intent],
    ) -> Result<(), String> {
        self.verify(
            &submission.validity_proof,
            &submission.solution,
            submission.total_score,
            decrypted_intents,
        )
    }
}

/// Structural consistency checks applied to every solver submission
/// before cryptographic verification.
///
/// Catches the cheap-to-detect dishonesty:
///
/// - Score sum disagrees with claimed total.
/// - Same `IntentId` participates in more than one ring.
/// - A referenced `IntentId` is not present in `decrypted_intents`.
///
/// These checks are necessary but not sufficient — they guarantee the
/// submission's *shape* is internally consistent, not that the proof
/// genuinely attests to a valid solution. Cryptographic soundness is
/// delegated to the kind verifier in
/// [`WitnessedProofVerifier::verify_submission`].
fn check_submission_structure(
    solution: &[RingTrade],
    total_score: f64,
    decrypted_intents: &[Intent],
) -> Result<(), String> {
    let computed_score: f64 = solution.iter().map(|r| r.score).sum();
    if (computed_score - total_score).abs() > 1e-9 {
        return Err(format!(
            "score mismatch: computed {} vs claimed {}",
            computed_score, total_score
        ));
    }
    let mut used_intents: std::collections::HashSet<IntentId> = std::collections::HashSet::new();
    for ring in solution {
        for participant in &ring.participants {
            if !used_intents.insert(*participant) {
                return Err(format!(
                    "intent {:02x}{:02x}... used in multiple rings",
                    participant[0], participant[1]
                ));
            }
        }
    }
    let batch_ids: std::collections::HashSet<IntentId> =
        decrypted_intents.iter().map(|i| i.id).collect();
    for id in &used_intents {
        if !batch_ids.contains(id) {
            return Err(format!("intent {:02x}{:02x}... not in batch", id[0], id[1]));
        }
    }
    Ok(())
}

/// Production proof verifier: routes the solver's `validity_proof`
/// through the canonical [`WitnessedPredicateRegistry`].
///
/// When a [`SolverSubmission`] carries a `witnessed_predicate`, the
/// verifier:
///
/// 1. Runs the structural shape check
///    ([`check_submission_structure`]) — score sum, distinct intents,
///    membership.
/// 2. Computes the **batch binding** — a 32-byte BLAKE3 derivation
///    over the sorted decrypted-intent-id set — and confirms it
///    matches `witnessed_predicate.commitment`. This is the audience
///    binding: the proof verifies against a specific batch.
/// 3. Dispatches the proof through the canonical registry keyed on
///    `witnessed_predicate.kind` — `Dfa`, `Temporal`,
///    `MerkleMembership`, `BlindedSet`, `BridgePredicate`,
///    `PedersenEquality`, or `Custom { vk_hash }`.
/// 4. Surfaces the kind's verification verdict to the trustless
///    engine. A `KindNotRegistered` failure means the executor refuses
///    to validate the kind; an algebraic reject means the proof itself
///    failed.
///
/// Submissions without a witnessed predicate are treated as
/// legacy / smoke-test submissions: the structural-only checks apply
/// and the proof bytes themselves are not cryptographically validated.
/// Production deployments should reject this path by attaching a
/// witnessed predicate to every submission.
pub struct WitnessedProofVerifier {
    registry: Arc<WitnessedPredicateRegistry>,
    /// When true, submissions without a `witnessed_predicate` are
    /// rejected outright (production posture). When false (default),
    /// they fall back to structural-only verification — the legacy
    /// `MockProofVerifier` behavior, preserved here so tests that
    /// don't yet carry a predicate keep passing.
    strict: bool,
}

impl WitnessedProofVerifier {
    /// Construct a verifier wrapping an existing canonical registry.
    ///
    /// Production deployments pass the workspace-shared registry with
    /// real STARK / Schnorr / Bulletproof verifiers registered for
    /// each built-in kind. Tests can pass
    /// `WitnessedPredicateRegistry::with_stubs()` to exercise the
    /// dispatch plumbing without pulling in the circuit crate.
    pub fn new(registry: WitnessedPredicateRegistry) -> Self {
        Self {
            registry: Arc::new(registry),
            strict: false,
        }
    }

    /// Construct a verifier that **rejects** submissions without a
    /// `witnessed_predicate` declaration. Production posture.
    pub fn strict(registry: WitnessedPredicateRegistry) -> Self {
        Self {
            registry: Arc::new(registry),
            strict: true,
        }
    }

    /// Convenience constructor: stub registry, non-strict. Test
    /// equivalent of the legacy [`MockProofVerifier`] but routed
    /// through the canonical surface so adversarial tests can
    /// register their own kind verifiers.
    pub fn with_stub_registry() -> Self {
        Self {
            registry: Arc::new(WitnessedPredicateRegistry::with_stubs()),
            strict: false,
        }
    }

    /// Access the underlying registry (for tests that want to register
    /// custom verifiers on top of the default kinds).
    pub fn registry(&self) -> &WitnessedPredicateRegistry {
        &self.registry
    }

    /// Compute the canonical "batch binding" commitment for an intent
    /// set. The binding is BLAKE3-derived over the sorted intent IDs,
    /// so it's deterministic and order-independent.
    ///
    /// A solver's `witnessed_predicate.commitment` must equal this
    /// value; otherwise the proof was generated against a different
    /// intent set and is rejected.
    pub fn compute_batch_binding(decrypted_intents: &[Intent]) -> [u8; 32] {
        let mut ids: Vec<IntentId> = decrypted_intents.iter().map(|i| i.id).collect();
        ids.sort();
        let mut hasher = blake3::Hasher::new_derive_key("dregg-trustless-batch-binding-v1");
        hasher.update(&(ids.len() as u64).to_le_bytes());
        for id in &ids {
            hasher.update(id);
        }
        *hasher.finalize().as_bytes()
    }
}

impl ProofVerifier for WitnessedProofVerifier {
    /// Legacy entry point. Defers to `verify_submission` via a
    /// synthetic [`SolverSubmission`] without a witnessed predicate.
    /// Strict-mode verifiers reject (the predicate is absent); permissive-
    /// mode verifiers fall through to the structural check.
    fn verify(
        &self,
        proof: &[u8],
        solution: &[RingTrade],
        total_score: f64,
        decrypted_intents: &[Intent],
    ) -> Result<(), String> {
        if proof.is_empty() {
            return Err("empty proof".to_string());
        }
        if self.strict {
            return Err("strict verifier requires a witnessed_predicate on the submission".into());
        }
        check_submission_structure(solution, total_score, decrypted_intents)
    }

    fn verify_submission(
        &self,
        submission: &SolverSubmission,
        decrypted_intents: &[Intent],
    ) -> Result<(), String> {
        if submission.validity_proof.is_empty() {
            return Err("empty proof".to_string());
        }
        check_submission_structure(
            &submission.solution,
            submission.total_score,
            decrypted_intents,
        )?;

        let Some(wp) = submission.witnessed_predicate.as_ref() else {
            if self.strict {
                return Err(
                    "strict verifier requires a witnessed_predicate on the submission".into(),
                );
            }
            // SOUNDNESS NOTE (SILVER-DEBT T1.2 — CLOSED):
            // The predicate-less fail-OPEN hole is closed. The production
            // engine (`TrustlessIntentEngine::new`) and the live node
            // (node/src/state.rs) now construct the verifier with
            // `WitnessedProofVerifier::strict(..)`, so a submission that omits
            // `witnessed_predicate` is REJECTED above before reaching this
            // branch — its `validity_proof` is never accepted on the structural
            // check alone. This permissive branch is reachable only via the
            // explicit non-strict constructors (`WitnessedProofVerifier::new` /
            // `::with_stub_registry`), which exist solely for plumbing-coverage
            // tests where the proof algebra is out of scope; they MUST NOT be
            // used in any production path. The closed-hole assertion is pinned
            // by `predicateless_submission_is_rejected_hole_closed` and
            // `strict_verifier_rejects_predicateless_submission`.
            return Ok(());
        };

        // Audience binding: the predicate's commitment must equal the
        // canonical batch binding for the decrypted intent set. This
        // rejects a proof minted against a different batch.
        let expected_binding = Self::compute_batch_binding(decrypted_intents);
        if wp.commitment != expected_binding {
            return Err(format!(
                "batch binding mismatch: predicate commits to {:02x}{:02x}..., \
                 expected {:02x}{:02x}... for current batch",
                wp.commitment[0], wp.commitment[1], expected_binding[0], expected_binding[1],
            ));
        }

        // Dispatch through the canonical registry. The predicate's
        // `input_ref` is conceptually `PublicInput`: the batch binding
        // is the "public input" of the proof. We supply it as
        // `PredicateInput::Bytes(commitment)` so the verifier sees
        // the same audience the executor sees.
        let input_bytes = wp.commitment;
        let input = match wp.input_ref {
            InputRef::PublicInput { .. } | InputRef::Witness { .. } => {
                PredicateInput::Bytes(&input_bytes)
            }
            // Surfaces outside an action context (slot caveats,
            // preconditions, intent solving) must reject
            // `SigningMessage` shape per PREDICATE-INVENTORY §3.
            InputRef::SigningMessage => {
                return Err(
                    "SigningMessage input is action-context only; not valid for solver proof"
                        .into(),
                );
            }
            // Slot / Sender shapes have no meaning in a batch-binding
            // context — they're cell-bound, not intent-batch-bound.
            InputRef::Slot { .. } => {
                return Err("Slot input not valid for solver proof".into());
            }
            InputRef::Sender => {
                return Err("Sender input not valid for solver proof".into());
            }
        };

        self.registry
            .verify(wp, &input, &submission.validity_proof)
            .map_err(|e| match e {
                WitnessedPredicateError::KindNotRegistered { kind } => {
                    format!("predicate kind not registered: {}", kind_label(kind))
                }
                WitnessedPredicateError::Rejected { kind_name, reason } => {
                    format!("predicate {kind_name} rejected: {reason}")
                }
                other => format!("predicate verification failed: {other}"),
            })
    }
}

fn kind_label(kind: WitnessedPredicateKind) -> String {
    match kind {
        WitnessedPredicateKind::Dfa => "Dfa".into(),
        WitnessedPredicateKind::Temporal => "Temporal".into(),
        WitnessedPredicateKind::MerkleMembership => "MerkleMembership".into(),
        WitnessedPredicateKind::BlindedSet => "BlindedSet".into(),
        WitnessedPredicateKind::BridgePredicate => "BridgePredicate".into(),
        WitnessedPredicateKind::PedersenEquality => "PedersenEquality".into(),
        // Categorical dual of MerkleMembership — sorted-set non-membership
        // via adjacent-leaf witnessing. Label kept terse for log lines.
        WitnessedPredicateKind::NonMembership => "NonMembership".into(),
        WitnessedPredicateKind::Custom { vk_hash } => format!(
            "Custom {{ vk_hash: {:02x}{:02x}... }}",
            vk_hash[0], vk_hash[1]
        ),
    }
}

/// **Deprecated.** Use [`WitnessedProofVerifier`] (canonical registry
/// dispatch). `MockProofVerifier` retained only for legacy tests that
/// have not yet migrated.
///
/// The verifier accepts any non-empty proof that passes the structural
/// consistency check ([`check_submission_structure`]). It does not
/// verify any cryptographic claim — neither the proof bytes nor any
/// witnessed predicate.
#[derive(Clone, Debug)]
#[deprecated(
    since = "0.2.0",
    note = "use WitnessedProofVerifier which routes through WitnessedPredicateRegistry"
)]
pub struct MockProofVerifier;

#[allow(deprecated)]
impl ProofVerifier for MockProofVerifier {
    fn verify(
        &self,
        proof: &[u8],
        solution: &[RingTrade],
        total_score: f64,
        decrypted_intents: &[Intent],
    ) -> Result<(), String> {
        if proof.is_empty() {
            return Err("empty proof".to_string());
        }
        check_submission_structure(solution, total_score, decrypted_intents)
    }
}

// =============================================================================
// TrustlessIntentEngine
// =============================================================================

/// The trustless intent solving engine.
///
/// Orchestrates the 7-layer protocol from encrypted intent submission through
/// atomic settlement. Designed to be embedded in a federation node.
pub struct TrustlessIntentEngine {
    /// The current active batch being processed.
    pub current_batch: IntentBatch,
    /// Number of waves between batch boundaries.
    pub batch_interval: u64,
    /// Duration of the challenge window (in waves).
    pub challenge_window: u64,
    /// Minimum bond required from solvers.
    pub min_solver_bond: u64,
    /// Threshold for decryption (number of shares needed).
    pub decrypt_threshold: usize,
    /// Total number of validators in the federation.
    pub num_validators: usize,
    /// Current blocklace height.
    pub current_height: u64,
    /// Proof verifier implementation.
    verifier: Box<dyn ProofVerifier>,
    /// Counter for batch IDs.
    next_batch_id: u64,
    /// Archive of settled batches (batch_id -> compound turn).
    pub settled_batches: HashMap<u64, SettlementOutput>,
    /// Solver bond escrow. When a solver posts a submission, their
    /// bond is locked here; on successful finalize the bond is
    /// released, on a successful challenge the displaced solver's
    /// bond is slashed (per audit §14 — bond escrow with `BoundedBy`
    /// slot caveat semantics, mirrored in-memory by [`BondEscrow`]).
    ///
    /// Defaults to an empty escrow. Production deployments pre-deposit
    /// solver balances via [`Self::deposit_bond`] (or the cell-program
    /// migration's slot updates) so solvers can actually post bonds.
    pub bond_escrow: BondEscrow,
}

impl TrustlessIntentEngine {
    /// Create a new engine with **fail-closed production-posture defaults**
    /// (P0 #82 fix).
    ///
    /// The default verifier is
    /// `WitnessedProofVerifier::strict(WitnessedPredicateRegistry::default_builtins())`:
    ///
    /// - Submissions that OMIT `witnessed_predicate` are **rejected**
    ///   (fail-CLOSED). The `validity_proof` bytes are never accepted on the
    ///   structural check alone — the prior predicate-less bypass (SILVER-DEBT
    ///   T1.2) is closed.
    /// - Submissions that carry a `witnessed_predicate` dispatch through the
    ///   canonical registry. Built-in kinds (`Dfa`, `Temporal`,
    ///   `MerkleMembership`, `BlindedSet`, `BridgePredicate`,
    ///   `PedersenEquality`) are wired to
    ///   [`dregg_cell::predicate::WitnessedPredicateRegistry::default_builtins`],
    ///   which installs `NotYetWiredVerifier` for kinds whose real algebra
    ///   adapter has not been registered on the host. These verifiers
    ///   **reject** with a "not yet wired" reason — they do not silently
    ///   accept, which was the pre-fix behavior under the stub registry.
    /// - `NonMembership` ships a real `SortedNeighborNonMembershipVerifier`
    ///   in the cell crate, so genuine non-membership claims succeed out
    ///   of the box.
    ///
    /// Production deployments wishing to verify real proofs must install
    /// adapters via
    /// [`dregg_cell::predicate::WitnessedPredicateRegistry::register_builtin`]
    /// before handing the registry to [`Self::with_verifier`].
    ///
    /// Tests that depend on the prior permissive-stub behavior should use
    /// [`Self::with_stub_verifier`] (or construct an explicit verifier and
    /// pass it to [`Self::with_verifier`]).
    ///
    /// STARBRIDGE-FOLLOWUP-03 (§5.8): Real STARK wiring (dregg-witnessed-registry-default
    /// crate + circuit adapters for Dfa etc) remains BLOCKED ON HUMAN per
    /// SILVER-DEBT T1.2/T2.8. `NotYetWiredVerifier` is the correct fail-closed
    /// default now; wasm stays mock-limited. Precise: trustless.rs:749 default
    /// + cell/src/predicate.rs NotYetWired entries. No new crate this session.
    pub fn new(decrypt_threshold: usize, num_validators: usize) -> Self {
        let registry = WitnessedPredicateRegistry::default_builtins();
        Self {
            current_batch: IntentBatch::new(0),
            batch_interval: DEFAULT_BATCH_INTERVAL,
            challenge_window: DEFAULT_CHALLENGE_WINDOW,
            min_solver_bond: DEFAULT_MIN_SOLVER_BOND,
            decrypt_threshold,
            num_validators,
            current_height: 0,
            // STRICT by default (fail-CLOSED). A submission that omits
            // `witnessed_predicate` is REJECTED — the `validity_proof` bytes
            // are never waved through on a structural check alone. See
            // `WitnessedProofVerifier::strict` and the closed-hole note in
            // `verify_submission`.
            verifier: Box::new(WitnessedProofVerifier::strict(registry)),
            next_batch_id: 1,
            settled_batches: HashMap::new(),
            bond_escrow: BondEscrow::new(),
        }
    }

    /// Test-only constructor: install the legacy stub-registry verifier
    /// (accepts any non-empty proof against any built-in kind). Use this
    /// in plumbing-coverage tests where the surface contract matters but
    /// the proof algebra is out of scope; never in production paths.
    ///
    /// Renamed from `Self::new` (pre-#82): the implicit-stub default in
    /// the old `new()` was a silent-bypass of witnessed predicates.
    pub fn with_stub_verifier(decrypt_threshold: usize, num_validators: usize) -> Self {
        Self {
            current_batch: IntentBatch::new(0),
            batch_interval: DEFAULT_BATCH_INTERVAL,
            challenge_window: DEFAULT_CHALLENGE_WINDOW,
            min_solver_bond: DEFAULT_MIN_SOLVER_BOND,
            decrypt_threshold,
            num_validators,
            current_height: 0,
            verifier: Box::new(WitnessedProofVerifier::with_stub_registry()),
            next_batch_id: 1,
            settled_batches: HashMap::new(),
            bond_escrow: BondEscrow::new(),
        }
    }

    /// Create an engine with a custom proof verifier.
    pub fn with_verifier(
        decrypt_threshold: usize,
        num_validators: usize,
        verifier: Box<dyn ProofVerifier>,
    ) -> Self {
        Self {
            current_batch: IntentBatch::new(0),
            batch_interval: DEFAULT_BATCH_INTERVAL,
            challenge_window: DEFAULT_CHALLENGE_WINDOW,
            min_solver_bond: DEFAULT_MIN_SOLVER_BOND,
            decrypt_threshold,
            num_validators,
            current_height: 0,
            verifier,
            next_batch_id: 1,
            settled_batches: HashMap::new(),
            bond_escrow: BondEscrow::new(),
        }
    }

    /// Deposit value into a solver's bond account. Tests and node
    /// initialization use this to pre-fund solvers; in production the
    /// cell-program version is driven by a transfer turn into the
    /// SolverEscrow cell.
    pub fn deposit_bond(&mut self, solver_id: &[u8; 32], amount: u64) {
        self.bond_escrow.deposit(solver_id, amount);
    }

    // =========================================================================
    // Layer 1: SUBMIT (encrypted intent submission)
    // =========================================================================

    /// Submit an encrypted intent to the current batch.
    ///
    /// The intent is encrypted to the federation's threshold key, so no individual
    /// validator can read it. The `creator_commitment` is visible for deduplication
    /// but does not reveal the intent contents.
    pub fn submit_encrypted(&mut self, intent: EncryptedIntent) -> Result<(), EngineError> {
        if self.current_batch.state != BatchState::Collecting {
            return Err(EngineError::WrongState {
                expected: BatchState::Collecting,
                actual: self.current_batch.state,
            });
        }

        if self.current_batch.encrypted_intents.len() >= MAX_INTENTS_PER_BATCH {
            return Err(EngineError::BatchFull);
        }

        // Deduplication check
        let content_id = intent.content_id();
        if self.current_batch.seen_intent_ids.contains_key(&content_id) {
            return Err(EngineError::DuplicateIntent);
        }
        let cipher_id = intent.ciphertext_id();

        self.current_batch.seen_intent_ids.insert(content_id, ());
        self.current_batch.seen_ciphertext_ids.insert(cipher_id, ());
        self.current_batch.encrypted_intents.push(intent);
        Ok(())
    }

    // =========================================================================
    // Layer 2: BATCH (consensus-determined boundary)
    // =========================================================================

    /// Close the current batch at the given blocklace height.
    ///
    /// This transitions the batch from Collecting -> AwaitingDecrypt.
    /// After this call, no more intents can be submitted to this batch.
    /// The batch boundary is determined by consensus (the blocklace's finality
    /// determines the exact set of intents).
    pub fn close_batch(&mut self, height: u64) -> Result<(), EngineError> {
        if self.current_batch.state != BatchState::Collecting {
            return Err(EngineError::WrongState {
                expected: BatchState::Collecting,
                actual: self.current_batch.state,
            });
        }

        self.current_batch.batch_boundary_height = height;
        self.current_batch.state = BatchState::AwaitingDecrypt;
        Ok(())
    }

    // =========================================================================
    // Layer 3: DECRYPT (threshold decryption ceremony)
    // =========================================================================

    /// Contribute a decryption share from a validator.
    ///
    /// Shares are bound to a specific [`ThresholdCiphertext`] via
    /// `ciphertext_id` (BLAKE3 over the ciphertext bytes). The engine
    /// accumulates shares per ciphertext; once **every** submitted
    /// ciphertext has at least `decrypt_threshold` shares, the engine
    /// reconstructs the decryption key and decrypts each ciphertext
    /// via [`combine_shares`], deserializes the plaintexts as
    /// [`Intent`]s, and transitions the batch to `Solving`.
    ///
    /// Share-MAC verification is performed inside `combine_shares` —
    /// corrupted shares are caught with an `InvalidShareMac` error
    /// surfaced as [`EngineError::InvalidDecryptionShare`].
    pub fn contribute_decrypt_share(&mut self, share: DecryptionShare) -> Result<(), EngineError> {
        if self.current_batch.state != BatchState::AwaitingDecrypt {
            return Err(EngineError::WrongState {
                expected: BatchState::AwaitingDecrypt,
                actual: self.current_batch.state,
            });
        }

        // Validate the share references a ciphertext in this batch.
        if !self
            .current_batch
            .seen_ciphertext_ids
            .contains_key(&share.ciphertext_id)
        {
            return Err(EngineError::InvalidDecryptionShare {
                reason: format!(
                    "share ciphertext_id {:02x}{:02x}... does not match any submitted ciphertext",
                    share.ciphertext_id[0], share.ciphertext_id[1]
                ),
            });
        }

        // Validate validator index is in range
        if share.validator_index == 0 || share.validator_index as usize > self.num_validators {
            return Err(EngineError::InvalidDecryptionShare {
                reason: format!(
                    "validator index {} out of range [1, {}]",
                    share.validator_index, self.num_validators
                ),
            });
        }

        // Check for duplicate validator index for this ciphertext.
        let shares_for_ct = self
            .current_batch
            .decrypt_shares
            .entry(share.ciphertext_id)
            .or_default();
        if shares_for_ct
            .iter()
            .any(|s| s.validator_index == share.validator_index)
        {
            return Err(EngineError::InvalidDecryptionShare {
                reason: format!(
                    "duplicate share from validator {} for ciphertext {:02x}{:02x}...",
                    share.validator_index, share.ciphertext_id[0], share.ciphertext_id[1]
                ),
            });
        }

        shares_for_ct.push(share);

        // Check if every submitted ciphertext has >= threshold shares; if
        // so, run the threshold decryption ceremony.
        let all_ready = !self.current_batch.encrypted_intents.is_empty()
            && self.current_batch.encrypted_intents.iter().all(|ct| {
                self.current_batch
                    .decrypt_shares
                    .get(&ct.ciphertext_id())
                    .map(|v| v.len() >= self.decrypt_threshold)
                    .unwrap_or(false)
            });

        if all_ready {
            self.run_threshold_decryption()?;
        }

        Ok(())
    }

    /// Reconstruct the decryption key and decrypt every encrypted
    /// intent in the current batch. Called by
    /// [`Self::contribute_decrypt_share`] once threshold shares for
    /// every ciphertext are available.
    ///
    /// On success, transitions the batch to `Solving` and populates
    /// `decrypted` with the postcard-deserialized [`Intent`]s in the
    /// same order as `encrypted_intents`. Ciphertexts whose plaintext
    /// fails to deserialize as an `Intent` are dropped (malformed
    /// submissions cannot enter the solving phase).
    fn run_threshold_decryption(&mut self) -> Result<(), EngineError> {
        let mut decrypted: Vec<Intent> = Vec::new();
        for ct in self.current_batch.encrypted_intents.iter() {
            let shares = self
                .current_batch
                .decrypt_shares
                .get(&ct.ciphertext_id())
                .ok_or_else(|| EngineError::InsufficientDecryptionShares {
                    have: 0,
                    need: self.decrypt_threshold,
                })?;

            let plaintext = combine_shares(&ct.ciphertext, shares, self.decrypt_threshold)
                .map_err(|e| match e {
                    ThresholdDecryptError::InvalidShareMac(idx) => {
                        EngineError::InvalidDecryptionShare {
                            reason: format!("share MAC verification failed for validator {idx}"),
                        }
                    }
                    ThresholdDecryptError::InsufficientShares { have, need } => {
                        EngineError::InsufficientDecryptionShares { have, need }
                    }
                    other => EngineError::InvalidDecryptionShare {
                        reason: format!("threshold decrypt failed: {other}"),
                    },
                })?;

            // Deserialize the plaintext as an Intent. Malformed
            // ciphertexts are skipped silently — they can never
            // enter the solving phase because no solver can
            // reference an absent IntentId.
            if let Ok(intent) = postcard::from_bytes::<Intent>(&plaintext) {
                decrypted.push(intent);
            }
        }

        self.current_batch.decrypted = Some(decrypted);
        self.current_batch.state = BatchState::Solving;
        Ok(())
    }

    // =========================================================================
    // Layer 4 + 5: SOLVE + PROVE (open competition with validity proofs)
    // =========================================================================

    /// Submit a solver's solution with its validity proof.
    ///
    /// Anyone can submit a solution. The solver must:
    /// 1. Post a bond >= min_solver_bond
    /// 2. Provide a STARK proof that the solution is valid
    /// 3. Include the computed total_score
    ///
    /// The proof is verified immediately. If valid and the score is highest,
    /// this becomes the new winning solution. If this is the first valid solution,
    /// the batch transitions to Challenging.
    pub fn submit_solution(&mut self, submission: SolverSubmission) -> Result<(), EngineError> {
        if self.current_batch.state != BatchState::Solving
            && self.current_batch.state != BatchState::Challenging
        {
            return Err(EngineError::WrongState {
                expected: BatchState::Solving,
                actual: self.current_batch.state,
            });
        }

        // Check bond
        if submission.bond < self.min_solver_bond {
            return Err(EngineError::InsufficientBond {
                provided: submission.bond,
                required: self.min_solver_bond,
            });
        }

        // Check submission limit
        if self.current_batch.solutions.len() >= MAX_SOLVER_SUBMISSIONS {
            return Err(EngineError::TooManySubmissions);
        }

        // Verify the proof FIRST — a malformed submission never holds
        // any bond. The bond is locked only after proof verification
        // succeeds, so failed-proof submissions don't pollute the
        // escrow state (and don't `AlreadyPosted` on retry).
        let decrypted = self
            .current_batch
            .decrypted
            .as_ref()
            .ok_or(EngineError::WrongState {
                expected: BatchState::Solving,
                actual: self.current_batch.state,
            })?;

        self.verifier
            .verify_submission(&submission, decrypted)
            .map_err(|reason| EngineError::InvalidProof { reason })?;

        // Lock the bond in escrow. The bond stays locked until either
        // finalize (release) or a successful challenge (slash). If the
        // solver hasn't pre-deposited enough, the lock fails with
        // InsufficientBond. A solver who is rebidding (same solver,
        // same batch) is already locked — we map `AlreadyPosted` to a
        // gentle no-op (the lock from the first submission still
        // suffices; the new submission inherits the same locked bond).
        let bond_key = BondKey {
            solver_id: submission.solver_id,
            batch_id: self.current_batch.batch_id,
        };
        match self.bond_escrow.lock(
            &submission.solver_id,
            self.current_batch.batch_id,
            submission.bond,
        ) {
            Ok(()) => {}
            Err(crate::bond::BondError::AlreadyPosted) => {
                // Rebid by same solver — the original lock remains
                // active; this submission piggybacks on it.
            }
            Err(crate::bond::BondError::InsufficientBalance { available, .. }) => {
                return Err(EngineError::InsufficientBond {
                    provided: available,
                    required: submission.bond,
                });
            }
            Err(e) => {
                return Err(EngineError::InvalidProof {
                    reason: format!("bond escrow error: {e}"),
                });
            }
        }
        // Bind each participating intent to this (solver, batch) so the
        // slash path can find the bond by intent.
        for ring in &submission.solution {
            for intent_id in &ring.participants {
                self.bond_escrow.bind_intent(*intent_id, bond_key);
            }
        }

        // Check if this beats the current winner
        let is_new_winner = match &self.current_batch.winning_solution {
            None => true,
            Some(current) => submission.total_score > current.total_score,
        };

        if is_new_winner {
            self.current_batch.winning_solution = Some(submission.clone());
            // Transition to Challenging on first valid submission
            if self.current_batch.state == BatchState::Solving {
                self.current_batch.state = BatchState::Challenging;
                self.current_batch.challenge_start_height = Some(self.current_height);
            }
        }

        self.current_batch.solutions.push(submission);
        Ok(())
    }

    // =========================================================================
    // Layer 6: SELECT (challenge window)
    // =========================================================================

    /// Challenge the current winning solution with a better one.
    ///
    /// During the challenge window, anyone can submit a solution with a higher
    /// score. If successful, the challenger's solution replaces the current winner,
    /// and the original solver's bond is slashed (per audit §14 — real
    /// escrow slashing via `BondEscrow::slash`).
    pub fn challenge(&mut self, better_solution: SolverSubmission) -> Result<(), EngineError> {
        if self.current_batch.state != BatchState::Challenging {
            return Err(EngineError::WrongState {
                expected: BatchState::Challenging,
                actual: self.current_batch.state,
            });
        }

        // Check challenge window hasn't expired
        if let Some(start) = self.current_batch.challenge_start_height {
            if self.current_height > start + self.challenge_window {
                return Err(EngineError::ChallengeWindowExpired);
            }
        }

        // The challenge must have a higher score than the current winner
        let current_score = self
            .current_batch
            .winning_solution
            .as_ref()
            .map(|s| s.total_score)
            .unwrap_or(0.0);

        if better_solution.total_score <= current_score {
            return Err(EngineError::ScoreNotHigher {
                submitted: better_solution.total_score,
                current: current_score,
            });
        }

        // Capture the displaced winner's identity before the challenger
        // overwrites it. If submit_solution succeeds and the challenger
        // becomes the new winner, the displaced solver's bond is slashed.
        let displaced = self
            .current_batch
            .winning_solution
            .as_ref()
            .map(|s| s.solver_id);
        let batch_id = self.current_batch.batch_id;

        // Verify and submit through the normal path
        self.submit_solution(better_solution)?;

        // Slash the displaced solver's bond if there was one. The slash
        // ignores NotPosted errors (e.g. if the challenger somehow
        // landed without displacing — should not happen given the
        // higher-score check above).
        if let Some(loser_id) = displaced {
            let _ = self.bond_escrow.slash(&loser_id, batch_id);
        }

        Ok(())
    }

    // =========================================================================
    // Layer 7: SETTLE (atomic compound turn)
    // =========================================================================

    /// Finalize the batch: lower the winning solution into a real `Turn`
    /// via [`lowering::Intent::RingSettlement`] (P2.G).
    ///
    /// This can only be called after the challenge window has expired.
    /// Every ring leg becomes an [`Effect::Transfer`] inside the sealed
    /// turn's call forest, authorized uniformly through
    /// [`lowering::seal_plan_uniform`]. The result lives in
    /// [`SettlementOutput`], which replaces the legacy ad-hoc
    /// `CompoundTurn` carrier.
    ///
    /// The anchor cell is derived deterministically from `solver_id`
    /// (`CellId::from_bytes(solver_id)`) so the same winning submission
    /// produces the same anchor. Federation node deployments override
    /// this by injecting a configured anchor at engine construction time
    /// (TODO follow-up — currently every node reproduces the solver
    /// anchor).
    pub fn finalize(&mut self) -> Result<SettlementOutput, EngineError> {
        if self.current_batch.state != BatchState::Challenging {
            return Err(EngineError::WrongState {
                expected: BatchState::Challenging,
                actual: self.current_batch.state,
            });
        }

        // Verify challenge window has expired
        if let Some(start) = self.current_batch.challenge_start_height {
            if self.current_height <= start + self.challenge_window {
                // Challenge window still open
                return Err(EngineError::WrongState {
                    expected: BatchState::Challenging,
                    actual: self.current_batch.state,
                });
            }
        }

        let winner = self
            .current_batch
            .winning_solution
            .as_ref()
            .ok_or(EngineError::NoWinningSolution)?;

        // Compute proof hash for binding.
        let proof_hash = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-solution-proof-hash-v1");
            hasher.update(&winner.validity_proof);
            *hasher.finalize().as_bytes()
        };

        // Build the high-level RingSettlement intent and lower it through
        // the canonical four-layer tower.
        let anchor = CellId::from_bytes(winner.solver_id);
        let ring_intent = lowering::Intent::RingSettlement {
            rings: winner.solution.clone(),
            anchor,
            solver_id: winner.solver_id,
            validity_proof_hash: proof_hash,
        };
        let plan = lowering::lower(ring_intent, &LoweringContext::default()).map_err(|e| {
            EngineError::SettlementFailed {
                reason: format!("lowering failed: {e}"),
            }
        })?;

        // Seal uniformly with the solver's binding bytes carried as a
        // placeholder Signature. The real federation deployment swaps
        // `seal_plan_uniform` for a per-leg sealer that reads each
        // pending action's `auth_hint`; tests only need a non-Unchecked
        // value to satisfy the SealedTurn invariant.
        let auth = Authorization::Signature(winner.solver_id, proof_hash);
        let sealed = lowering::seal_plan_uniform(plan, anchor, self.current_batch.batch_id, auth);

        let output = SettlementOutput {
            batch_id: self.current_batch.batch_id,
            sealed,
            proof_hash,
            solver_id: winner.solver_id,
        };

        // Release the winning solver's bond (their submission was
        // unchallenged or held up through the challenge window).
        let winner_id = winner.solver_id;
        let batch_id = self.current_batch.batch_id;
        let _ = self.bond_escrow.release(&winner_id, batch_id);

        // Any other submissions for this batch held a locked bond too.
        // Those solvers didn't win but they also weren't successfully
        // challenged — their bonds are returned. (Slashing only applies
        // to losers of a successful challenge, which already happened
        // in `challenge()`. If a solver was already slashed,
        // `release` returns `NotPosted` which is ignored.)
        let other_solvers: Vec<[u8; 32]> = self
            .current_batch
            .solutions
            .iter()
            .filter(|s| s.solver_id != winner_id)
            .map(|s| s.solver_id)
            .collect();
        for solver_id in other_solvers {
            let _ = self.bond_escrow.release(&solver_id, batch_id);
        }

        // Archive and advance to next batch
        self.current_batch.state = BatchState::Settled;
        self.settled_batches
            .insert(self.current_batch.batch_id, output.clone());

        // Start a new batch
        let new_batch_id = self.next_batch_id;
        self.next_batch_id += 1;
        self.current_batch = IntentBatch::new(new_batch_id);

        Ok(output)
    }

    // =========================================================================
    // Height management
    // =========================================================================

    /// Advance the blocklace height. Used for challenge window expiry tracking.
    pub fn advance_height(&mut self, new_height: u64) {
        self.current_height = new_height;
    }

    /// Check if the challenge window has expired for the current batch.
    pub fn is_challenge_window_expired(&self) -> bool {
        if self.current_batch.state != BatchState::Challenging {
            return false;
        }
        match self.current_batch.challenge_start_height {
            Some(start) => self.current_height > start + self.challenge_window,
            None => false,
        }
    }

    /// Get the current batch state.
    pub fn batch_state(&self) -> BatchState {
        self.current_batch.state
    }

    /// Get the number of encrypted intents in the current batch.
    pub fn intent_count(&self) -> usize {
        self.current_batch.encrypted_intents.len()
    }

    /// Get the total number of decryption shares collected across
    /// all ciphertexts in the current batch.
    pub fn decrypt_share_count(&self) -> usize {
        self.current_batch
            .decrypt_shares
            .values()
            .map(|v| v.len())
            .sum()
    }

    /// Get the number of decryption shares collected for a specific
    /// ciphertext (looked up by its `ciphertext_id`).
    pub fn decrypt_share_count_for(&self, ciphertext_id: &[u8; 32]) -> usize {
        self.current_batch
            .decrypt_shares
            .get(ciphertext_id)
            .map(|v| v.len())
            .unwrap_or(0)
    }

    /// Get the current winning score, if any.
    pub fn winning_score(&self) -> Option<f64> {
        self.current_batch
            .winning_solution
            .as_ref()
            .map(|s| s.total_score)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{RingTrade, Settlement};
    use crate::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec};
    use dregg_federation::threshold_decrypt::{
        KeyShare, ThresholdEncryptionKey, generate_epoch_key, produce_decryption_share,
        threshold_encrypt,
    };

    /// Stable test fixture: a single keypair shared across all tests in
    /// this module, generated once so each `TrustlessIntentEngine` test
    /// can encrypt with the same epoch key.
    fn make_test_keys(
        threshold: u8,
        num_validators: u8,
    ) -> (ThresholdEncryptionKey, Vec<KeyShare>) {
        let epoch_id = [0xEEu8; 32];
        generate_epoch_key(epoch_id, threshold, num_validators)
    }

    /// Helper: create a test intent with a deterministic ID.
    fn make_intent(id_seed: u8) -> Intent {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some(format!("action_{}", id_seed)),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        Intent::new(
            IntentKind::Offer,
            spec,
            CommitmentId([id_seed; 32]),
            9999,
            None,
        )
    }

    /// Helper: encrypt an intent under the given threshold key, producing
    /// an [`EncryptedIntent`] ready for submission. Returns the encrypted
    /// intent (caller submits) alongside the intent's content id so tests
    /// can correlate decrypted output with submissions.
    fn encrypt_intent(
        intent: &Intent,
        key: &ThresholdEncryptionKey,
        height: u64,
    ) -> EncryptedIntent {
        let plaintext = postcard::to_allocvec(intent).expect("intent serializes");
        let ciphertext = threshold_encrypt(&plaintext, key).expect("encrypt succeeds");
        EncryptedIntent {
            ciphertext,
            creator_commitment: intent.creator,
            submitted_at: height,
        }
    }

    /// Helper: produce a decryption share for a given encrypted intent
    /// from a specific validator's key share.
    fn make_share_for(enc: &EncryptedIntent, key_share: &KeyShare) -> DecryptionShare {
        produce_decryption_share(&enc.ciphertext, key_share)
    }

    /// Helper: create a solver submission for given intents.
    fn make_submission(
        solver_byte: u8,
        intents: &[Intent],
        score: f64,
        height: u64,
    ) -> SolverSubmission {
        // Build a single ring trade from all intents
        let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
        let mut settlements = Vec::new();
        for i in 0..intents.len() {
            let next = (i + 1) % intents.len();
            settlements.push(Settlement {
                from: intents[i].creator,
                to: intents[next].creator,
                asset: [i as u8; 32],
                amount: 100,
            });
        }

        let ring = RingTrade {
            participants,
            settlements,
            score,
        };

        SolverSubmission {
            solver_id: [solver_byte; 32],
            solution: vec![ring],
            total_score: score,
            validity_proof: vec![0x01, 0x02, 0x03], // non-empty mock proof
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: height,
        }
    }

    /// Helper: build a solver submission that carries a **real**,
    /// cryptographically-verifiable `witnessed_predicate` — a
    /// `NonMembership` neighbor proof. This is the only built-in kind that
    /// ships a real (non-`NotYetWired`) verifier
    /// (`SortedNeighborNonMembershipVerifier` in the cell crate), so a
    /// submission built this way is accepted by the STRICT default verifier
    /// only because the proof bytes genuinely verify against the batch
    /// binding — not because the predicate is absent.
    ///
    /// Construction: the verifier feeds `PredicateInput::Bytes(commitment)`
    /// (the batch binding) as the candidate, requiring `lower < candidate <
    /// upper` plus a commitment-keyed adjacency tag. We pick `lower =
    /// [0x00; 32]` and `upper = [0xFF; 32]` so any candidate is strictly
    /// inside the interval, and compute the honest adjacency tag.
    fn make_real_submission(
        solver_byte: u8,
        intents: &[Intent],
        score: f64,
        height: u64,
    ) -> SolverSubmission {
        use dregg_cell::predicate::NonMembershipNeighborProof;

        let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
        let mut settlements = Vec::new();
        for i in 0..intents.len() {
            let next = (i + 1) % intents.len();
            settlements.push(Settlement {
                from: intents[i].creator,
                to: intents[next].creator,
                asset: [i as u8; 32],
                amount: 100,
            });
        }
        let ring = RingTrade {
            participants,
            settlements,
            score,
        };

        let commitment = WitnessedProofVerifier::compute_batch_binding(intents);
        // Honest neighbor proof: lower < candidate(=commitment) < upper.
        let proof = NonMembershipNeighborProof::new(&commitment, [0x00; 32], [0xFF; 32]);
        let wp = WitnessedPredicate {
            kind: WitnessedPredicateKind::NonMembership,
            commitment,
            input_ref: InputRef::PublicInput { pi_index: 0 },
            proof_witness_index: 0,
        };

        SolverSubmission {
            solver_id: [solver_byte; 32],
            solution: vec![ring],
            total_score: score,
            validity_proof: proof.to_bytes().to_vec(),
            witnessed_predicate: Some(wp),
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: height,
        }
    }

    // =========================================================================
    // Test: Encrypted intents cannot be read before decrypt
    // =========================================================================
    #[test]
    fn test_encrypted_intents_opaque_before_decrypt() {
        let (key, _shares) = make_test_keys(3, 5);
        let mut engine = TrustlessIntentEngine::new(3, 5);

        let intent = make_intent(0x42);
        let enc = encrypt_intent(&intent, &key, 1);
        engine.submit_encrypted(enc).unwrap();

        // The batch has encrypted intents but no decrypted intents
        assert_eq!(engine.current_batch.encrypted_intents.len(), 1);
        assert!(engine.current_batch.decrypted.is_none());

        // The ciphertext payload bytes do not deserialize as a plaintext
        // Intent. (The ChaCha20 keystream randomization plus the
        // Poly1305-style tag at the end ensures it can't masquerade.)
        let raw = &engine.current_batch.encrypted_intents[0]
            .ciphertext
            .ciphertext;
        let attempt: Result<Intent, _> = postcard::from_bytes(raw);
        assert!(
            attempt.is_err(),
            "encrypted intent should not deserialize as plaintext Intent"
        );
    }

    // =========================================================================
    // Test: Batch boundary is deterministic
    // =========================================================================
    #[test]
    fn test_batch_boundary_deterministic() {
        let (key, _shares) = make_test_keys(3, 5);
        let mut engine = TrustlessIntentEngine::new(3, 5);

        // Submit some intents
        engine
            .submit_encrypted(encrypt_intent(&make_intent(1), &key, 1))
            .unwrap();
        engine
            .submit_encrypted(encrypt_intent(&make_intent(2), &key, 2))
            .unwrap();
        engine
            .submit_encrypted(encrypt_intent(&make_intent(3), &key, 3))
            .unwrap();

        // Close at a specific height
        engine.close_batch(100).unwrap();

        // The batch boundary is exactly the set of intents submitted before close
        assert_eq!(engine.current_batch.encrypted_intents.len(), 3);
        assert_eq!(engine.current_batch.batch_boundary_height, 100);
        assert_eq!(engine.current_batch.state, BatchState::AwaitingDecrypt);

        // Cannot submit more intents after close
        let result = engine.submit_encrypted(encrypt_intent(&make_intent(4), &key, 4));
        assert_eq!(
            result.unwrap_err(),
            EngineError::WrongState {
                expected: BatchState::Collecting,
                actual: BatchState::AwaitingDecrypt,
            }
        );
    }

    /// Internal helper: drive the engine through Collecting → Solving
    /// with the given intents, encrypting each under `key` and feeding
    /// `threshold` shares per ciphertext from `key_shares`.
    ///
    /// Side effect: pre-deposits bond funds for every byte-prefix
    /// solver id (`[0x00; 32]`, `[0x01; 32]`, …, `[0xFF; 32]`) so the
    /// submit-solution path's bond locking can find balance. Tests
    /// that need a specifically un-funded solver can override this
    /// via `engine.bond_escrow.withdraw(...)`.
    fn drive_to_solving(
        engine: &mut TrustlessIntentEngine,
        key: &ThresholdEncryptionKey,
        key_shares: &[KeyShare],
        intents: &[Intent],
        close_height: u64,
    ) -> Vec<EncryptedIntent> {
        // Pre-fund every byte-prefix solver_id used by tests.
        for b in 0..=255u8 {
            engine.deposit_bond(&[b; 32], DEFAULT_MIN_SOLVER_BOND * 10);
        }
        let mut enc_intents = Vec::new();
        for (i, intent) in intents.iter().enumerate() {
            let enc = encrypt_intent(intent, key, (i as u64) + 1);
            engine.submit_encrypted(enc.clone()).unwrap();
            enc_intents.push(enc);
        }
        engine.close_batch(close_height).unwrap();
        for enc in enc_intents.iter() {
            for ks in key_shares.iter().take(engine.decrypt_threshold) {
                engine
                    .contribute_decrypt_share(make_share_for(enc, ks))
                    .unwrap();
            }
        }
        assert_eq!(engine.current_batch.state, BatchState::Solving);
        enc_intents
    }

    // =========================================================================
    // Test: Solution with higher score wins
    // =========================================================================
    #[test]
    fn test_higher_score_wins() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);

        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // The engine decrypted the submitted ciphertexts into real intents.
        let decrypted_ids: std::collections::HashSet<IntentId> = engine
            .current_batch
            .decrypted
            .as_ref()
            .unwrap()
            .iter()
            .map(|i| i.id)
            .collect();
        for intent in &intents {
            assert!(
                decrypted_ids.contains(&intent.id),
                "decrypted set must include intent {:?}",
                intent.id[0]
            );
        }

        // Solver A submits with score 5.0 (real verifiable NonMembership proof)
        let sub_a = make_real_submission(0xAA, &intents, 5.0, 11);
        engine.submit_solution(sub_a).unwrap();

        assert_eq!(engine.winning_score(), Some(5.0));

        // Solver B submits with score 8.0 (higher) — also a real proof.
        let sub_b = make_real_submission(0xBB, &intents, 8.0, 12);
        engine.submit_solution(sub_b).unwrap();

        assert_eq!(engine.winning_score(), Some(8.0));
        assert_eq!(
            engine
                .current_batch
                .winning_solution
                .as_ref()
                .unwrap()
                .solver_id,
            [0xBB; 32]
        );
    }

    // =========================================================================
    // Test: Challenge replaces winning solution if score is higher
    // =========================================================================
    #[test]
    fn test_challenge_replaces_winner() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        engine.advance_height(10);

        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // First solution: score 5.0 (real verifiable proof)
        let sub_a = make_real_submission(0xAA, &intents, 5.0, 11);
        engine.submit_solution(sub_a).unwrap();
        assert_eq!(engine.current_batch.state, BatchState::Challenging);
        assert_eq!(engine.winning_score(), Some(5.0));

        // Challenge with score 10.0 (within window) — also a real proof.
        engine.advance_height(12);
        let challenge = make_real_submission(0xCC, &intents, 10.0, 12);
        engine.challenge(challenge).unwrap();

        assert_eq!(engine.winning_score(), Some(10.0));
        assert_eq!(
            engine
                .current_batch
                .winning_solution
                .as_ref()
                .unwrap()
                .solver_id,
            [0xCC; 32]
        );
    }

    // =========================================================================
    // Test: Challenge with lower score rejected
    // =========================================================================
    #[test]
    fn test_challenge_lower_score_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        engine.advance_height(10);

        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // Winner with score 10.0 (real verifiable proof)
        let sub = make_real_submission(0xAA, &intents, 10.0, 11);
        engine.submit_solution(sub).unwrap();

        // Challenge with lower score (3.0 < 10.0). Rejected on the
        // ScoreNotHigher gate, which fires before the proof verifier, so a
        // predicate-less submission is fine here.
        let bad_challenge = SolverSubmission {
            solver_id: [0xBB; 32],
            solution: vec![RingTrade {
                participants: vec![intents[0].id],
                settlements: vec![],
                score: 3.0,
            }],
            total_score: 3.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 12,
        };
        let result = engine.challenge(bad_challenge);
        assert_eq!(
            result.unwrap_err(),
            EngineError::ScoreNotHigher {
                submitted: 3.0,
                current: 10.0,
            }
        );
    }

    // =========================================================================
    // Test: Invalid solution (bad proof) rejected
    // =========================================================================
    #[test]
    fn test_invalid_proof_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // Empty proof -> rejected
        let bad_sub = SolverSubmission {
            solver_id: [0xAA; 32],
            solution: vec![],
            total_score: 5.0,
            validity_proof: vec![],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 11,
        };
        let result = engine.submit_solution(bad_sub);
        assert!(matches!(result, Err(EngineError::InvalidProof { .. })));
    }

    // =========================================================================
    // Test: Score mismatch in proof rejected
    // =========================================================================
    #[test]
    fn test_score_mismatch_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let bad_sub = SolverSubmission {
            solver_id: [0xAA; 32],
            solution: vec![RingTrade {
                participants: vec![intents[0].id],
                settlements: vec![],
                score: 5.0,
            }],
            total_score: 100.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 11,
        };
        let result = engine.submit_solution(bad_sub);
        assert!(matches!(result, Err(EngineError::InvalidProof { .. })));
    }

    // =========================================================================
    // Test: Intent not in batch rejected
    // =========================================================================
    #[test]
    fn test_intent_not_in_batch_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let phantom_intent = make_intent(99);
        let bad_sub = SolverSubmission {
            solver_id: [0xAA; 32],
            solution: vec![RingTrade {
                participants: vec![phantom_intent.id],
                settlements: vec![],
                score: 5.0,
            }],
            total_score: 5.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 11,
        };
        let result = engine.submit_solution(bad_sub);
        assert!(matches!(result, Err(EngineError::InvalidProof { .. })));
    }

    // =========================================================================
    // Test: Duplicate intent usage in solution rejected
    // =========================================================================
    #[test]
    fn test_duplicate_intent_usage_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let bad_sub = SolverSubmission {
            solver_id: [0xAA; 32],
            solution: vec![
                RingTrade {
                    participants: vec![intents[0].id],
                    settlements: vec![],
                    score: 3.0,
                },
                RingTrade {
                    participants: vec![intents[0].id],
                    settlements: vec![],
                    score: 3.0,
                },
            ],
            total_score: 6.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 11,
        };
        let result = engine.submit_solution(bad_sub);
        assert!(matches!(result, Err(EngineError::InvalidProof { .. })));
    }

    // =========================================================================
    // Test: Settlement is atomic (all-or-nothing finalization)
    // =========================================================================
    #[test]
    fn test_settlement_atomic() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        engine.advance_height(10);

        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_real_submission(0xAA, &intents, 7.0, 11);
        engine.submit_solution(sub).unwrap();
        assert_eq!(engine.current_batch.state, BatchState::Challenging);

        engine.advance_height(20);

        let compound = engine.finalize().unwrap();

        assert!(!compound.sealed.turn.call_forest.roots.is_empty());
        assert_eq!(compound.batch_id, 0);
        assert_eq!(compound.solver_id, [0xAA; 32]);

        for root in &compound.sealed.turn.call_forest.roots {
            assert_eq!(root.action.effects.len(), 1);
            assert!(matches!(
                root.action.effects[0],
                dregg_turn::action::Effect::Transfer { .. }
            ));
        }

        assert_eq!(engine.current_batch.state, BatchState::Collecting);
        assert_eq!(engine.current_batch.batch_id, 1);
        assert!(engine.settled_batches.contains_key(&0));
    }

    // =========================================================================
    // Test: Cannot finalize during challenge window
    // =========================================================================
    #[test]
    fn test_cannot_finalize_during_challenge() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        engine.advance_height(10);

        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_real_submission(0xAA, &intents, 5.0, 11);
        engine.submit_solution(sub).unwrap();
        assert_eq!(engine.current_batch.state, BatchState::Challenging);

        let result = engine.finalize();
        assert!(result.is_err());
    }

    // =========================================================================
    // Test: Insufficient bond rejected
    // =========================================================================
    #[test]
    fn test_insufficient_bond_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let bad_sub = SolverSubmission {
            solver_id: [0xAA; 32],
            solution: vec![RingTrade {
                participants: vec![intents[0].id],
                settlements: vec![],
                score: 5.0,
            }],
            total_score: 5.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: 1,
            submitted_at: 11,
        };
        let result = engine.submit_solution(bad_sub);
        assert_eq!(
            result.unwrap_err(),
            EngineError::InsufficientBond {
                provided: 1,
                required: DEFAULT_MIN_SOLVER_BOND,
            }
        );
    }

    // =========================================================================
    // Test: Duplicate encrypted intent rejected
    // =========================================================================
    #[test]
    fn test_duplicate_encrypted_intent_rejected() {
        let (key, _shares) = make_test_keys(3, 5);
        let mut engine = TrustlessIntentEngine::new(3, 5);

        let enc = encrypt_intent(&make_intent(0x42), &key, 1);
        engine.submit_encrypted(enc.clone()).unwrap();

        // Same ciphertext again -> duplicate
        let result = engine.submit_encrypted(enc);
        assert_eq!(result.unwrap_err(), EngineError::DuplicateIntent);
    }

    // =========================================================================
    // Test: Full protocol flow (happy path) — full threshold decryption
    // =========================================================================
    #[test]
    fn test_full_protocol_flow() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        // Pre-fund the byte-prefix solver IDs for the bond escrow.
        for b in 0..=255u8 {
            engine.deposit_bond(&[b; 32], DEFAULT_MIN_SOLVER_BOND * 10);
        }
        engine.advance_height(1);

        // Layer 1: Submit encrypted intents
        let intents = vec![make_intent(1), make_intent(2), make_intent(3)];
        let mut enc_intents = Vec::new();
        for (i, intent) in intents.iter().enumerate() {
            let enc = encrypt_intent(intent, &key, (i as u64) + 1);
            enc_intents.push(enc.clone());
            engine.submit_encrypted(enc).unwrap();
        }
        assert_eq!(engine.batch_state(), BatchState::Collecting);
        assert_eq!(engine.intent_count(), 3);

        // Layer 2: Close batch
        engine.close_batch(5).unwrap();
        assert_eq!(engine.batch_state(), BatchState::AwaitingDecrypt);

        // Layer 3: Threshold decryption — partial shares first.
        // Provide one share per ciphertext from validator 1; not enough
        // to reach threshold on any individual ciphertext.
        for enc in enc_intents.iter() {
            engine
                .contribute_decrypt_share(make_share_for(enc, &key_shares[0]))
                .unwrap();
        }
        assert_eq!(engine.batch_state(), BatchState::AwaitingDecrypt);

        // Add the second share per ciphertext — threshold reached.
        for enc in enc_intents.iter() {
            engine
                .contribute_decrypt_share(make_share_for(enc, &key_shares[1]))
                .unwrap();
        }
        assert_eq!(engine.batch_state(), BatchState::Solving);

        // The engine populated `decrypted` itself; the cleartext side-
        // channel `set_decrypted_intents` is no longer reachable.
        let decrypted = engine.current_batch.decrypted.as_ref().unwrap();
        assert_eq!(decrypted.len(), 3);
        let decrypted_ids: std::collections::HashSet<IntentId> =
            decrypted.iter().map(|i| i.id).collect();
        for intent in &intents {
            assert!(decrypted_ids.contains(&intent.id));
        }

        // Layer 4+5: Solve + Prove
        engine.advance_height(10);
        let sub = make_real_submission(0xAA, &intents, 9.0, 10);
        engine.submit_solution(sub).unwrap();
        assert_eq!(engine.batch_state(), BatchState::Challenging);

        // Layer 6: Challenge window
        assert!(!engine.is_challenge_window_expired());
        engine.advance_height(20);
        assert!(engine.is_challenge_window_expired());

        // Layer 7: Settle
        let compound = engine.finalize().unwrap();
        assert_eq!(compound.batch_id, 0);
        assert_eq!(compound.solver_id, [0xAA; 32]);
        assert!(!compound.sealed.turn.call_forest.roots.is_empty());

        assert_eq!(engine.batch_state(), BatchState::Collecting);
        assert_eq!(engine.current_batch.batch_id, 1);
    }

    // =========================================================================
    // Test: Threshold not reached -> stays in AwaitingDecrypt
    // =========================================================================
    #[test]
    fn test_threshold_not_reached() {
        let (key, key_shares) = make_test_keys(3, 5);
        let mut engine = TrustlessIntentEngine::new(3, 5);

        let intent = make_intent(1);
        let enc = encrypt_intent(&intent, &key, 1);
        engine.submit_encrypted(enc.clone()).unwrap();
        engine.close_batch(10).unwrap();

        // Only 2 shares (need 3)
        engine
            .contribute_decrypt_share(make_share_for(&enc, &key_shares[0]))
            .unwrap();
        engine
            .contribute_decrypt_share(make_share_for(&enc, &key_shares[1]))
            .unwrap();

        // Still awaiting decrypt
        assert_eq!(engine.batch_state(), BatchState::AwaitingDecrypt);
        assert_eq!(engine.decrypt_share_count(), 2);
    }

    // =========================================================================
    // Test: Challenge window expiry
    // =========================================================================
    #[test]
    fn test_challenge_window_expiry() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        engine.advance_height(10);

        let intents = vec![make_intent(1)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_real_submission(0xAA, &intents, 5.0, 11);
        engine.submit_solution(sub).unwrap();

        engine.advance_height(16);
        assert!(engine.is_challenge_window_expired());

        // Late challenge rejected by the window gate (before the verifier),
        // so a predicate-less submission is fine here.
        let late_challenge = SolverSubmission {
            solver_id: [0xBB; 32],
            solution: vec![RingTrade {
                participants: vec![intents[0].id],
                settlements: vec![],
                score: 99.0,
            }],
            total_score: 99.0,
            validity_proof: vec![0x01],
            witnessed_predicate: None,
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: 16,
        };
        let result = engine.challenge(late_challenge);
        assert_eq!(result.unwrap_err(), EngineError::ChallengeWindowExpired);
    }

    // =========================================================================
    // Test: Duplicate validator share rejected
    // =========================================================================
    #[test]
    fn test_duplicate_validator_share_rejected() {
        let (key, key_shares) = make_test_keys(3, 5);
        let mut engine = TrustlessIntentEngine::new(3, 5);

        let intent = make_intent(1);
        let enc = encrypt_intent(&intent, &key, 1);
        engine.submit_encrypted(enc.clone()).unwrap();
        engine.close_batch(10).unwrap();

        engine
            .contribute_decrypt_share(make_share_for(&enc, &key_shares[0]))
            .unwrap();

        // Same validator again — same ciphertext, same validator
        let result = engine.contribute_decrypt_share(make_share_for(&enc, &key_shares[0]));
        assert!(matches!(
            result,
            Err(EngineError::InvalidDecryptionShare { .. })
        ));
    }

    // =========================================================================
    // Test: Tampered share is detected via MAC verification
    // =========================================================================
    #[test]
    fn test_tampered_share_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);

        let intent = make_intent(1);
        let enc = encrypt_intent(&intent, &key, 1);
        engine.submit_encrypted(enc.clone()).unwrap();
        engine.close_batch(10).unwrap();

        // Validator 1 contributes a HONEST share.
        engine
            .contribute_decrypt_share(make_share_for(&enc, &key_shares[0]))
            .unwrap();
        // Validator 2 contributes a CORRUPTED share — share bytes flipped.
        let mut bad = make_share_for(&enc, &key_shares[1]);
        bad.share = [0xFF; 32];

        // contribute_decrypt_share stores it (it can't tell the share is
        // bad in isolation), then once threshold is met,
        // run_threshold_decryption invokes combine_shares which catches
        // the MAC failure and returns an error.
        let result = engine.contribute_decrypt_share(bad);
        assert!(
            matches!(result, Err(EngineError::InvalidDecryptionShare { .. })),
            "expected InvalidDecryptionShare, got: {result:?}"
        );
        // Batch should not have advanced to Solving on a corrupted share.
        assert_eq!(engine.batch_state(), BatchState::AwaitingDecrypt);
    }

    // =========================================================================
    // Test: Share for a ciphertext NOT in the batch is rejected
    // =========================================================================
    #[test]
    fn test_share_for_unknown_ciphertext_rejected() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);

        // Submit one intent.
        let intent = make_intent(1);
        let enc_in_batch = encrypt_intent(&intent, &key, 1);
        engine.submit_encrypted(enc_in_batch).unwrap();
        engine.close_batch(10).unwrap();

        // Encrypt a DIFFERENT intent under the same key — not submitted
        // to this batch.
        let phantom = make_intent(99);
        let phantom_enc = encrypt_intent(&phantom, &key, 1);

        // A share bound to the phantom ciphertext_id must be rejected.
        let bad = make_share_for(&phantom_enc, &key_shares[0]);
        let result = engine.contribute_decrypt_share(bad);
        assert!(matches!(
            result,
            Err(EngineError::InvalidDecryptionShare { .. })
        ));
    }

    // =========================================================================
    // Adversarial tests: WitnessedProofVerifier dispatch through the
    // canonical WitnessedPredicateRegistry.
    // =========================================================================

    /// Helper: build a SolverSubmission for the given intents that
    /// carries a `witnessed_predicate` declaration with the supplied
    /// kind. The commitment is set to the canonical batch binding for
    /// `intents`; tests that want to tamper with the binding override
    /// it after construction.
    fn make_witnessed_submission(
        solver_byte: u8,
        intents: &[Intent],
        score: f64,
        height: u64,
        kind: WitnessedPredicateKind,
        proof_bytes: Vec<u8>,
    ) -> SolverSubmission {
        let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
        let mut settlements = Vec::new();
        for i in 0..intents.len() {
            let next = (i + 1) % intents.len();
            settlements.push(Settlement {
                from: intents[i].creator,
                to: intents[next].creator,
                asset: [i as u8; 32],
                amount: 100,
            });
        }

        let ring = RingTrade {
            participants,
            settlements,
            score,
        };

        let commitment = WitnessedProofVerifier::compute_batch_binding(intents);
        let wp = WitnessedPredicate {
            kind,
            commitment,
            input_ref: InputRef::PublicInput { pi_index: 0 },
            proof_witness_index: 0,
        };

        SolverSubmission {
            solver_id: [solver_byte; 32],
            solution: vec![ring],
            total_score: score,
            validity_proof: proof_bytes,
            witnessed_predicate: Some(wp),
            bond: DEFAULT_MIN_SOLVER_BOND,
            submitted_at: height,
        }
    }

    #[test]
    fn witnessed_verifier_accepts_dfa_kind_with_stub_registry() {
        // Plumbing test: use the explicit stub-verifier constructor.
        // The new `new()` default installs NotYetWiredVerifier (P0 #82),
        // which would reject this submission.
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::with_stub_verifier(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Dfa,
            vec![0x01, 0x02, 0x03],
        );
        engine
            .submit_solution(sub)
            .expect("DFA stub verifier accepts non-empty proof bytes");
        assert_eq!(engine.winning_score(), Some(5.0));
    }

    /// P0 #82 adversarial test: a production-style engine constructed via
    /// `TrustlessIntentEngine::new` (the default constructor) must NOT
    /// silently accept a witnessed predicate against a kind whose real
    /// verifier has not been installed. Pre-fix the default used the
    /// permissive stub registry, which accepted any non-empty proof bytes
    /// against any built-in kind. After the fix the default installs
    /// `NotYetWiredVerifier` for non-NonMembership built-ins, which rejects
    /// with a clear "not yet wired" reason.
    #[test]
    fn p0_82_default_engine_rejects_witnessed_predicate_not_yet_wired() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // Submit a DFA witnessed-predicate with non-empty proof bytes.
        // Under the pre-fix stub default, this would be silently accepted.
        // Under the strict default (default_builtins → NotYetWiredVerifier),
        // it must reject with a clear "not yet wired" reason.
        let sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Dfa,
            vec![0x01, 0x02, 0x03],
        );
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("not yet wired") || reason.contains("not yet installed"),
                    "expected 'not yet wired' surface from NotYetWiredVerifier, got: {reason}"
                );
            }
            other => panic!(
                "default engine must NOT silently accept a not-yet-wired witnessed predicate, got: {other:?}"
            ),
        }
    }

    /// HOLE CLOSED (SILVER-DEBT T1.2): the production default
    /// `TrustlessIntentEngine::new` installs the STRICT verifier, so a
    /// submission that omits `witnessed_predicate` is REJECTED — its
    /// `validity_proof` is never accepted on the structural check alone. This
    /// test pins the fail-CLOSED posture so any accidental regression back to
    /// the permissive default surfaces here.
    ///
    /// (Previously `nonstrict_default_accepts_predicateless_submission_known_hole`,
    /// which pinned the now-closed fail-OPEN behavior.)
    #[test]
    fn predicateless_submission_is_rejected_hole_closed() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        // A submission with NO witnessed predicate and an arbitrary,
        // never-verified `validity_proof`. The strict production default must
        // REJECT it rather than wave the proof bytes through.
        let sub = make_submission(0xAA, &intents, 5.0, 11);
        assert!(
            sub.witnessed_predicate.is_none(),
            "this test exercises the (now-closed) predicate-less bypass path"
        );
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("requires a witnessed_predicate"),
                    "expected strict-mode predicate-required rejection, got: {reason}"
                );
            }
            other => panic!(
                "HOLE: production default must REJECT a predicate-less submission \
                 (proof bytes never verified otherwise). Got: {other:?}"
            ),
        }
    }

    /// Companion to the known-hole test: a `strict` verifier (the correct
    /// production posture) DOES reject the same predicate-less submission. This
    /// proves the fix is one constructor swap away — `new()` only needs to call
    /// `WitnessedProofVerifier::strict(..)` instead of `::new(..)` once the
    /// node + predicate-less tests are migrated.
    #[test]
    fn strict_verifier_rejects_predicateless_submission() {
        let (key, key_shares) = make_test_keys(2, 3);
        let registry = WitnessedPredicateRegistry::default_builtins();
        let mut engine = TrustlessIntentEngine::with_verifier(
            2,
            3,
            Box::new(WitnessedProofVerifier::strict(registry)),
        );
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_submission(0xAA, &intents, 5.0, 11);
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("requires a witnessed_predicate"),
                    "expected strict-mode predicate-required rejection, got: {reason}"
                );
            }
            other => panic!(
                "strict verifier MUST reject a predicate-less submission, got: {other:?}"
            ),
        }
    }

    /// P0 #82: same adversarial check for `IntentPredicateVerifier::default()`
    /// — the programmatic-defaults surface used by app callers must also
    /// fail-closed on a not-yet-wired kind.
    #[test]
    fn p0_82_default_predicate_verifier_rejects_dfa_kind() {
        use crate::predicate::{IntentPredicateVerifier, ResourceDfa};

        let verifier = IntentPredicateVerifier::default();
        let dfa = ResourceDfa::new([0x11; 32], vec![0xAB, 0xCD]);
        let result = verifier.matches_resource(&dfa, "documents/x");
        assert!(
            result.is_err(),
            "default IntentPredicateVerifier must reject DFA proof (not-yet-wired)"
        );
        let err = format!("{}", result.unwrap_err());
        assert!(
            err.contains("not yet wired") || err.contains("not yet installed"),
            "expected not-yet-wired reason, got: {err}"
        );
    }

    #[test]
    fn witnessed_verifier_rejects_unknown_custom_vk_hash() {
        // The default stub registry doesn't register any Custom { vk_hash }
        // verifiers — an unknown vk_hash surfaces as a KindNotRegistered
        // rejection that the engine maps to InvalidProof.
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Custom {
                vk_hash: [0x99; 32],
            },
            vec![0x01, 0x02, 0x03],
        );
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("not registered") || reason.contains("Custom"),
                    "expected KindNotRegistered surface, got: {reason}"
                );
            }
            other => panic!("expected InvalidProof for unknown Custom vk_hash, got: {other:?}"),
        }
    }

    #[test]
    fn witnessed_verifier_accepts_registered_custom_vk_hash() {
        // Register a custom kind, then submit with the matching vk_hash.
        use dregg_cell::predicate::{
            PredicateInput, WitnessedPredicateError, WitnessedPredicateVerifier as WpVerifier,
        };
        use std::sync::Arc;

        struct AcceptAll;
        impl WpVerifier for AcceptAll {
            fn name(&self) -> &'static str {
                "test-accept-all"
            }
            fn kind(&self) -> WitnessedPredicateKind {
                WitnessedPredicateKind::Custom {
                    vk_hash: [0x77; 32],
                }
            }
            fn verify(
                &self,
                _commitment: &[u8; 32],
                _input: &PredicateInput<'_>,
                _proof_bytes: &[u8],
            ) -> Result<(), WitnessedPredicateError> {
                Ok(())
            }
        }

        let mut reg = WitnessedPredicateRegistry::with_stubs();
        reg.register_custom([0x77; 32], Arc::new(AcceptAll));

        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine =
            TrustlessIntentEngine::with_verifier(2, 3, Box::new(WitnessedProofVerifier::new(reg)));
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Custom {
                vk_hash: [0x77; 32],
            },
            vec![0xAB, 0xCD],
        );
        engine
            .submit_solution(sub)
            .expect("registered Custom kind should verify");
        assert_eq!(engine.winning_score(), Some(5.0));
    }

    #[test]
    fn witnessed_verifier_rejects_tampered_batch_binding() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let mut sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Dfa,
            vec![0x01, 0x02, 0x03],
        );
        // Tamper: rewrite the commitment to a different value. The
        // verifier must reject because the proof's "audience" no longer
        // matches the decrypted batch.
        if let Some(ref mut wp) = sub.witnessed_predicate {
            wp.commitment = [0xFF; 32];
        }
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("batch binding"),
                    "expected batch-binding rejection, got: {reason}"
                );
            }
            other => {
                panic!("expected InvalidProof for tampered commitment, got: {other:?}")
            }
        }
    }

    #[test]
    fn witnessed_verifier_rejects_empty_proof_bytes() {
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Dfa,
            vec![], // empty
        );
        assert!(matches!(
            engine.submit_solution(sub),
            Err(EngineError::InvalidProof { .. })
        ));
    }

    #[test]
    fn witnessed_verifier_strict_mode_rejects_missing_predicate() {
        // A strict verifier rejects any submission whose
        // `witnessed_predicate` is None — production posture.
        let reg = WitnessedPredicateRegistry::with_stubs();
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::with_verifier(
            2,
            3,
            Box::new(WitnessedProofVerifier::strict(reg)),
        );
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let sub = make_submission(0xAA, &intents, 5.0, 11);
        assert!(matches!(
            engine.submit_solution(sub),
            Err(EngineError::InvalidProof { .. })
        ));
    }

    #[test]
    fn witnessed_verifier_rejects_signing_message_input_outside_action_context() {
        // SigningMessage InputRef is for `Authorization::Custom` only —
        // applying it to a solver proof is a shape mismatch.
        let (key, key_shares) = make_test_keys(2, 3);
        let mut engine = TrustlessIntentEngine::new(2, 3);
        let intents = vec![make_intent(1), make_intent(2)];
        drive_to_solving(&mut engine, &key, &key_shares, &intents, 10);

        let mut sub = make_witnessed_submission(
            0xAA,
            &intents,
            5.0,
            11,
            WitnessedPredicateKind::Dfa,
            vec![0x01, 0x02],
        );
        if let Some(ref mut wp) = sub.witnessed_predicate {
            wp.input_ref = InputRef::SigningMessage;
        }
        let result = engine.submit_solution(sub);
        match result {
            Err(EngineError::InvalidProof { reason }) => {
                assert!(
                    reason.contains("SigningMessage"),
                    "expected SigningMessage shape mismatch, got: {reason}"
                );
            }
            other => panic!("expected InvalidProof for SigningMessage input, got: {other:?}"),
        }
    }

    #[test]
    fn batch_binding_is_deterministic_and_order_independent() {
        let i1 = make_intent(1);
        let i2 = make_intent(2);
        let i3 = make_intent(3);
        let b1 =
            WitnessedProofVerifier::compute_batch_binding(&[i1.clone(), i2.clone(), i3.clone()]);
        let b2 =
            WitnessedProofVerifier::compute_batch_binding(&[i3.clone(), i1.clone(), i2.clone()]);
        let b3 = WitnessedProofVerifier::compute_batch_binding(&[i1, i2]);
        assert_eq!(b1, b2, "binding must be order-independent");
        assert_ne!(b1, b3, "binding must change with intent membership");
    }
}
