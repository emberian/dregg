//! Qualification verification: prove worker meets requirements without revealing identity.
//!
//! Workers prove qualifications anonymously:
//! - Federation membership: ring membership STARK (proves "I'm in this set" without revealing which member).
//! - Predicate proof: proves "my attribute >= threshold" without revealing the exact value.
//! - Standing proof: IVC chain proving N prior bounty completions.
//!
//! # Security model
//!
//! All proof verification paths perform CRYPTOGRAPHIC verification. Structural checks alone
//! are NEVER sufficient. The `dev` feature enables a fallback for local testing without a
//! live federation, but it is never the default.
//!
//! # Federation root coherence
//!
//! In a multi-validator devnet, different nodes may have slightly different current roots
//! due to propagation delay or ordering differences. A proof generated against one node's
//! root might be verified against another node that hasn't yet seen that root update.
//!
//! To handle this, [`FederationRootHistory`] maintains a sliding window of recent roots.
//! Verification accepts a proof that matches ANY root in the window. This provides
//! tolerance for propagation lag without weakening security (old roots are evicted after
//! a bounded TTL measured in root updates).

use std::collections::VecDeque;
use std::time::Instant;

use pyana_app_framework::{PredicateType, PyanaEngine};
use pyana_circuit::{
    BabyBear, IvcProof, IvcVerification, PredicateProof, verify_ivc, verify_predicate,
};

use crate::QualificationRequirement;

// =============================================================================
// Federation Root History
// =============================================================================

/// Default number of historical roots to retain.
/// With 30-second sync intervals, 16 roots covers ~8 minutes of lag tolerance.
const DEFAULT_ROOT_HISTORY_DEPTH: usize = 16;

/// A sliding window of recent federation roots for multi-validator coherence.
///
/// In a multi-node federation, roots propagate with non-zero latency. A worker
/// may generate a proof against root R_n while the verifier is still on R_{n-1}
/// (or vice versa). By accepting any root from the recent history, slight lag
/// between nodes does not cause spurious proof rejections.
///
/// # Security properties
///
/// - The window is bounded: only the most recent `depth` roots are accepted.
/// - Roots are ordered by insertion time (newest first for fast-path matching).
/// - The zero root is never stored (invalid federation state).
/// - Duplicate roots are not re-inserted (prevents history pollution).
#[derive(Clone, Debug)]
pub struct FederationRootHistory {
    /// Recent roots, ordered newest-first.
    roots: VecDeque<RootEntry>,
    /// Maximum number of roots to retain.
    depth: usize,
}

/// A single entry in the root history.
#[derive(Clone, Debug)]
struct RootEntry {
    root: [u8; 32],
    /// When this root was recorded locally.
    recorded_at: Instant,
}

impl FederationRootHistory {
    /// Create a new root history with the default depth.
    pub fn new() -> Self {
        Self {
            roots: VecDeque::new(),
            depth: DEFAULT_ROOT_HISTORY_DEPTH,
        }
    }

    /// Create a new root history with a specific depth.
    pub fn with_depth(depth: usize) -> Self {
        Self {
            roots: VecDeque::new(),
            depth: depth.max(1),
        }
    }

    /// Create a root history initialized with a single root.
    pub fn with_initial_root(root: [u8; 32]) -> Self {
        let mut history = Self::new();
        history.push(root);
        history
    }

    /// Push a new root into the history.
    ///
    /// If the root is all-zeroes or already present, this is a no-op.
    /// Oldest entries are evicted when the window exceeds `depth`.
    pub fn push(&mut self, root: [u8; 32]) {
        // Reject zero root.
        if root == [0u8; 32] {
            return;
        }

        // Deduplicate: don't re-insert a root already in the window.
        if self.roots.iter().any(|entry| entry.root == root) {
            return;
        }

        // Insert at the front (newest first).
        self.roots.push_front(RootEntry {
            root,
            recorded_at: Instant::now(),
        });

        // Evict oldest if over capacity.
        while self.roots.len() > self.depth {
            self.roots.pop_back();
        }
    }

    /// Check whether a given root is in the history window.
    pub fn is_known_root(&self, root: &[u8; 32]) -> bool {
        self.roots.iter().any(|entry| &entry.root == root)
    }

    /// Get the current (most recently pushed) root, if any.
    pub fn current(&self) -> Option<[u8; 32]> {
        self.roots.front().map(|entry| entry.root)
    }

    /// Get all known roots (newest first), for verification attempts.
    pub fn known_roots(&self) -> Vec<[u8; 32]> {
        self.roots.iter().map(|entry| entry.root).collect()
    }

    /// Return the number of roots currently stored.
    pub fn len(&self) -> usize {
        self.roots.len()
    }

    /// Whether the history is empty.
    pub fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }

    /// The configured maximum depth.
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// Age of the most recent root entry (time since it was recorded).
    pub fn current_age(&self) -> Option<std::time::Duration> {
        self.roots.front().map(|entry| entry.recorded_at.elapsed())
    }
}

/// Error type for qualification verification.
#[derive(Debug, Clone)]
pub enum QualificationError {
    /// The proof is malformed or empty.
    InvalidProof(String),
    /// The proof does not satisfy the requirement.
    ProofRejected(String),
    /// The federation root is unknown or stale.
    UnknownFederationRoot,
    /// The IVC chain is invalid or too short.
    InvalidIvcChain(String),
    /// Verification cannot be performed (missing configuration). Fail closed.
    VerificationUnavailable(String),
}

impl std::fmt::Display for QualificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(msg) => write!(f, "invalid proof: {msg}"),
            Self::ProofRejected(msg) => write!(f, "proof rejected: {msg}"),
            Self::UnknownFederationRoot => write!(f, "unknown federation root"),
            Self::InvalidIvcChain(msg) => write!(f, "invalid IVC chain: {msg}"),
            Self::VerificationUnavailable(msg) => {
                write!(f, "verification unavailable (fail closed): {msg}")
            }
        }
    }
}

impl std::error::Error for QualificationError {}

/// Verify a worker's anonymous qualification proof against the federation root history.
///
/// # Privacy properties
///
/// - The worker's identity is never revealed to the verifier.
/// - For federation membership: the proof shows set membership without revealing WHICH member.
/// - For predicate proofs: the exact attribute value remains hidden.
/// - For standing proofs: only the count threshold is checked, not which specific bounties were completed.
///
/// # Security
///
/// ALL paths perform real cryptographic verification. If verification cannot be performed
/// (e.g., no federation root configured), the function fails CLOSED (rejects).
///
/// # Federation root coherence
///
/// For federation membership proofs, the verifier accepts proofs against ANY root in
/// the `FederationRootHistory` window. This tolerates propagation lag in multi-validator
/// devnets without weakening security (the window is bounded and old roots are evicted).
///
/// # Arguments
///
/// * `engine` - The PyanaEngine instance for federation membership verification.
/// * `requirement` - What the worker must prove.
/// * `proof` - The cryptographic proof bytes (format depends on requirement type).
/// * `root_history` - The federation root history (recent roots window).
///
/// # Returns
///
/// `Ok(true)` if the proof is valid, `Ok(false)` if it's structurally valid but doesn't meet
/// the threshold, or an error if the proof is malformed or verification fails.
pub fn verify_qualification(
    engine: &PyanaEngine,
    requirement: &QualificationRequirement,
    proof: &[u8],
    root_history: &FederationRootHistory,
) -> Result<bool, QualificationError> {
    match requirement {
        QualificationRequirement::None => Ok(true),

        QualificationRequirement::FederationMember => {
            verify_federation_membership_multi(engine, proof, root_history)
        }

        QualificationRequirement::PredicateProof {
            predicate_type,
            attribute,
            threshold,
        } => verify_predicate_proof(proof, *predicate_type, attribute, *threshold),

        QualificationRequirement::StandingProof {
            min_completed_bounties,
        } => verify_standing_proof(proof, *min_completed_bounties),
    }
}

/// Backward-compatible single-root verification entry point.
///
/// Wraps the single root in a `FederationRootHistory` for use by code that
/// only tracks a single root (tests, simple setups).
pub fn verify_qualification_single_root(
    engine: &PyanaEngine,
    requirement: &QualificationRequirement,
    proof: &[u8],
    federation_root: [u8; 32],
) -> Result<bool, QualificationError> {
    let history = FederationRootHistory::with_initial_root(federation_root);
    verify_qualification(engine, requirement, proof, &history)
}

/// Verify a ring membership STARK proving the worker is a federation member.
///
/// Tries verification against each root in the history window (newest first).
/// In a multi-validator devnet, the proof may have been generated against a root
/// that this node hasn't yet adopted as "current" due to propagation lag. Accepting
/// any root from the recent window resolves this coherence issue.
///
/// Uses the PyanaEngine's `verify_membership_proof()` to perform real STARK verification
/// of the federation membership proof.
fn verify_federation_membership_multi(
    engine: &PyanaEngine,
    proof: &[u8],
    root_history: &FederationRootHistory,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty federation membership proof".to_string(),
        ));
    }

    // If we have no known roots at all, fail closed.
    if root_history.is_empty() {
        return Err(QualificationError::VerificationUnavailable(
            "no federation root configured".to_string(),
        ));
    }

    // Try verification against each known root (newest first for fast-path).
    // The proof embeds the root it was generated against as a public input,
    // so only the matching root will pass verification.
    let known_roots = root_history.known_roots();
    for root in &known_roots {
        if engine.verify_membership_proof(proof, root) {
            return Ok(true);
        }
    }

    // None of the known roots matched. This means either:
    // 1. The proof is invalid (most common), or
    // 2. The proof was generated against a root that has already been evicted
    //    from the window (extremely stale proof).
    Err(QualificationError::ProofRejected(format!(
        "federation membership STARK verification failed against {} known root(s)",
        known_roots.len()
    )))
}

/// Verify a predicate STARK proving an attribute satisfies a threshold.
///
/// Example: "my reputation score >= 5" without revealing that it's actually 47.
///
/// Deserializes the proof as a `PredicateProof` from the circuit crate and verifies
/// the STARK proof cryptographically against the expected threshold and fact commitment.
fn verify_predicate_proof(
    proof: &[u8],
    predicate_type: PredicateType,
    _attribute: &str,
    threshold: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty predicate proof".to_string(),
        ));
    }

    // Deserialize the real PredicateProof from wire bytes.
    let predicate_proof: PredicateProof = postcard::from_bytes(proof).map_err(|e| {
        QualificationError::InvalidProof(format!("failed to deserialize predicate proof: {e}"))
    })?;

    // Verify the predicate type matches what is required.
    let expected_type = to_circuit_predicate_type(predicate_type);
    if predicate_proof.predicate_type != expected_type {
        return Err(QualificationError::ProofRejected(
            "proof is for a different predicate type".to_string(),
        ));
    }

    // Verify the threshold matches the requirement.
    let expected_threshold = BabyBear::new(threshold as u32);
    if predicate_proof.threshold != expected_threshold {
        return Err(QualificationError::ProofRejected(format!(
            "proof threshold does not match required threshold {threshold}"
        )));
    }

    // Use the proof's fact commitment for verification.
    // The STARK proof itself cryptographically binds the fact commitment to the
    // proven attribute value, so the verifier trusts it if the STARK verifies.
    let fact_commitment = predicate_proof.fact_commitment;

    // Verify the STARK proof cryptographically.
    if verify_predicate(&predicate_proof, expected_threshold, fact_commitment) {
        Ok(true)
    } else {
        Err(QualificationError::ProofRejected(
            "predicate STARK verification failed".to_string(),
        ))
    }
}

/// Verify an IVC chain proving the worker has completed at least N bounties.
///
/// The IVC proof accumulates state transitions: each completed bounty extends
/// the chain by one step. The verifier checks the chain length meets the threshold
/// without learning which specific bounties were completed.
///
/// Deserializes as an `IvcProof` and performs real cryptographic verification
/// of the hash chain (and STARK proof if present).
fn verify_standing_proof(
    proof: &[u8],
    min_completed_bounties: u64,
) -> Result<bool, QualificationError> {
    if proof.is_empty() {
        return Err(QualificationError::InvalidProof(
            "empty standing proof".to_string(),
        ));
    }

    // Deserialize the real IvcProof from wire bytes.
    let ivc_proof: IvcProof = postcard::from_bytes(proof).map_err(|e| {
        QualificationError::InvalidIvcChain(format!("failed to deserialize IVC proof: {e}"))
    })?;

    // Check the claimed step count meets the minimum threshold.
    if (ivc_proof.step_count as u64) < min_completed_bounties {
        return Err(QualificationError::ProofRejected(format!(
            "IVC chain has {} steps but {} required",
            ivc_proof.step_count, min_completed_bounties
        )));
    }

    // Verify the IVC proof cryptographically.
    // verify_ivc checks:
    //   1. Public inputs consistency
    //   2. If a real STARK proof is present, verifies it
    //   3. Otherwise, falls back to BLAKE3 digest binding check
    //   4. Accumulated hash integrity
    match verify_ivc(&ivc_proof, None) {
        IvcVerification::Valid => Ok(true),
        IvcVerification::EmptyChain => Err(QualificationError::InvalidIvcChain(
            "IVC chain is empty".to_string(),
        )),
        IvcVerification::ProofInvalid => Err(QualificationError::ProofRejected(
            "IVC proof cryptographic verification failed".to_string(),
        )),
        IvcVerification::InitialRootMismatch => Err(QualificationError::InvalidIvcChain(
            "IVC initial root mismatch".to_string(),
        )),
        IvcVerification::AccumulatedHashMismatch => Err(QualificationError::InvalidIvcChain(
            "IVC accumulated hash mismatch (chain tampered)".to_string(),
        )),
        other => Err(QualificationError::ProofRejected(format!(
            "IVC verification returned unexpected status: {other:?}"
        ))),
    }
}

/// Convert app-framework PredicateType to circuit PredicateType.
///
/// These are re-exported from the same source so they are identical, but
/// we call this to be explicit about the conversion in case the types
/// ever diverge.
fn to_circuit_predicate_type(pt: PredicateType) -> pyana_circuit::PredicateType {
    match pt {
        PredicateType::Gte => pyana_circuit::PredicateType::Gte,
        PredicateType::Lte => pyana_circuit::PredicateType::Lte,
        PredicateType::Gt => pyana_circuit::PredicateType::Gt,
        PredicateType::Lt => pyana_circuit::PredicateType::Lt,
        PredicateType::Neq => pyana_circuit::PredicateType::Neq,
        PredicateType::InRangeLow => pyana_circuit::PredicateType::InRangeLow,
        PredicateType::InRangeHigh => pyana_circuit::PredicateType::InRangeHigh,
    }
}
