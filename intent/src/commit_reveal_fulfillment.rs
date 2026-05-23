//! Commit-reveal anti-frontrunning for the fulfillment execution path.
//!
//! The gossip layer (`gossip.rs`) has a commit-reveal protocol that prevents
//! front-running at the discovery layer. This module extends that protection
//! into the actual fulfillment execution path:
//!
//! 1. **Commit phase**: A fulfiller who finds a match commits to fulfilling it
//!    by broadcasting a blinded commitment (hash of intent_id + secret + epoch).
//!    Other fulfillers see "someone committed" but don't know who or how.
//!
//! 2. **Reveal + Execute phase**: After the commit window elapses, the fulfiller
//!    reveals their secret, proving they committed first, and executes the
//!    actual fulfillment (token presentation, proof generation).
//!
//! Without this, a malicious observer could see a matching intent, watch the
//! gossip layer for matches, and race to submit their own fulfillment first.
//!
//! # Integration with `gossip.rs`
//!
//! The `FulfillmentRegistry` tracks commitments independently of the `IntentPool`'s
//! own commit-reveal (which operates at the gossip/pool level). This module
//! provides a higher-level `CommitRevealFulfiller` that orchestrates the full
//! two-phase flow and delegates to the existing `fulfill()` function for the
//! actual proof/token generation.

use std::collections::HashMap;

use crate::fulfillment::{FulfillOptions, Fulfillment, FulfillmentError, fulfill};
use crate::gossip::COMMIT_REVEAL_WINDOW_SECS;
use crate::matcher::HeldCapability;
use crate::{CommitmentId, Intent, Match, current_epoch};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from the commit-reveal fulfillment protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommitRevealFulfillmentError {
    /// No commitment was registered for this intent by this fulfiller.
    NoCommitment,
    /// The reveal window has not yet elapsed since the commitment.
    TooEarly { remaining_secs: u64 },
    /// The commitment has expired (reveal window passed without reveal).
    Expired,
    /// The secret does not match the registered commitment.
    SecretMismatch,
    /// Another fulfiller committed earlier and has priority.
    PriorityConflict { first_committed_at: u64 },
    /// The underlying fulfillment failed.
    FulfillmentFailed(FulfillmentError),
    /// The intent has already been fulfilled via commit-reveal.
    AlreadyFulfilled,
    /// The commitment ID has been blocked due to too many abandoned commitments
    /// (commits without reveals) in this epoch.
    AbandonPenalty { abandons: u8, max: u8 },
}

impl std::fmt::Display for CommitRevealFulfillmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoCommitment => write!(f, "no commitment registered for this fulfillment"),
            Self::TooEarly { remaining_secs } => {
                write!(
                    f,
                    "reveal too early, {}s remaining in window",
                    remaining_secs
                )
            }
            Self::Expired => write!(f, "commitment expired: reveal window missed"),
            Self::SecretMismatch => write!(f, "secret does not match registered commitment"),
            Self::PriorityConflict { first_committed_at } => {
                write!(
                    f,
                    "another fulfiller committed first (at timestamp {})",
                    first_committed_at
                )
            }
            Self::FulfillmentFailed(e) => write!(f, "fulfillment failed: {}", e),
            Self::AlreadyFulfilled => write!(f, "intent already fulfilled via commit-reveal"),
            Self::AbandonPenalty { abandons, max } => {
                write!(
                    f,
                    "commitment ID blocked: {} abandoned commits (max {} per epoch)",
                    abandons, max
                )
            }
        }
    }
}

impl std::error::Error for CommitRevealFulfillmentError {}

/// Maximum number of abandoned commitments (commit without reveal) allowed per
/// commitment hash per epoch. After this many abandons, the commitment ID is
/// blocked from future commits for the rest of the epoch.
pub const MAX_ABANDONS_PER_EPOCH: u8 = 3;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A commitment to fulfill a specific intent, binding the fulfiller's identity
/// and a secret that will be revealed later.
#[derive(Clone, Debug)]
pub struct FulfillmentCommitment {
    /// The intent being claimed for fulfillment.
    pub intent_id: [u8; 32],
    /// The blinded commitment: BLAKE3(intent_id || fulfiller_secret || epoch).
    pub commitment_hash: [u8; 32],
    /// When this commitment was registered (Unix seconds).
    pub committed_at: u64,
    /// The epoch at the time of commitment.
    pub epoch: u64,
}

/// The result of a successful reveal-and-fulfill operation.
#[derive(Clone, Debug)]
pub struct FulfillmentResult {
    /// The produced fulfillment.
    pub fulfillment: Fulfillment,
    /// The commitment that was revealed.
    pub commitment: FulfillmentCommitment,
    /// The epoch in which the fulfillment was executed.
    pub fulfilled_epoch: u64,
}

/// Maximum time (in seconds) a commitment remains valid for reveal.
/// After this window, the commitment expires and the slot reopens.
pub const COMMITMENT_EXPIRY_SECS: u64 = 60;

// ---------------------------------------------------------------------------
// FulfillmentRegistry: tracks commitments and enforces ordering
// ---------------------------------------------------------------------------

/// Registry that tracks fulfillment commitments and enforces ordering.
///
/// This is the enforcement layer: it ensures that only the first committer
/// (by timestamp) can reveal and execute, preventing front-running even
/// when multiple parties discover the same match simultaneously.
pub struct FulfillmentRegistry {
    /// Maps intent_id -> list of commitments (ordered by committed_at).
    commitments: HashMap<[u8; 32], Vec<FulfillmentCommitment>>,
    /// Set of intent IDs that have been fulfilled through this registry.
    fulfilled: std::collections::HashSet<[u8; 32]>,
    /// Current block height (for epoch computation).
    current_block_height: u64,
    /// Tracks abandoned commitment counts per commitment_hash per epoch.
    /// Key is the commitment_hash from the FulfillmentCommitment (identifies the committer).
    /// Value is the number of times that committer has abandoned (committed without revealing).
    /// Reset when the epoch advances.
    abandoned_count: HashMap<[u8; 32], u8>,
    /// The epoch in which the abandoned_count was last relevant.
    /// When the current epoch advances past this, abandoned_count is cleared.
    abandon_epoch: u64,
}

impl FulfillmentRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            commitments: HashMap::new(),
            fulfilled: std::collections::HashSet::new(),
            current_block_height: 0,
            abandoned_count: HashMap::new(),
            abandon_epoch: 0,
        }
    }

    /// Update the current block height.
    ///
    /// When the epoch advances, the abandon penalty counters are cleared
    /// (fresh epoch = fresh slate for all committers).
    pub fn update_block_height(&mut self, height: u64) {
        let new_epoch = current_epoch(height);
        if new_epoch > self.abandon_epoch {
            self.abandoned_count.clear();
            self.abandon_epoch = new_epoch;
        }
        self.current_block_height = height;
    }

    /// Get the current epoch.
    pub fn current_epoch(&self) -> u64 {
        current_epoch(self.current_block_height)
    }

    /// Register a commitment to fulfill an intent.
    ///
    /// Returns the commitment on success, or an error if the intent is already
    /// fulfilled or if the committer has been blocked due to abandon penalties.
    pub fn register_commitment(
        &mut self,
        intent_id: [u8; 32],
        fulfiller_secret: &[u8; 32],
        now: u64,
    ) -> Result<FulfillmentCommitment, CommitRevealFulfillmentError> {
        if self.fulfilled.contains(&intent_id) {
            return Err(CommitRevealFulfillmentError::AlreadyFulfilled);
        }

        let epoch = current_epoch(self.current_block_height);
        let commitment_hash = compute_commitment_hash(&intent_id, fulfiller_secret, epoch);

        // SECURITY: Check if this commitment ID has been penalized for too many
        // abandoned commitments in this epoch.
        if let Some(&count) = self.abandoned_count.get(&commitment_hash) {
            if count >= MAX_ABANDONS_PER_EPOCH {
                return Err(CommitRevealFulfillmentError::AbandonPenalty {
                    abandons: count,
                    max: MAX_ABANDONS_PER_EPOCH,
                });
            }
        }

        let commitment = FulfillmentCommitment {
            intent_id,
            commitment_hash,
            committed_at: now,
            epoch,
        };

        self.commitments
            .entry(intent_id)
            .or_default()
            .push(commitment.clone());

        Ok(commitment)
    }

    /// Check whether a reveal is valid: the secret matches a registered commitment,
    /// the window has elapsed, the commitment hasn't expired, and this is the
    /// first (highest priority) committer.
    pub fn validate_reveal(
        &self,
        intent_id: &[u8; 32],
        fulfiller_secret: &[u8; 32],
        now: u64,
    ) -> Result<&FulfillmentCommitment, CommitRevealFulfillmentError> {
        if self.fulfilled.contains(intent_id) {
            return Err(CommitRevealFulfillmentError::AlreadyFulfilled);
        }

        let commitments = self
            .commitments
            .get(intent_id)
            .ok_or(CommitRevealFulfillmentError::NoCommitment)?;

        // Find the commitment matching this secret.
        // SECURITY FIX: Use each commitment's stored epoch (the epoch at commit
        // time) to recompute the expected hash, NOT the current epoch. If the epoch
        // advances between commit and reveal, using the current epoch would produce
        // a different hash and the reveal would always fail at epoch boundaries.
        let matching = commitments
            .iter()
            .find(|c| {
                let expected_hash = compute_commitment_hash(intent_id, fulfiller_secret, c.epoch);
                c.commitment_hash == expected_hash
            })
            .ok_or(CommitRevealFulfillmentError::SecretMismatch)?;

        // Check the reveal window has elapsed
        let elapsed = now.saturating_sub(matching.committed_at);
        if elapsed < COMMIT_REVEAL_WINDOW_SECS {
            return Err(CommitRevealFulfillmentError::TooEarly {
                remaining_secs: COMMIT_REVEAL_WINDOW_SECS - elapsed,
            });
        }

        // Check the commitment hasn't expired
        if elapsed > COMMITMENT_EXPIRY_SECS {
            return Err(CommitRevealFulfillmentError::Expired);
        }

        // Check priority: this must be the earliest commitment for this intent
        // (only non-expired commitments count)
        let earliest_valid = commitments
            .iter()
            .filter(|c| now.saturating_sub(c.committed_at) <= COMMITMENT_EXPIRY_SECS)
            .min_by_key(|c| c.committed_at);

        if let Some(earliest) = earliest_valid {
            if earliest.committed_at < matching.committed_at {
                return Err(CommitRevealFulfillmentError::PriorityConflict {
                    first_committed_at: earliest.committed_at,
                });
            }
        }

        Ok(matching)
    }

    /// Mark an intent as fulfilled, removing all pending commitments.
    pub fn mark_fulfilled(&mut self, intent_id: [u8; 32]) {
        self.fulfilled.insert(intent_id);
        self.commitments.remove(&intent_id);
    }

    /// Garbage-collect expired commitments.
    ///
    /// Commitments that expire without being revealed are considered "abandoned."
    /// The committer's abandon count is incremented as a penalty. After
    /// `MAX_ABANDONS_PER_EPOCH` abandons, the commitment ID is blocked for
    /// the rest of the epoch.
    pub fn gc(&mut self, now: u64) {
        for commitments in self.commitments.values_mut() {
            // Track which commitments are being removed as abandoned (expired without reveal)
            for c in commitments.iter() {
                if now.saturating_sub(c.committed_at) > COMMITMENT_EXPIRY_SECS {
                    // This commitment expired without reveal -> count as abandon
                    let count = self.abandoned_count.entry(c.commitment_hash).or_insert(0);
                    *count = count.saturating_add(1);
                }
            }
            commitments.retain(|c| now.saturating_sub(c.committed_at) <= COMMITMENT_EXPIRY_SECS);
        }
        // Remove entries with no remaining commitments
        self.commitments.retain(|_, v| !v.is_empty());
    }

    /// Check if an intent has any pending (non-expired) commitments.
    pub fn has_pending_commitments(&self, intent_id: &[u8; 32], now: u64) -> bool {
        self.commitments
            .get(intent_id)
            .map(|cs| {
                cs.iter()
                    .any(|c| now.saturating_sub(c.committed_at) <= COMMITMENT_EXPIRY_SECS)
            })
            .unwrap_or(false)
    }

    /// Check if an intent has been fulfilled through this registry.
    pub fn is_fulfilled(&self, intent_id: &[u8; 32]) -> bool {
        self.fulfilled.contains(intent_id)
    }

    /// Get the number of pending commitments for an intent.
    pub fn commitment_count(&self, intent_id: &[u8; 32]) -> usize {
        self.commitments
            .get(intent_id)
            .map(|cs| cs.len())
            .unwrap_or(0)
    }

    /// Get the abandon count for a given commitment hash in the current epoch.
    pub fn abandon_count_for(&self, commitment_hash: &[u8; 32]) -> u8 {
        self.abandoned_count
            .get(commitment_hash)
            .copied()
            .unwrap_or(0)
    }
}

impl Default for FulfillmentRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// CommitRevealFulfiller: wraps fulfill() with two-phase protection
// ---------------------------------------------------------------------------

/// A fulfiller that wraps the existing `fulfill_intent` with a two-phase
/// commit-reveal protocol to prevent front-running.
///
/// Usage:
/// 1. Call `commit_to_fulfillment()` when a match is found.
/// 2. Wait for the commit window to elapse.
/// 3. Call `reveal_and_fulfill()` to prove commitment priority and execute.
pub struct CommitRevealFulfiller {
    /// The registry tracking commitments and ordering.
    pub registry: FulfillmentRegistry,
    /// Our anonymous commitment identity.
    our_commitment: CommitmentId,
}

impl CommitRevealFulfiller {
    /// Create a new commit-reveal fulfiller.
    pub fn new(our_commitment: CommitmentId) -> Self {
        Self {
            registry: FulfillmentRegistry::new(),
            our_commitment,
        }
    }

    /// Phase 1: Commit to fulfilling an intent.
    ///
    /// Produces a blinded commitment (hash of intent_id + fulfiller_secret + epoch)
    /// that is broadcast/submitted before revealing the actual fulfillment.
    /// Other fulfillers see "someone committed" but don't know who or how.
    ///
    /// The caller should broadcast the returned `FulfillmentCommitment` to the
    /// network so that others know a commitment exists.
    pub fn commit_to_fulfillment(
        &mut self,
        intent_id: &[u8; 32],
        fulfiller_secret: &[u8; 32],
        now: u64,
    ) -> Result<FulfillmentCommitment, CommitRevealFulfillmentError> {
        self.registry
            .register_commitment(*intent_id, fulfiller_secret, now)
    }

    /// Phase 2: Reveal the secret and execute the fulfillment.
    ///
    /// This:
    /// 1. Validates that the secret matches a registered commitment.
    /// 2. Checks the commit window has elapsed (anti-frontrunning).
    /// 3. Checks this fulfiller has priority (committed first).
    /// 4. Executes the actual fulfillment (calls `fulfill()`).
    /// 5. Marks the intent as fulfilled in the registry.
    ///
    /// Returns the fulfillment result on success, or rejects if:
    /// - No commitment was registered (front-running attempt)
    /// - The window hasn't elapsed yet
    /// - Another fulfiller committed earlier
    /// - The commitment has expired
    pub fn reveal_and_fulfill(
        &mut self,
        intent: &Intent,
        matched: &Match,
        source_token: &HeldCapability,
        fulfiller_secret: &[u8; 32],
        options: &FulfillOptions,
        now: u64,
    ) -> Result<FulfillmentResult, CommitRevealFulfillmentError> {
        // Validate the reveal
        let commitment = self
            .registry
            .validate_reveal(&intent.id, fulfiller_secret, now)?
            .clone();

        // Execute the actual fulfillment
        let fulfillment = fulfill(intent, matched, source_token, self.our_commitment, options)
            .map_err(CommitRevealFulfillmentError::FulfillmentFailed)?;

        // Mark as fulfilled
        self.registry.mark_fulfilled(intent.id);

        Ok(FulfillmentResult {
            fulfillment,
            commitment,
            fulfilled_epoch: current_epoch(self.registry.current_block_height),
        })
    }

    /// Update the block height (delegates to registry).
    pub fn update_block_height(&mut self, height: u64) {
        self.registry.update_block_height(height);
    }

    /// Run garbage collection on expired commitments.
    pub fn gc(&mut self, now: u64) {
        self.registry.gc(now);
    }
}

// ---------------------------------------------------------------------------
// Public API: standalone functions for use without CommitRevealFulfiller
// ---------------------------------------------------------------------------

/// Compute a fulfillment commitment hash from intent_id, secret, and epoch.
///
/// This is the binding commitment: `BLAKE3(intent_id || fulfiller_secret || epoch)`.
/// It hides the fulfiller's identity and strategy while binding them to the intent.
pub fn compute_commitment_hash(
    intent_id: &[u8; 32],
    fulfiller_secret: &[u8; 32],
    epoch: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-commit-reveal-v1");
    hasher.update(intent_id);
    hasher.update(fulfiller_secret);
    hasher.update(&epoch.to_le_bytes());
    *hasher.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matcher::Sensitivity;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec, VerificationMode};

    fn test_intent() -> Intent {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None)
    }

    fn test_match(intent: &Intent) -> Match {
        Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        }
    }

    fn test_source_token() -> HeldCapability {
        HeldCapability {
            token_id: "tok_test".into(),
            actions: vec!["read".into(), "write".into()],
            resource: "*".into(),
            app_id: None,
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: Some(10000),
            budget: None,
            sensitivity: Sensitivity::Normal,
        }
    }

    fn test_root_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[1] = 0x13;
        key[31] = 0xFF;
        key
    }

    // =========================================================================
    // FulfillmentRegistry tests
    // =========================================================================

    #[test]
    fn test_commit_reveal_normal_flow() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let secret = [0xCC; 32];

        // Phase 1: Commit
        let commitment = registry
            .register_commitment(intent.id, &secret, 100)
            .unwrap();
        assert_eq!(commitment.intent_id, intent.id);
        assert_eq!(commitment.committed_at, 100);
        assert!(registry.has_pending_commitments(&intent.id, 100));

        // Too early to reveal
        let result = registry.validate_reveal(&intent.id, &secret, 102);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::TooEarly { remaining_secs: 3 }
        );

        // Phase 2: Reveal after window (5 seconds)
        let result = registry.validate_reveal(&intent.id, &secret, 106);
        assert!(result.is_ok());
        let validated = result.unwrap();
        assert_eq!(validated.commitment_hash, commitment.commitment_hash);

        // Mark fulfilled
        registry.mark_fulfilled(intent.id);
        assert!(registry.is_fulfilled(&intent.id));
        assert!(!registry.has_pending_commitments(&intent.id, 200));
    }

    #[test]
    fn test_commit_reveal_frontrunning_rejected() {
        let registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let wrong_secret = [0xFF; 32];

        // No commitment registered, try to reveal directly -> rejected
        let result = registry.validate_reveal(&intent.id, &wrong_secret, 200);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::NoCommitment
        );
    }

    #[test]
    fn test_commit_reveal_wrong_secret_rejected() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let real_secret = [0xCC; 32];
        let wrong_secret = [0xDD; 32];

        // Commit with real secret
        registry
            .register_commitment(intent.id, &real_secret, 100)
            .unwrap();

        // Try to reveal with wrong secret after window
        let result = registry.validate_reveal(&intent.id, &wrong_secret, 106);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::SecretMismatch
        );
    }

    #[test]
    fn test_commit_reveal_expired() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let secret = [0xCC; 32];

        // Commit at time 100
        registry
            .register_commitment(intent.id, &secret, 100)
            .unwrap();

        // Try to reveal way after expiry (100 + 60 + 1 = 161)
        let result = registry.validate_reveal(&intent.id, &secret, 161);
        assert_eq!(result.unwrap_err(), CommitRevealFulfillmentError::Expired);
    }

    #[test]
    fn test_commit_reveal_double_commit_first_wins() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let secret_a = [0xAA; 32];
        let secret_b = [0xBB; 32];

        // Fulfiller A commits first at time 100
        registry
            .register_commitment(intent.id, &secret_a, 100)
            .unwrap();

        // Fulfiller B commits second at time 102
        registry
            .register_commitment(intent.id, &secret_b, 102)
            .unwrap();

        assert_eq!(registry.commitment_count(&intent.id), 2);

        // Both wait for window. Fulfiller B tries to reveal at time 108 (102 + 6).
        // But A committed first, so B gets PriorityConflict.
        let result = registry.validate_reveal(&intent.id, &secret_b, 108);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::PriorityConflict {
                first_committed_at: 100
            }
        );

        // Fulfiller A reveals at time 106 (100 + 6) -> success
        let result = registry.validate_reveal(&intent.id, &secret_a, 106);
        assert!(result.is_ok());
    }

    #[test]
    fn test_commit_reveal_already_fulfilled() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let secret = [0xCC; 32];

        // Commit and fulfill
        registry
            .register_commitment(intent.id, &secret, 100)
            .unwrap();
        registry.mark_fulfilled(intent.id);

        // Try to commit again -> rejected
        let result = registry.register_commitment(intent.id, &secret, 200);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::AlreadyFulfilled
        );

        // Try to reveal -> rejected
        let result = registry.validate_reveal(&intent.id, &secret, 200);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::AlreadyFulfilled
        );
    }

    #[test]
    fn test_commit_reveal_gc_cleans_expired() {
        let mut registry = FulfillmentRegistry::new();
        let intent = test_intent();
        let secret = [0xCC; 32];

        registry
            .register_commitment(intent.id, &secret, 100)
            .unwrap();
        assert_eq!(registry.commitment_count(&intent.id), 1);

        // GC at time well past expiry
        registry.gc(200);
        assert_eq!(registry.commitment_count(&intent.id), 0);
        assert!(!registry.has_pending_commitments(&intent.id, 200));
    }

    #[test]
    fn test_commit_reveal_priority_after_first_expires() {
        let registry = &mut FulfillmentRegistry::new();
        let intent = test_intent();
        let secret_a = [0xAA; 32];
        let secret_b = [0xBB; 32];

        // A commits at 100
        registry
            .register_commitment(intent.id, &secret_a, 100)
            .unwrap();

        // B commits at 150
        registry
            .register_commitment(intent.id, &secret_b, 150)
            .unwrap();

        // A's commitment expires at 100 + 60 = 160.
        // B tries to reveal at 156 (150 + 6). A is still valid (160 > 156), so B loses.
        let result = registry.validate_reveal(&intent.id, &secret_b, 156);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::PriorityConflict {
                first_committed_at: 100
            }
        );

        // At time 162, A has expired. B can now reveal (150 + 6 = 156 <= 162).
        let result = registry.validate_reveal(&intent.id, &secret_b, 162);
        assert!(
            result.is_ok(),
            "B should get priority after A expires: {:?}",
            result.err()
        );
    }

    // =========================================================================
    // CommitRevealFulfiller integration tests
    // =========================================================================

    #[test]
    fn test_commit_reveal_fulfiller_happy_path() {
        let our_id = CommitmentId([0xBB; 32]);
        let mut fulfiller = CommitRevealFulfiller::new(our_id);

        let intent = test_intent();
        let matched = test_match(&intent);
        let token = test_source_token();
        let secret = [0xCC; 32];

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        // Phase 1: Commit
        let commitment = fulfiller
            .commit_to_fulfillment(&intent.id, &secret, 100)
            .unwrap();
        assert_eq!(commitment.intent_id, intent.id);

        // Phase 2: Reveal + Fulfill (after window)
        let result =
            fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 106);
        assert!(result.is_ok(), "should succeed: {:?}", result.err());

        let fres = result.unwrap();
        assert_eq!(fres.fulfillment.intent_id, intent.id);
        assert_eq!(fres.fulfillment.granted_actions, vec!["read".to_string()]);
        assert_eq!(fres.fulfillment.mode, VerificationMode::Trusted);
        assert!(fres.fulfillment.token_data.is_some());

        // Intent should now be marked fulfilled
        assert!(fulfiller.registry.is_fulfilled(&intent.id));
    }

    #[test]
    fn test_commit_reveal_fulfiller_no_commit_rejected() {
        let our_id = CommitmentId([0xBB; 32]);
        let mut fulfiller = CommitRevealFulfiller::new(our_id);

        let intent = test_intent();
        let matched = test_match(&intent);
        let token = test_source_token();
        let secret = [0xCC; 32];

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        // Try to reveal without committing -> front-running attempt rejected
        let result =
            fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 200);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::NoCommitment
        );
    }

    #[test]
    fn test_commit_reveal_fulfiller_too_early_rejected() {
        let our_id = CommitmentId([0xBB; 32]);
        let mut fulfiller = CommitRevealFulfiller::new(our_id);

        let intent = test_intent();
        let matched = test_match(&intent);
        let token = test_source_token();
        let secret = [0xCC; 32];

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        // Commit at 100
        fulfiller
            .commit_to_fulfillment(&intent.id, &secret, 100)
            .unwrap();

        // Try to reveal at 103 (only 3s elapsed, need 5s)
        let result =
            fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 103);
        assert_eq!(
            result.unwrap_err(),
            CommitRevealFulfillmentError::TooEarly { remaining_secs: 2 }
        );
    }

    #[test]
    fn test_commit_reveal_fulfiller_expired_rejected() {
        let our_id = CommitmentId([0xBB; 32]);
        let mut fulfiller = CommitRevealFulfiller::new(our_id);

        let intent = test_intent();
        let matched = test_match(&intent);
        let token = test_source_token();
        let secret = [0xCC; 32];

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        // Commit at 100
        fulfiller
            .commit_to_fulfillment(&intent.id, &secret, 100)
            .unwrap();

        // Try to reveal at 200 (100s elapsed, max is 60s) -> expired
        let result =
            fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 200);
        assert_eq!(result.unwrap_err(), CommitRevealFulfillmentError::Expired);
    }

    #[test]
    fn test_commit_reveal_fulfiller_double_fulfill_rejected() {
        let our_id = CommitmentId([0xBB; 32]);
        let mut fulfiller = CommitRevealFulfiller::new(our_id);

        let intent = test_intent();
        let matched = test_match(&intent);
        let token = test_source_token();
        let secret = [0xCC; 32];

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        // First commit + reveal succeeds
        fulfiller
            .commit_to_fulfillment(&intent.id, &secret, 100)
            .unwrap();
        let result =
            fulfiller.reveal_and_fulfill(&intent, &matched, &token, &secret, &options, 106);
        assert!(result.is_ok());

        // Second attempt to commit -> rejected
        let result2 = fulfiller.commit_to_fulfillment(&intent.id, &secret, 200);
        assert_eq!(
            result2.unwrap_err(),
            CommitRevealFulfillmentError::AlreadyFulfilled
        );
    }
}
