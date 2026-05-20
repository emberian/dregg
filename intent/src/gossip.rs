//! Intent gossip: propagation and local pool management.
//!
//! Intents propagate through the gossip network (Plumtree lazy-push) so that
//! all connected wallets can attempt local matching. The IntentPool manages
//! the set of known intents with expiry-based garbage collection.
//!
//! # Privacy properties
//!
//! - Intents themselves are PUBLIC: everyone sees "someone needs X"
//! - The creator is anonymous (CommitmentId, not an identity)
//! - Matches are PRIVATE: never broadcast, sent directly to the creator
//!
//! # Security hardening
//!
//! - Gossip-received intents MUST have a valid stake commitment
//! - All intents are validated against size limits before storage
//! - Per-creator rate limiting prevents spam floods
//! - Commit-reveal protocol prevents fulfillment frontrunning

use std::collections::HashMap;

use crate::{CommitmentId, Intent, IntentKind, Match, MatchSpec};
use crate::fulfillment::Fulfillment;
use crate::matcher::{HeldCapability, MatchResult, match_intent};
use crate::validation::{self, ValidationError};

/// Maximum intents allowed per creator per minute.
pub const MAX_INTENTS_PER_CREATOR_PER_MINUTE: usize = 10;

/// Rate limiting window duration in seconds.
pub const RATE_LIMIT_WINDOW_SECS: u64 = 60;

/// Commit-reveal window duration in seconds.
/// First valid commitment wins priority; others must wait this long before competing.
pub const COMMIT_REVEAL_WINDOW_SECS: u64 = 5;

/// Error returned when an intent is rejected by the pool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiveError {
    /// The intent has expired.
    Expired,
    /// The intent is a duplicate (already in pool).
    Duplicate,
    /// The intent was broadcast by us.
    OwnIntent,
    /// The intent failed validation (size limits, etc.).
    Invalid(ValidationError),
    /// The intent lacks a valid stake commitment (required for gossip).
    MissingStake,
    /// The creator has exceeded the rate limit.
    RateLimited {
        creator: CommitmentId,
        count: usize,
        max: usize,
    },
}

impl std::fmt::Display for ReceiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expired => write!(f, "intent has expired"),
            Self::Duplicate => write!(f, "intent is a duplicate"),
            Self::OwnIntent => write!(f, "intent is from this wallet"),
            Self::Invalid(e) => write!(f, "validation error: {e}"),
            Self::MissingStake => write!(f, "intent lacks valid stake commitment for gossip"),
            Self::RateLimited { creator, count, max } => {
                write!(
                    f,
                    "creator {:?} rate limited: {count} intents exceeds max {max}",
                    &creator.0[..4]
                )
            }
        }
    }
}

impl std::error::Error for ReceiveError {}

// ---------------------------------------------------------------------------
// Commit-Reveal Protocol (anti-frontrunning)
// ---------------------------------------------------------------------------

/// Phase 1: Satisfier commits to fulfilling an intent (blinded).
///
/// The commitment hides which fulfillment will be revealed, preventing
/// other satisfiers from copying the solution.
#[derive(Clone, Debug)]
pub struct FulfillmentCommitment {
    /// The intent being fulfilled.
    pub intent_id: [u8; 32],
    /// BLAKE3(fulfillment_data || nonce) -- hides the actual fulfillment.
    pub satisfier_commitment: [u8; 32],
    /// When the commitment was made (Unix seconds).
    pub timestamp: u64,
}

/// Phase 2: Satisfier reveals the actual fulfillment.
///
/// Must match a previously submitted commitment. The nonce proves this
/// reveal corresponds to the earlier commitment.
#[derive(Clone, Debug)]
pub struct FulfillmentReveal {
    /// Hash of the FulfillmentCommitment (for lookup).
    pub commitment_hash: [u8; 32],
    /// The actual fulfillment data.
    pub fulfillment: Fulfillment,
    /// Random nonce used in the commitment: proves this matches.
    pub nonce: [u8; 32],
}

/// Configuration for the intent pool.
#[derive(Clone, Debug)]
pub struct IntentPoolConfig {
    /// Maximum number of intents to hold in the pool.
    pub max_intents: usize,
    /// How often to run garbage collection (seconds).
    pub gc_interval_secs: u64,
    /// Whether to automatically match incoming intents against held tokens.
    pub auto_match: bool,
}

impl Default for IntentPoolConfig {
    fn default() -> Self {
        Self {
            max_intents: 10_000,
            gc_interval_secs: 60,
            auto_match: true,
        }
    }
}

/// Policy for auto-fulfillment when a match is found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutoFulfillPolicy {
    /// Never auto-fulfill; always ask the user.
    Never,
    /// Auto-fulfill for intents matching these resource patterns.
    ForPatterns(Vec<String>),
    /// Auto-fulfill everything (dangerous, but useful for automated agents).
    Always,
}

/// Callback type for match notifications.
pub type MatchCallback = Box<dyn Fn(&Intent, &Match) + Send + Sync>;

/// The local pool of known intents (like a mempool for capabilities).
///
/// Stores active intents, performs garbage collection on expired ones,
/// and triggers local matching when new intents arrive.
pub struct IntentPool {
    /// Active intents indexed by their content-addressed ID.
    intents: HashMap<[u8; 32], Intent>,
    /// Our wallet's held capabilities (for matching).
    held_tokens: Vec<HeldCapability>,
    /// Our anonymous commitment identity.
    our_commitment: CommitmentId,
    /// Pool configuration.
    config: IntentPoolConfig,
    /// Auto-fulfillment policy.
    auto_fulfill: AutoFulfillPolicy,
    /// Pending matches waiting for user approval or auto-fulfillment.
    pending_matches: Vec<(Intent, Match)>,
    /// Intents we have broadcast (to avoid re-matching our own).
    our_intent_ids: Vec<[u8; 32]>,
    /// Rate limiting: tracks (window_start, count) per creator.
    recent_by_creator: HashMap<CommitmentId, (u64, usize)>,
    /// Pending fulfillment commitments (commit-reveal anti-frontrunning).
    pending_commitments: HashMap<[u8; 32], FulfillmentCommitment>,
}

impl IntentPool {
    /// Create a new intent pool.
    pub fn new(
        our_commitment: CommitmentId,
        config: IntentPoolConfig,
        auto_fulfill: AutoFulfillPolicy,
    ) -> Self {
        Self {
            intents: HashMap::new(),
            held_tokens: Vec::new(),
            our_commitment,
            config,
            auto_fulfill,
            pending_matches: Vec::new(),
            our_intent_ids: Vec::new(),
            recent_by_creator: HashMap::new(),
            pending_commitments: HashMap::new(),
        }
    }

    /// Update the wallet's held capabilities (call when tokens change).
    pub fn update_held_tokens(&mut self, tokens: Vec<HeldCapability>) {
        self.held_tokens = tokens;
    }

    /// Broadcast a new intent from this wallet.
    ///
    /// Returns the intent (with computed ID) ready for gossip propagation.
    pub fn broadcast_intent(
        &mut self,
        kind: IntentKind,
        matcher: MatchSpec,
        expiry: u64,
        proof_of_stake: Option<pyana_cell::NoteCommitment>,
    ) -> Intent {
        let intent = Intent::new(kind, matcher, self.our_commitment, expiry, proof_of_stake);
        self.our_intent_ids.push(intent.id);
        self.intents.insert(intent.id, intent.clone());
        intent
    }

    /// Receive an intent from the gossip network.
    ///
    /// Adds it to the pool and (if auto_match is enabled) triggers local matching.
    /// Returns any match found.
    ///
    /// This is the hardened entry point that enforces:
    /// - Stake requirement (gossip intents must have valid stake)
    /// - Size validation (reject oversized intents)
    /// - Rate limiting (per-creator flood protection)
    pub fn receive_intent(&mut self, intent: Intent, now: u64) -> Option<Match> {
        self.receive_intent_checked(intent, now, true).ok().flatten()
    }

    /// Receive an intent with full error reporting.
    ///
    /// `require_stake`: true for gossip-received intents, false for local (own-page) intents.
    pub fn receive_intent_checked(
        &mut self,
        intent: Intent,
        now: u64,
        require_stake: bool,
    ) -> Result<Option<Match>, ReceiveError> {
        // Don't process expired intents
        if intent.is_expired(now) {
            return Err(ReceiveError::Expired);
        }

        // Don't match our own intents
        if self.our_intent_ids.contains(&intent.id) {
            return Err(ReceiveError::OwnIntent);
        }

        // Don't process duplicates
        if self.intents.contains_key(&intent.id) {
            return Err(ReceiveError::Duplicate);
        }

        // --- HARDENING: Validate intent fields (Fix 2) ---
        validation::validate_intent(&intent).map_err(ReceiveError::Invalid)?;

        // --- HARDENING: Require valid stake for gossip (Fix 1) ---
        if require_stake && !crate::verify_stake(&intent) {
            return Err(ReceiveError::MissingStake);
        }

        // --- HARDENING: Rate limiting per creator (Fix 6) ---
        if let Err(e) = self.check_rate_limit(&intent.creator, now) {
            return Err(e);
        }

        // Enforce pool size limit (drop oldest if full)
        if self.intents.len() >= self.config.max_intents {
            self.gc(now);
            // If still full after GC, drop the oldest
            if self.intents.len() >= self.config.max_intents {
                if let Some(oldest_id) = self.find_oldest_intent() {
                    self.intents.remove(&oldest_id);
                }
            }
        }

        // Store the intent
        self.intents.insert(intent.id, intent.clone());

        // Record for rate limiting
        self.record_intent_from_creator(&intent.creator, now);

        // Auto-match if enabled
        if self.config.auto_match {
            let result = match_intent(
                &intent,
                &self.held_tokens,
                self.our_commitment,
                crate::VerificationMode::Trusted,
                now,
            );

            if let MatchResult::Matched { matched, .. } = result {
                // Check auto-fulfill policy
                if self.should_auto_fulfill(&intent) {
                    return Ok(Some(matched));
                } else {
                    // Store as pending for user approval
                    self.pending_matches.push((intent, matched.clone()));
                    return Ok(Some(matched));
                }
            }
        }

        Ok(None)
    }

    /// Receive a local intent (from the wallet's own page) without stake requirement.
    ///
    /// Local intents skip the stake check but still undergo validation and rate limiting.
    pub fn receive_local_intent(&mut self, intent: Intent, now: u64) -> Result<Option<Match>, ReceiveError> {
        self.receive_intent_checked(intent, now, false)
    }

    /// Run garbage collection: remove expired intents.
    pub fn gc(&mut self, now: u64) {
        self.intents.retain(|_, intent| !intent.is_expired(now));
    }

    /// Get all active (non-expired) intents in the pool.
    pub fn active_intents(&self, now: u64) -> Vec<&Intent> {
        self.intents
            .values()
            .filter(|i| !i.is_expired(now))
            .collect()
    }

    /// Get the number of intents in the pool.
    pub fn len(&self) -> usize {
        self.intents.len()
    }

    /// Check if the pool is empty.
    pub fn is_empty(&self) -> bool {
        self.intents.is_empty()
    }

    /// Get pending matches waiting for user approval.
    pub fn pending_matches(&self) -> &[(Intent, Match)] {
        &self.pending_matches
    }

    /// Approve a pending match (remove from pending, return for fulfillment).
    pub fn approve_match(&mut self, intent_id: &[u8; 32]) -> Option<(Intent, Match)> {
        if let Some(idx) = self
            .pending_matches
            .iter()
            .position(|(i, _)| &i.id == intent_id)
        {
            Some(self.pending_matches.remove(idx))
        } else {
            None
        }
    }

    /// Reject a pending match.
    pub fn reject_match(&mut self, intent_id: &[u8; 32]) {
        self.pending_matches.retain(|(i, _)| &i.id != intent_id);
    }

    /// Get a specific intent by ID.
    pub fn get_intent(&self, id: &[u8; 32]) -> Option<&Intent> {
        self.intents.get(id)
    }

    /// Re-evaluate all pool intents against current held tokens.
    ///
    /// Useful after wallet state changes (new tokens provisioned, etc.)
    pub fn rematch_all(&mut self, now: u64) -> Vec<Match> {
        let mut matches = Vec::new();
        let intent_ids: Vec<[u8; 32]> = self.intents.keys().copied().collect();

        for id in intent_ids {
            if self.our_intent_ids.contains(&id) {
                continue;
            }
            if let Some(intent) = self.intents.get(&id) {
                let result = match_intent(
                    intent,
                    &self.held_tokens,
                    self.our_commitment,
                    crate::VerificationMode::Trusted,
                    now,
                );
                if let MatchResult::Matched { matched, .. } = result {
                    matches.push(matched);
                }
            }
        }

        matches
    }

    // -----------------------------------------------------------------------
    // Commit-Reveal Protocol (Fix 3: anti-frontrunning)
    // -----------------------------------------------------------------------

    /// Phase 1: Commit to fulfilling an intent.
    ///
    /// Creates a blinded commitment that hides which fulfillment will be revealed.
    /// The commitment is stored locally and should be broadcast to the network.
    /// First valid commitment wins priority.
    pub fn commit_to_fulfill(
        &mut self,
        intent_id: [u8; 32],
        fulfillment: &Fulfillment,
        now: u64,
    ) -> FulfillmentCommitment {
        // Generate random nonce
        let mut nonce = [0u8; 32];
        crate::getrandom(&mut nonce);

        // Compute blinded commitment: BLAKE3(serialized_fulfillment || nonce)
        let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-commit-v1");
        hasher.update(&intent_id);
        hasher.update(&fulfillment.fulfiller.0);
        for action in &fulfillment.granted_actions {
            hasher.update(action.as_bytes());
        }
        hasher.update(fulfillment.granted_resource.as_bytes());
        hasher.update(&nonce);
        let satisfier_commitment = *hasher.finalize().as_bytes();

        let commitment = FulfillmentCommitment {
            intent_id,
            satisfier_commitment,
            timestamp: now,
        };

        // Store the pending commitment (keyed by commitment hash for reveal lookup)
        let commitment_key = Self::hash_commitment(&commitment);
        self.pending_commitments.insert(commitment_key, commitment.clone());

        commitment
    }

    /// Phase 2: Reveal a previously committed fulfillment.
    ///
    /// The reveal must match a stored commitment. The nonce proves this reveal
    /// corresponds to the earlier blinded commitment.
    ///
    /// Returns `Ok(())` if the reveal is valid, `Err` if:
    /// - No matching commitment exists
    /// - The reveal window hasn't opened yet
    /// - The nonce doesn't match the commitment
    pub fn reveal_fulfillment(
        &mut self,
        reveal: &FulfillmentReveal,
        now: u64,
    ) -> Result<(), CommitRevealError> {
        // Look up the commitment
        let commitment = self
            .pending_commitments
            .get(&reveal.commitment_hash)
            .ok_or(CommitRevealError::NoCommitment)?;

        // Check that the reveal window has elapsed
        let elapsed = now.saturating_sub(commitment.timestamp);
        if elapsed < COMMIT_REVEAL_WINDOW_SECS {
            return Err(CommitRevealError::TooEarly {
                remaining: COMMIT_REVEAL_WINDOW_SECS - elapsed,
            });
        }

        // Verify the nonce matches the commitment
        let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-commit-v1");
        hasher.update(&commitment.intent_id);
        hasher.update(&reveal.fulfillment.fulfiller.0);
        for action in &reveal.fulfillment.granted_actions {
            hasher.update(action.as_bytes());
        }
        hasher.update(reveal.fulfillment.granted_resource.as_bytes());
        hasher.update(&reveal.nonce);
        let recomputed = *hasher.finalize().as_bytes();

        if recomputed != commitment.satisfier_commitment {
            return Err(CommitRevealError::NonceMismatch);
        }

        // Remove the commitment (fulfilled)
        self.pending_commitments.remove(&reveal.commitment_hash);

        Ok(())
    }

    /// Check if there's already a commitment for the given intent.
    pub fn has_commitment_for(&self, intent_id: &[u8; 32]) -> bool {
        self.pending_commitments
            .values()
            .any(|c| &c.intent_id == intent_id)
    }

    /// Get the pending commitment count.
    pub fn pending_commitment_count(&self) -> usize {
        self.pending_commitments.len()
    }

    /// Compute the hash of a FulfillmentCommitment (used as its key).
    fn hash_commitment(commitment: &FulfillmentCommitment) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-commitment-key-v1");
        hasher.update(&commitment.intent_id);
        hasher.update(&commitment.satisfier_commitment);
        hasher.update(&commitment.timestamp.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    // -----------------------------------------------------------------------
    // Rate limiting (Fix 6)
    // -----------------------------------------------------------------------

    /// Check if a creator is within their rate limit.
    fn check_rate_limit(&self, creator: &CommitmentId, now: u64) -> Result<(), ReceiveError> {
        if let Some(&(window_start, count)) = self.recent_by_creator.get(creator) {
            // Check if we're still in the same window
            if now.saturating_sub(window_start) < RATE_LIMIT_WINDOW_SECS {
                if count >= MAX_INTENTS_PER_CREATOR_PER_MINUTE {
                    return Err(ReceiveError::RateLimited {
                        creator: *creator,
                        count,
                        max: MAX_INTENTS_PER_CREATOR_PER_MINUTE,
                    });
                }
            }
        }
        Ok(())
    }

    /// Record an intent from a creator for rate-limiting purposes.
    fn record_intent_from_creator(&mut self, creator: &CommitmentId, now: u64) {
        let entry = self.recent_by_creator.entry(*creator).or_insert((now, 0));
        // Reset window if it's expired
        if now.saturating_sub(entry.0) >= RATE_LIMIT_WINDOW_SECS {
            *entry = (now, 1);
        } else {
            entry.1 += 1;
        }
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    /// Check if a match should be auto-fulfilled based on policy.
    fn should_auto_fulfill(&self, intent: &Intent) -> bool {
        match &self.auto_fulfill {
            AutoFulfillPolicy::Never => false,
            AutoFulfillPolicy::Always => true,
            AutoFulfillPolicy::ForPatterns(patterns) => {
                if let Some(ref resource_pattern) = intent.matcher.resource_pattern {
                    patterns.iter().any(|p| {
                        globset::Glob::new(p)
                            .map(|g| g.compile_matcher().is_match(resource_pattern))
                            .unwrap_or(false)
                    })
                } else {
                    false
                }
            }
        }
    }

    /// Find the oldest intent by expiry (for eviction).
    fn find_oldest_intent(&self) -> Option<[u8; 32]> {
        self.intents
            .iter()
            .min_by_key(|(_, i)| i.expiry)
            .map(|(id, _)| *id)
    }
}

/// Errors from the commit-reveal protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommitRevealError {
    /// No commitment found for this reveal.
    NoCommitment,
    /// The reveal window hasn't elapsed yet.
    TooEarly { remaining: u64 },
    /// The nonce in the reveal doesn't match the commitment.
    NonceMismatch,
}

impl std::fmt::Display for CommitRevealError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoCommitment => write!(f, "no matching commitment found"),
            Self::TooEarly { remaining } => {
                write!(f, "reveal too early, {remaining}s remaining in window")
            }
            Self::NonceMismatch => write!(f, "nonce does not match commitment"),
        }
    }
}

impl std::error::Error for CommitRevealError {}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec};
    use crate::matcher::Sensitivity;

    /// A valid (non-zero) stake commitment for testing gossip-received intents.
    fn valid_stake() -> Option<pyana_cell::NoteCommitment> {
        Some(pyana_cell::NoteCommitment([0xDE; 32]))
    }

    fn test_pool() -> IntentPool {
        IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: true,
            },
            AutoFulfillPolicy::Always,
        )
    }

    fn test_token(actions: &[&str], resource: &str) -> HeldCapability {
        HeldCapability {
            token_id: "tok_1".into(),
            actions: actions.iter().map(|s| s.to_string()).collect(),
            resource: resource.into(),
            app_id: None,
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: None,
            budget: None,
            sensitivity: Sensitivity::Normal,
        }
    }

    #[test]
    fn test_broadcast_adds_to_pool() {
        let mut pool = test_pool();
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = pool.broadcast_intent(IntentKind::Need, spec, 9999, None);
        assert_eq!(pool.len(), 1);
        assert!(pool.get_intent(&intent.id).is_some());
    }

    #[test]
    fn test_receive_triggers_matching() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read", "write"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]), // different creator
            9999,
            valid_stake(),
        );

        let result = pool.receive_intent(intent, 100);
        assert!(result.is_some());
    }

    #[test]
    fn test_own_intents_not_matched() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = pool.broadcast_intent(IntentKind::Need, spec, 9999, valid_stake());

        // Now "receive" it as if from gossip -- should be ignored
        let result = pool.receive_intent(intent, 100);
        assert!(result.is_none());
    }

    #[test]
    fn test_expired_intent_rejected() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x33; 32]),
            50, // expires at t=50
            valid_stake(),
        );

        let result = pool.receive_intent(intent, 100); // now=100, expired
        assert!(result.is_none());
    }

    #[test]
    fn test_gc_removes_expired() {
        let mut pool = test_pool();

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };

        // Add intent that expires at t=200
        let intent = Intent::new(
            IntentKind::Need,
            spec.clone(),
            CommitmentId([0x44; 32]),
            200,
            None,
        );
        pool.intents.insert(intent.id, intent);

        // Add intent that expires at t=500
        let intent2 = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x55; 32]),
            500,
            None,
        );
        pool.intents.insert(intent2.id, intent2);

        assert_eq!(pool.len(), 2);
        pool.gc(300); // t=300: first expired, second still valid
        assert_eq!(pool.len(), 1);
    }

    #[test]
    fn test_duplicate_intent_ignored() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x66; 32]),
            9999,
            valid_stake(),
        );

        let r1 = pool.receive_intent(intent.clone(), 100);
        assert!(r1.is_some());

        // Receiving same intent again should return None (duplicate)
        let r2 = pool.receive_intent(intent, 100);
        assert!(r2.is_none());
    }

    #[test]
    fn test_rematch_all() {
        let mut pool = test_pool();
        // Initially no tokens
        pool.update_held_tokens(vec![]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x77; 32]),
            9999,
            None,
        );
        pool.intents.insert(intent.id, intent);

        // No matches yet (no tokens)
        let matches = pool.rematch_all(100);
        assert!(matches.is_empty());

        // Now add a token
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        // Rematch should find it
        let matches = pool.rematch_all(100);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn test_pool_size_limit() {
        let mut pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 3,
                gc_interval_secs: 60,
                auto_match: false,
            },
            AutoFulfillPolicy::Never,
        );

        for i in 0..5u8 {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([i + 0x80; 32]),
                (1000 + i as u64) * 10,
                valid_stake(),
            );
            pool.receive_intent(intent, 100);
        }

        // Pool should not exceed max_intents
        assert!(pool.len() <= 3);
    }

    #[test]
    fn test_active_intents_filters_expired() {
        let mut pool = test_pool();

        let spec1 = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let i1 = Intent::new(IntentKind::Need, spec1.clone(), CommitmentId([0xA0; 32]), 200, None);
        let i2 = Intent::new(IntentKind::Need, spec1, CommitmentId([0xB0; 32]), 500, None);

        pool.intents.insert(i1.id, i1);
        pool.intents.insert(i2.id, i2);

        let active = pool.active_intents(300);
        assert_eq!(active.len(), 1);
    }

    // -----------------------------------------------------------------------
    // New hardening tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_gossip_rejects_intent_without_stake() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        // Intent with no stake
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
            9999,
            None,
        );

        // Gossip path (require_stake=true) should reject
        let result = pool.receive_intent_checked(intent.clone(), 100, true);
        assert_eq!(result, Err(ReceiveError::MissingStake));

        // Local path (require_stake=false) should accept
        let result = pool.receive_local_intent(intent, 100);
        assert!(result.is_ok());
    }

    #[test]
    fn test_gossip_rejects_zero_stake() {
        let mut pool = test_pool();

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        // Intent with all-zero commitment (invalid)
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
            9999,
            Some(pyana_cell::NoteCommitment([0u8; 32])),
        );

        let result = pool.receive_intent_checked(intent, 100, true);
        assert_eq!(result, Err(ReceiveError::MissingStake));
    }

    #[test]
    fn test_rate_limiting() {
        let mut pool = test_pool();
        let creator = CommitmentId([0x99; 32]);

        // Post MAX_INTENTS_PER_CREATOR_PER_MINUTE intents (should all succeed)
        for i in 0..MAX_INTENTS_PER_CREATOR_PER_MINUTE {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                creator,
                9999,
                valid_stake(),
            );
            let result = pool.receive_intent_checked(intent, 100, true);
            assert!(result.is_ok(), "intent {i} should succeed");
        }

        // The next one should be rate-limited
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("action_overflow".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
        let result = pool.receive_intent_checked(intent, 100, true);
        assert!(matches!(result, Err(ReceiveError::RateLimited { .. })));
    }

    #[test]
    fn test_rate_limit_resets_after_window() {
        let mut pool = test_pool();
        let creator = CommitmentId([0xAA; 32]);

        // Fill up the rate limit at t=100
        for i in 0..MAX_INTENTS_PER_CREATOR_PER_MINUTE {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("a_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
            };
            let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
            pool.receive_intent_checked(intent, 100, true).unwrap();
        }

        // After the window expires (t=161), should be able to post again
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("new_window".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
        let result = pool.receive_intent_checked(intent, 161, true);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validation_rejects_oversized_intent() {
        let mut pool = test_pool();

        // Create intent with too many actions
        let actions: Vec<ActionPattern> = (0..65)
            .map(|i| ActionPattern {
                action: Some(format!("act_{i}")),
                resource: None,
            })
            .collect();
        let spec = MatchSpec {
            actions,
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x22; 32]), 9999, valid_stake());
        let result = pool.receive_intent_checked(intent, 100, true);
        assert!(matches!(result, Err(ReceiveError::Invalid(_))));
    }

    #[test]
    fn test_commit_reveal_happy_path() {
        let mut pool = test_pool();

        let fulfillment = crate::fulfillment::Fulfillment {
            intent_id: [0x01; 32],
            matched: crate::Match {
                intent_id: [0x01; 32],
                satisfier: CommitmentId([0xBB; 32]),
                proof: None,
                mode: crate::VerificationMode::Trusted,
            },
            token_data: None,
            granted_actions: vec!["read".into()],
            granted_resource: "docs/*".into(),
            expiry: Some(5000),
            fulfiller: CommitmentId([0xBB; 32]),
        };

        // Phase 1: Commit
        let commitment = pool.commit_to_fulfill([0x01; 32], &fulfillment, 100);
        assert!(pool.has_commitment_for(&[0x01; 32]));
        assert_eq!(pool.pending_commitment_count(), 1);

        // Phase 2: Reveal (too early -- should fail)
        let commitment_hash = IntentPool::hash_commitment(&commitment);
        let reveal = FulfillmentReveal {
            commitment_hash,
            fulfillment: fulfillment.clone(),
            nonce: [0xFF; 32], // wrong nonce
        };
        let result = pool.reveal_fulfillment(&reveal, 102); // only 2 seconds elapsed
        assert_eq!(result, Err(CommitRevealError::TooEarly { remaining: 3 }));

        // Phase 2: Reveal (wrong nonce -- should fail even after window)
        let result = pool.reveal_fulfillment(&reveal, 106);
        assert_eq!(result, Err(CommitRevealError::NonceMismatch));

        // The commitment is still pending (wrong nonce doesn't consume it)
        assert_eq!(pool.pending_commitment_count(), 1);
    }

    #[test]
    fn test_commit_reveal_no_commitment() {
        let mut pool = test_pool();

        let fulfillment = crate::fulfillment::Fulfillment {
            intent_id: [0x01; 32],
            matched: crate::Match {
                intent_id: [0x01; 32],
                satisfier: CommitmentId([0xBB; 32]),
                proof: None,
                mode: crate::VerificationMode::Trusted,
            },
            token_data: None,
            granted_actions: vec!["read".into()],
            granted_resource: "docs/*".into(),
            expiry: Some(5000),
            fulfiller: CommitmentId([0xBB; 32]),
        };

        let reveal = FulfillmentReveal {
            commitment_hash: [0xFF; 32], // no such commitment
            fulfillment,
            nonce: [0x00; 32],
        };

        let result = pool.reveal_fulfillment(&reveal, 200);
        assert_eq!(result, Err(CommitRevealError::NoCommitment));
    }
}
