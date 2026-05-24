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
//! - Global rate limiting prevents Sybil floods
//! - Epoch-scoped nullifiers limit stake to K uses per epoch (anti-Sybil)
//! - Commit-reveal protocol prevents fulfillment frontrunning

use std::collections::{HashMap, HashSet};

use pyana_circuit::field::BabyBear;

use crate::fulfillment::Fulfillment;
use crate::matcher::{HeldCapability, MatchResult, match_intent};
use crate::validation::{self, ValidationError};
use crate::{
    CommitmentId, Intent, IntentKind, MAX_STAKE_USES_PER_EPOCH, Match, MatchSpec, StakeProof,
    compute_stake_nullifier, current_epoch,
};

/// Maximum intents allowed per creator per minute.
pub const MAX_INTENTS_PER_CREATOR_PER_MINUTE: usize = 10;

/// Global maximum intents allowed per time window (prevents Sybil floods).
pub const MAX_GLOBAL_INTENTS_PER_WINDOW: usize = 500;

/// Rate limiting window duration in seconds.
pub const RATE_LIMIT_WINDOW_SECS: u64 = 60;

/// Maximum age (in seconds) for pending commitments before GC reclaims them.
pub const MAX_COMMITMENT_AGE_SECS: u64 = 300;

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
    /// The intent lacks a valid stake proof (required for gossip).
    MissingStake,
    /// The stake proof failed Merkle verification against the known note tree root.
    InvalidStakeProof,
    /// The stake has exhausted all K uses in this epoch (epoch-scoped nullifier).
    StakeAlreadyUsed,
    /// The creator has exceeded the rate limit.
    RateLimited {
        creator: CommitmentId,
        count: usize,
        max: usize,
    },
    /// The global rate limit has been exceeded (Sybil flood protection).
    GlobalRateLimited { count: usize, max: usize },
    /// The intent has already been fulfilled.
    AlreadyFulfilled,
}

impl std::fmt::Display for ReceiveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expired => write!(f, "intent has expired"),
            Self::Duplicate => write!(f, "intent is a duplicate"),
            Self::OwnIntent => write!(f, "intent is from this wallet"),
            Self::Invalid(e) => write!(f, "validation error: {e}"),
            Self::MissingStake => write!(f, "intent lacks stake proof for gossip"),
            Self::InvalidStakeProof => {
                write!(
                    f,
                    "stake proof failed Merkle verification against known root"
                )
            }
            Self::StakeAlreadyUsed => {
                write!(
                    f,
                    "stake exhausted: all {} uses consumed in this epoch",
                    crate::MAX_STAKE_USES_PER_EPOCH
                )
            }
            Self::RateLimited {
                creator,
                count,
                max,
            } => {
                write!(
                    f,
                    "creator {:?} rate limited: {count} intents exceeds max {max}",
                    &creator.0[..4]
                )
            }
            Self::GlobalRateLimited { count, max } => {
                write!(
                    f,
                    "global rate limit exceeded: {count} intents exceeds max {max}"
                )
            }
            Self::AlreadyFulfilled => write!(f, "intent has already been fulfilled"),
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
    /// Claimed minimum stake value (informational only).
    ///
    /// NOTE: This value CANNOT be trusted for access control because the staker
    /// can claim any value without opening the commitment. The Merkle proof only
    /// proves the note EXISTS in the tree, not its value. This field is retained
    /// for informational/display purposes only.
    pub minimum_stake_value: u64,
}

impl Default for IntentPoolConfig {
    fn default() -> Self {
        Self {
            max_intents: 10_000,
            gc_interval_secs: 60,
            auto_match: true,
            minimum_stake_value: 0,
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

/// Stored intent with arrival metadata.
#[derive(Clone, Debug)]
struct StoredIntent {
    /// The intent itself.
    intent: Intent,
    /// When this intent arrived in the pool (Unix seconds).
    arrived_at: u64,
}

/// The local pool of known intents (like a mempool for capabilities).
///
/// Stores active intents, performs garbage collection on expired ones,
/// and triggers local matching when new intents arrive.
pub struct IntentPool {
    /// Active intents indexed by their content-addressed ID.
    intents: HashMap<[u8; 32], StoredIntent>,
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
    /// Global rate limiting: (window_start, count).
    global_rate: (u64, usize),
    /// Pending fulfillment commitments (commit-reveal anti-frontrunning).
    pending_commitments: HashMap<[u8; 32], FulfillmentCommitment>,
    /// The latest attested Poseidon2 note tree root from the federation.
    /// Stake proofs are verified against this root.
    known_note_root: BabyBear,
    /// Epoch-scoped nullifier set: maps stake nullifiers to used status.
    ///
    /// Each note commitment gets `MAX_STAKE_USES_PER_EPOCH` uses per epoch.
    /// The nullifier is `Poseidon2(commitment, epoch, counter)` for counter in [0, K-1].
    /// Different epochs produce different nullifiers (unlinkable for privacy).
    used_stake_nullifiers: HashSet<[u8; 32]>,
    /// The current block height, used to determine epoch for nullifier computation.
    current_block_height: u64,
    /// Map of intent IDs that have been fulfilled to the block height at fulfillment time.
    /// Used for replay protection with bounded retention (GC prunes old entries).
    fulfilled_intents: HashMap<[u8; 32], u64>,
}

/// Number of blocks to retain fulfilled intent entries before GC can prune them.
/// After this many blocks, the fulfilled entry is considered stale and can be removed.
pub const FULFILLED_RETENTION_BLOCKS: u64 = 10_000;

impl IntentPool {
    /// Create a new intent pool.
    ///
    /// `known_note_root`: the latest attested Poseidon2 note tree root from the
    /// federation. Incoming gossip intents' stake proofs are verified against this root.
    pub fn new(
        our_commitment: CommitmentId,
        config: IntentPoolConfig,
        auto_fulfill: AutoFulfillPolicy,
        known_note_root: BabyBear,
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
            global_rate: (0, 0),
            pending_commitments: HashMap::new(),
            known_note_root,
            used_stake_nullifiers: HashSet::new(),
            current_block_height: 0,
            fulfilled_intents: HashMap::new(),
        }
    }

    /// Update the known note tree root (when the federation attests a new root).
    pub fn update_known_note_root(&mut self, root: BabyBear) {
        self.known_note_root = root;
    }

    /// Get the current known note tree root.
    pub fn known_note_root(&self) -> BabyBear {
        self.known_note_root
    }

    /// Update the current block height.
    ///
    /// When the epoch advances (block_height crosses an epoch boundary), old nullifiers
    /// from previous epochs are automatically pruned since they are no longer relevant.
    pub fn update_block_height(&mut self, block_height: u64) {
        let old_epoch = current_epoch(self.current_block_height);
        let new_epoch = current_epoch(block_height);
        self.current_block_height = block_height;

        // When epoch advances, clear all nullifiers (they are epoch-scoped)
        if new_epoch > old_epoch {
            self.used_stake_nullifiers.clear();
        }
    }

    /// Get the current block height.
    pub fn current_block_height(&self) -> u64 {
        self.current_block_height
    }

    /// Get the current epoch.
    pub fn current_epoch(&self) -> u64 {
        current_epoch(self.current_block_height)
    }

    /// Update the wallet's held capabilities (call when tokens change).
    pub fn update_held_tokens(&mut self, tokens: Vec<HeldCapability>) {
        self.held_tokens = tokens;
    }

    /// Broadcast a new intent from this wallet.
    ///
    /// Returns the intent (with computed ID) ready for gossip propagation, or an error
    /// if the intent fails validation.
    /// `stake_proof`: a valid stake proof for gossip propagation (or None for local-only).
    pub fn broadcast_intent(
        &mut self,
        kind: IntentKind,
        matcher: MatchSpec,
        expiry: u64,
        stake_proof: Option<StakeProof>,
    ) -> Result<Intent, ReceiveError> {
        let intent = Intent::new(kind, matcher, self.our_commitment, expiry, stake_proof);

        // Validate self-submitted intents too (issue #11)
        validation::validate_intent(&intent).map_err(ReceiveError::Invalid)?;

        self.our_intent_ids.push(intent.id);
        self.intents.insert(
            intent.id,
            StoredIntent {
                intent: intent.clone(),
                arrived_at: 0, // own intents use time 0
            },
        );
        Ok(intent)
    }

    /// Receive an intent from the gossip network.
    ///
    /// Adds it to the pool and (if auto_match is enabled) triggers local matching.
    /// Returns any match found.
    ///
    /// This is the hardened entry point that enforces:
    /// - Stake requirement (gossip intents must have valid stake)
    /// - Size validation (reject oversized intents)
    /// - Rate limiting (per-creator and global flood protection)
    /// - Nullifier tracking (no stake reuse)
    pub fn receive_intent(&mut self, intent: Intent, now: u64) -> Option<Match> {
        self.receive_intent_checked(intent, now, true)
            .ok()
            .flatten()
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

        // Don't accept intents that have already been fulfilled (replay protection, issue #13)
        if self.fulfilled_intents.contains_key(&intent.id) {
            return Err(ReceiveError::AlreadyFulfilled);
        }

        // --- HARDENING: Validate intent fields ---
        validation::validate_intent(&intent).map_err(ReceiveError::Invalid)?;

        // --- HARDENING: Require valid stake proof for gossip ---
        if require_stake {
            match &intent.stake_proof {
                None => return Err(ReceiveError::MissingStake),
                Some(stake_proof) => {
                    // Verify the Merkle proof against the known note tree root
                    if !crate::verify_stake(stake_proof, self.known_note_root) {
                        return Err(ReceiveError::InvalidStakeProof);
                    }
                    // Epoch-scoped nullifier check: each note gets K uses per epoch.
                    // Try counter 0..K-1 -- if ALL nullifiers for this epoch are used, reject.
                    let epoch = current_epoch(self.current_block_height);
                    let all_used = (0..MAX_STAKE_USES_PER_EPOCH).all(|counter| {
                        let nullifier =
                            compute_stake_nullifier(&stake_proof.commitment.0, epoch, counter);
                        self.used_stake_nullifiers.contains(&nullifier)
                    });
                    if all_used {
                        return Err(ReceiveError::StakeAlreadyUsed);
                    }
                    // NOTE (issue #2): stake_proof.minimum_value is NOT checked for
                    // policy enforcement. The value cannot be verified without opening
                    // the commitment, so using it for access control is security theater.
                    // It is retained for informational/display purposes only.
                }
            }
        }

        // --- HARDENING: Global rate limit (issue #4) ---
        if let Err(e) = self.check_global_rate_limit(now) {
            return Err(e);
        }

        // --- HARDENING: Rate limiting per creator (secondary check) ---
        if let Err(e) = self.check_rate_limit(&intent.creator, now) {
            return Err(e);
        }

        // Enforce pool size limit (evict by arrival time, oldest first, issue #9)
        if self.intents.len() >= self.config.max_intents {
            self.gc(now);
            // If still full after GC, drop the oldest by arrival time
            if self.intents.len() >= self.config.max_intents {
                if let Some(oldest_id) = self.find_oldest_by_arrival() {
                    self.intents.remove(&oldest_id);
                }
            }
        }

        // Record stake nullifier for the next available counter in this epoch
        if let Some(stake_proof) = &intent.stake_proof {
            let epoch = current_epoch(self.current_block_height);
            // Find the first unused counter and insert its nullifier
            for counter in 0..MAX_STAKE_USES_PER_EPOCH {
                let nullifier = compute_stake_nullifier(&stake_proof.commitment.0, epoch, counter);
                if !self.used_stake_nullifiers.contains(&nullifier) {
                    self.used_stake_nullifiers.insert(nullifier);
                    break;
                }
            }
        }

        // Store the intent with arrival time
        self.intents.insert(
            intent.id,
            StoredIntent {
                intent: intent.clone(),
                arrived_at: now,
            },
        );

        // Record for rate limiting
        self.record_intent_from_creator(&intent.creator, now);
        self.record_global_intent(now);

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
    pub fn receive_local_intent(
        &mut self,
        intent: Intent,
        now: u64,
    ) -> Result<Option<Match>, ReceiveError> {
        self.receive_intent_checked(intent, now, false)
    }

    /// Mark an intent as fulfilled. Subsequent attempts to re-submit or re-fulfill
    /// this intent will be rejected with `AlreadyFulfilled`.
    pub fn mark_fulfilled(&mut self, intent_id: [u8; 32]) {
        self.fulfilled_intents
            .insert(intent_id, self.current_block_height);
        // Remove from active pool
        self.intents.remove(&intent_id);
    }

    /// Run garbage collection: remove expired intents and clean auxiliary structures.
    pub fn gc(&mut self, now: u64) {
        self.intents
            .retain(|_, stored| !stored.intent.is_expired(now));

        // Clean our_intent_ids: remove IDs no longer in the pool
        self.our_intent_ids
            .retain(|id| self.intents.contains_key(id));

        // Clean pending_matches: remove matches whose intent has been GC'd
        self.pending_matches
            .retain(|(intent, _)| self.intents.contains_key(&intent.id));

        // Clean recent_by_creator: remove entries whose window has expired
        self.recent_by_creator.retain(|_, (window_start, _)| {
            now.saturating_sub(*window_start) < RATE_LIMIT_WINDOW_SECS
        });

        // Clean pending_commitments: remove commitments older than max age
        self.pending_commitments.retain(|_, commitment| {
            now.saturating_sub(commitment.timestamp) < MAX_COMMITMENT_AGE_SECS
        });

        // SECURITY: Prune fulfilled_intents entries older than retention period.
        // Without this, the fulfilled set grows unboundedly (memory leak / DoS vector).
        let current_height = self.current_block_height;
        self.fulfilled_intents.retain(|_, fulfillment_height| {
            current_height.saturating_sub(*fulfillment_height) <= FULFILLED_RETENTION_BLOCKS
        });
    }

    /// Get all active (non-expired) intents in the pool.
    pub fn active_intents(&self, now: u64) -> Vec<&Intent> {
        self.intents
            .values()
            .filter(|s| !s.intent.is_expired(now))
            .map(|s| &s.intent)
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
        self.intents.get(id).map(|s| &s.intent)
    }

    /// Re-evaluate all pool intents against current held tokens.
    pub fn rematch_all(&mut self, now: u64) -> Vec<Match> {
        let mut matches = Vec::new();
        let intent_ids: Vec<[u8; 32]> = self.intents.keys().copied().collect();

        for id in intent_ids {
            if self.our_intent_ids.contains(&id) {
                continue;
            }
            if let Some(stored) = self.intents.get(&id) {
                let result = match_intent(
                    &stored.intent,
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
    // Commit-Reveal Protocol (anti-frontrunning)
    // -----------------------------------------------------------------------

    /// Phase 1: Commit to fulfilling an intent.
    pub fn commit_to_fulfill(
        &mut self,
        intent_id: [u8; 32],
        fulfillment: &Fulfillment,
        now: u64,
    ) -> FulfillmentCommitment {
        let mut nonce = [0u8; 32];
        crate::getrandom(&mut nonce);

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

        let commitment_key = Self::hash_commitment(&commitment);
        self.pending_commitments
            .insert(commitment_key, commitment.clone());

        commitment
    }

    /// Phase 2: Reveal a previously committed fulfillment.
    pub fn reveal_fulfillment(
        &mut self,
        reveal: &FulfillmentReveal,
        now: u64,
    ) -> Result<(), CommitRevealError> {
        let commitment = self
            .pending_commitments
            .get(&reveal.commitment_hash)
            .ok_or(CommitRevealError::NoCommitment)?;

        let elapsed = now.saturating_sub(commitment.timestamp);
        if elapsed < COMMIT_REVEAL_WINDOW_SECS {
            return Err(CommitRevealError::TooEarly {
                remaining: COMMIT_REVEAL_WINDOW_SECS - elapsed,
            });
        }

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

        let intent_id = commitment.intent_id;
        self.pending_commitments.remove(&reveal.commitment_hash);

        // Mark the intent as fulfilled (replay protection, issue #13)
        self.mark_fulfilled(intent_id);

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
    // Rate limiting
    // -----------------------------------------------------------------------

    fn check_rate_limit(&self, creator: &CommitmentId, now: u64) -> Result<(), ReceiveError> {
        if let Some(&(window_start, count)) = self.recent_by_creator.get(creator) {
            if now.saturating_sub(window_start) < RATE_LIMIT_WINDOW_SECS
                && count >= MAX_INTENTS_PER_CREATOR_PER_MINUTE
            {
                return Err(ReceiveError::RateLimited {
                    creator: *creator,
                    count,
                    max: MAX_INTENTS_PER_CREATOR_PER_MINUTE,
                });
            }
        }
        Ok(())
    }

    /// Check global rate limit (issue #4: prevents Sybil floods regardless of identity).
    fn check_global_rate_limit(&self, now: u64) -> Result<(), ReceiveError> {
        let (window_start, count) = self.global_rate;
        if now.saturating_sub(window_start) < RATE_LIMIT_WINDOW_SECS
            && count >= MAX_GLOBAL_INTENTS_PER_WINDOW
        {
            return Err(ReceiveError::GlobalRateLimited {
                count,
                max: MAX_GLOBAL_INTENTS_PER_WINDOW,
            });
        }
        Ok(())
    }

    fn record_intent_from_creator(&mut self, creator: &CommitmentId, now: u64) {
        let entry = self.recent_by_creator.entry(*creator).or_insert((now, 0));
        if now.saturating_sub(entry.0) >= RATE_LIMIT_WINDOW_SECS {
            *entry = (now, 1);
        } else {
            entry.1 += 1;
        }
    }

    fn record_global_intent(&mut self, now: u64) {
        if now.saturating_sub(self.global_rate.0) >= RATE_LIMIT_WINDOW_SECS {
            self.global_rate = (now, 1);
        } else {
            self.global_rate.1 += 1;
        }
    }

    // -----------------------------------------------------------------------
    // Private helpers
    // -----------------------------------------------------------------------

    fn should_auto_fulfill(&self, intent: &Intent) -> bool {
        match &self.auto_fulfill {
            AutoFulfillPolicy::Never => false,
            AutoFulfillPolicy::Always => true,
            AutoFulfillPolicy::ForPatterns(patterns) => {
                // Policy patterns are matched against the intent's
                // declared resource_pattern. We accept either form of
                // match: literal equality (exact pattern matching) or
                // mutual glob coverage (policy glob covers the intent's
                // pattern, or the intent's pattern as a glob covers the
                // policy entry). `matcher::resource_matches` is the
                // canonical predicate used elsewhere in the crate for
                // glob-aware comparison.
                //
                // Previously this called `Glob::new(p).is_match(intent_pattern)`,
                // which treats the intent's pattern as a LITERAL string
                // — so policy `"documents/*"` against intent
                // `"documents/*"` would fail because `*` doesn't match
                // a literal `*`. The fix treats both sides
                // glob-symmetrically.
                let intent_resource = match intent.matcher.resource_pattern.as_deref() {
                    Some(rp) => rp,
                    None => return false,
                };
                patterns.iter().any(|p| {
                    p == intent_resource
                        || crate::matcher::resource_matches(intent_resource, p)
                        || crate::matcher::resource_matches(p, intent_resource)
                })
            }
        }
    }

    /// Find the oldest intent by ARRIVAL TIME (issue #9).
    fn find_oldest_by_arrival(&self) -> Option<[u8; 32]> {
        self.intents
            .iter()
            .min_by_key(|(_, s)| s.arrived_at)
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
    use crate::matcher::Sensitivity;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec, StakeProof};
    use pyana_commit::{Poseidon2MerkleTree, commitment_to_field};

    fn build_test_tree() -> (BabyBear, StakeProof) {
        let commitment = pyana_cell::NoteCommitment([0xDE; 32]);
        let mut tree = Poseidon2MerkleTree::with_depth(4);
        for i in 0..5u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xAA;
            tree.append(commitment_to_field(&c));
        }
        let leaf = commitment_to_field(&commitment.0);
        let pos = tree.append(leaf);
        for i in 10..15u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xBB;
            tree.append(commitment_to_field(&c));
        }
        let root = tree.root();
        let merkle_proof = tree.prove_membership(pos).unwrap();
        let stake_proof = StakeProof {
            commitment,
            merkle_root: root,
            merkle_proof,
            minimum_value: 100,
        };
        (root, stake_proof)
    }

    fn valid_stake() -> Option<StakeProof> {
        let (_root, proof) = build_test_tree();
        Some(proof)
    }

    fn test_known_root() -> BabyBear {
        let (root, _proof) = build_test_tree();
        root
    }

    fn test_pool() -> IntentPool {
        IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: true,
                minimum_stake_value: 0,
            },
            AutoFulfillPolicy::Always,
            test_known_root(),
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = pool
            .broadcast_intent(IntentKind::Need, spec, 9999, None)
            .unwrap();
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = pool
            .broadcast_intent(IntentKind::Need, spec, 9999, valid_stake())
            .unwrap();
        let result = pool.receive_intent(intent, 100);
        assert!(result.is_none());
    }

    #[test]
    fn test_expired_intent_rejected() {
        let mut pool = test_pool();
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x33; 32]),
            50,
            valid_stake(),
        );
        let result = pool.receive_intent(intent, 100);
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec.clone(),
            CommitmentId([0x44; 32]),
            200,
            None,
        );
        pool.intents.insert(
            intent.id,
            StoredIntent {
                intent,
                arrived_at: 50,
            },
        );
        let intent2 = Intent::new(IntentKind::Need, spec, CommitmentId([0x55; 32]), 500, None);
        pool.intents.insert(
            intent2.id,
            StoredIntent {
                intent: intent2,
                arrived_at: 60,
            },
        );
        assert_eq!(pool.len(), 2);
        pool.gc(300);
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
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
        let r2 = pool.receive_intent(intent, 100);
        assert!(r2.is_none());
    }

    #[test]
    fn test_rematch_all() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![]);
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
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x77; 32]), 9999, None);
        pool.intents.insert(
            intent.id,
            StoredIntent {
                intent,
                arrived_at: 50,
            },
        );
        let matches = pool.rematch_all(100);
        assert!(matches.is_empty());
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);
        let matches = pool.rematch_all(100);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn test_pool_size_limit() {
        let root = test_known_root();
        let mut pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 3,
                gc_interval_secs: 60,
                auto_match: false,
                minimum_stake_value: 0,
            },
            AutoFulfillPolicy::Never,
            root,
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
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([i + 0x80; 32]),
                (1000 + i as u64) * 10,
                valid_stake(),
            );
            pool.receive_intent(intent, 100 + i as u64);
        }
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let i1 = Intent::new(
            IntentKind::Need,
            spec1.clone(),
            CommitmentId([0xA0; 32]),
            200,
            None,
        );
        let i2 = Intent::new(IntentKind::Need, spec1, CommitmentId([0xB0; 32]), 500, None);
        pool.intents.insert(
            i1.id,
            StoredIntent {
                intent: i1,
                arrived_at: 50,
            },
        );
        pool.intents.insert(
            i2.id,
            StoredIntent {
                intent: i2,
                arrived_at: 60,
            },
        );
        let active = pool.active_intents(300);
        assert_eq!(active.len(), 1);
    }

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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x22; 32]), 9999, None);
        let result = pool.receive_intent_checked(intent.clone(), 100, true);
        assert_eq!(result, Err(ReceiveError::MissingStake));
        let result = pool.receive_local_intent(intent, 100);
        assert!(result.is_ok());
    }

    #[test]
    fn test_gossip_rejects_invalid_stake_proof() {
        let mut pool = test_pool();
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let fake_commitment = pyana_cell::NoteCommitment([0xFF; 32]);
        let (_root, mut real_proof) = build_test_tree();
        real_proof.commitment = fake_commitment;
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
            9999,
            Some(real_proof),
        );
        let result = pool.receive_intent_checked(intent, 100, true);
        assert_eq!(result, Err(ReceiveError::InvalidStakeProof));
    }

    #[test]
    fn test_gossip_rejects_wrong_root() {
        let (_real_root, stake_proof) = build_test_tree();
        let wrong_root = BabyBear::new(0xBAD_CAFE);
        let mut pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: false,
                minimum_stake_value: 0,
            },
            AutoFulfillPolicy::Never,
            wrong_root,
        );
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
            9999,
            Some(stake_proof),
        );
        let result = pool.receive_intent_checked(intent, 100, true);
        assert_eq!(result, Err(ReceiveError::InvalidStakeProof));
    }

    #[test]
    fn test_stake_accepted_k_times_per_epoch() {
        let mut pool = test_pool();
        // Same stake can be used MAX_STAKE_USES_PER_EPOCH times in one epoch
        for i in 0..crate::MAX_STAKE_USES_PER_EPOCH {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([0x22 + i as u8; 32]),
                9999,
                valid_stake(),
            );
            let result = pool.receive_intent_checked(intent, 100 + i as u64, true);
            assert!(
                result.is_ok(),
                "intent {i} should succeed (K={} uses per epoch)",
                crate::MAX_STAKE_USES_PER_EPOCH
            );
        }

        // The (K+1)th use in the same epoch should be rejected
        let spec_overflow = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("overflow".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent_overflow = Intent::new(
            IntentKind::Need,
            spec_overflow,
            CommitmentId([0x99; 32]),
            9999,
            valid_stake(),
        );
        let result = pool.receive_intent_checked(intent_overflow, 110, true);
        assert_eq!(result, Err(ReceiveError::StakeAlreadyUsed));
    }

    #[test]
    fn test_stake_refreshes_in_new_epoch() {
        let mut pool = test_pool();
        // Use all K slots in epoch 0
        for i in 0..crate::MAX_STAKE_USES_PER_EPOCH {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("e0_action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([0x30 + i as u8; 32]),
                9999,
                valid_stake(),
            );
            let result = pool.receive_intent_checked(intent, 100 + i as u64, true);
            assert!(result.is_ok(), "epoch 0, use {i} should succeed");
        }

        // Advance to a new epoch (block height crosses epoch boundary)
        pool.update_block_height(crate::EPOCH_DURATION_BLOCKS);

        // Same stake should be accepted again in the new epoch
        let spec_new_epoch = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("new_epoch_action".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent_new_epoch = Intent::new(
            IntentKind::Need,
            spec_new_epoch,
            CommitmentId([0xEE; 32]),
            99999,
            valid_stake(),
        );
        let result =
            pool.receive_intent_checked(intent_new_epoch, crate::EPOCH_DURATION_BLOCKS + 1, true);
        assert!(result.is_ok(), "same stake should work in new epoch");
    }

    #[test]
    fn test_different_commitments_independent_tracking() {
        let mut pool = test_pool();
        // Use all K slots for one commitment
        for i in 0..crate::MAX_STAKE_USES_PER_EPOCH {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([0x22 + i as u8; 32]),
                9999,
                valid_stake(),
            );
            let result = pool.receive_intent_checked(intent, 100 + i as u64, true);
            assert!(result.is_ok());
        }

        // A different commitment should still work (build a different stake proof)
        let different_commitment = pyana_cell::NoteCommitment([0xAB; 32]);
        let mut tree = pyana_commit::Poseidon2MerkleTree::with_depth(4);
        for i in 0..5u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xAA;
            tree.append(pyana_commit::commitment_to_field(&c));
        }
        let leaf = pyana_commit::commitment_to_field(&different_commitment.0);
        let pos = tree.append(leaf);
        for i in 10..15u8 {
            let mut c = [0u8; 32];
            c[0] = i;
            c[1] = 0xBB;
            tree.append(pyana_commit::commitment_to_field(&c));
        }
        let root = tree.root();
        let merkle_proof = tree.prove_membership(pos).unwrap();
        let diff_stake = StakeProof {
            commitment: different_commitment,
            merkle_root: root,
            merkle_proof,
            minimum_value: 100,
        };

        // Update pool root to match new tree
        pool.update_known_note_root(root);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("diff_commitment".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xDD; 32]),
            9999,
            Some(diff_stake),
        );
        let result = pool.receive_intent_checked(intent, 200, true);
        assert!(result.is_ok(), "different commitment should be independent");
    }

    #[test]
    fn test_rate_limiting() {
        let mut pool = test_pool();
        let creator = CommitmentId([0x99; 32]);
        for i in 0..MAX_INTENTS_PER_CREATOR_PER_MINUTE {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
            let result = pool.receive_intent_checked(intent, 100, false);
            assert!(result.is_ok(), "intent {i} should succeed");
        }
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("action_overflow".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
        let result = pool.receive_intent_checked(intent, 100, false);
        assert!(matches!(result, Err(ReceiveError::RateLimited { .. })));
    }

    #[test]
    fn test_rate_limit_resets_after_window() {
        let mut pool = test_pool();
        let creator = CommitmentId([0xAA; 32]);
        for i in 0..MAX_INTENTS_PER_CREATOR_PER_MINUTE {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("a_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
                compound: None,
                predicate_requirements: vec![],
                strict_resource_matching: false,
            };
            let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
            pool.receive_intent_checked(intent, 100, false).unwrap();
        }
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("new_window".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, creator, 9999, valid_stake());
        let result = pool.receive_intent_checked(intent, 161, false);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validation_rejects_oversized_intent() {
        let mut pool = test_pool();
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
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]),
            9999,
            valid_stake(),
        );
        let result = pool.receive_intent_checked(intent, 100, true);
        assert!(matches!(result, Err(ReceiveError::Invalid(_))));
    }

    #[test]
    fn test_commit_reveal_happy_path() {
        let mut pool = test_pool();
        let fulfillment = crate::fulfillment::Fulfillment {
            intent_id: [0x01; 32],
            fulfiller: CommitmentId([0xBB; 32]),
            mode: crate::VerificationMode::Trusted,
            token_data: None,
            proof: None,
            granted_actions: vec!["read".into()],
            granted_resource: "docs/*".into(),
            expiry: Some(5000),
        };
        let commitment = pool.commit_to_fulfill([0x01; 32], &fulfillment, 100);
        assert!(pool.has_commitment_for(&[0x01; 32]));
        assert_eq!(pool.pending_commitment_count(), 1);
        let commitment_hash = IntentPool::hash_commitment(&commitment);
        let reveal = FulfillmentReveal {
            commitment_hash,
            fulfillment: fulfillment.clone(),
            nonce: [0xFF; 32],
        };
        let result = pool.reveal_fulfillment(&reveal, 102);
        assert_eq!(result, Err(CommitRevealError::TooEarly { remaining: 3 }));
        let result = pool.reveal_fulfillment(&reveal, 106);
        assert_eq!(result, Err(CommitRevealError::NonceMismatch));
        assert_eq!(pool.pending_commitment_count(), 1);
    }

    #[test]
    fn test_commit_reveal_no_commitment() {
        let mut pool = test_pool();
        let fulfillment = crate::fulfillment::Fulfillment {
            intent_id: [0x01; 32],
            fulfiller: CommitmentId([0xBB; 32]),
            mode: crate::VerificationMode::Trusted,
            token_data: None,
            proof: None,
            granted_actions: vec!["read".into()],
            granted_resource: "docs/*".into(),
            expiry: Some(5000),
        };
        let reveal = FulfillmentReveal {
            commitment_hash: [0xFF; 32],
            fulfillment,
            nonce: [0x00; 32],
        };
        let result = pool.reveal_fulfillment(&reveal, 200);
        assert_eq!(result, Err(CommitRevealError::NoCommitment));
    }

    #[test]
    fn test_fulfilled_intent_rejected_on_resubmit() {
        let mut pool = test_pool();
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
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x22; 32]), 9999, None);
        let intent_id = intent.id;
        let result = pool.receive_local_intent(intent.clone(), 100);
        assert!(result.is_ok());
        pool.mark_fulfilled(intent_id);
        let result = pool.receive_local_intent(intent, 101);
        assert_eq!(result, Err(ReceiveError::AlreadyFulfilled));
    }

    // -------------------------------------------------------------------
    // AutoFulfillPolicy::ForPatterns regression test (audit #4)
    //
    // Previously the policy ran `Glob::new(p).is_match(intent_pattern)`,
    // which treats the intent's resource_pattern as a LITERAL string.
    // For the obvious case `ForPatterns(vec!["documents/*"])` against
    // intent `resource_pattern = "documents/*"`, the glob `documents/*`
    // would NOT match the literal `"documents/*"` because `*` isn't a
    // literal `*`. The patched implementation uses symmetric
    // `resource_matches` plus literal equality so this case works.
    // -------------------------------------------------------------------
    #[test]
    fn test_for_patterns_matches_literal_equality() {
        let pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: true,
                minimum_stake_value: 0,
            },
            AutoFulfillPolicy::ForPatterns(vec!["documents/*".into()]),
            test_known_root(),
        );
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: Some("documents/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x33; 32]), 9999, None);
        assert!(
            pool.should_auto_fulfill(&intent),
            "documents/* policy must match documents/* intent"
        );
    }

    #[test]
    fn test_for_patterns_rejects_unrelated_pattern() {
        let pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: true,
                minimum_stake_value: 0,
            },
            AutoFulfillPolicy::ForPatterns(vec!["documents/*".into()]),
            test_known_root(),
        );
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: Some("images/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x33; 32]), 9999, None);
        assert!(
            !pool.should_auto_fulfill(&intent),
            "documents/* policy must NOT match images/* intent"
        );
    }
}
