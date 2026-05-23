//! Epoch transitions: membership changes, key rotation, threshold updates.
//!
//! An epoch is a period of N blocks (configurable, default 10000) during which
//! the validator set is fixed. At each epoch boundary:
//!
//! 1. Pending membership changes (joins/leaves) are applied.
//! 2. Each continuing validator generates a fresh XMSS signing tree for the new epoch.
//! 3. The threshold adjusts based on the new membership count (BFT: `(n - 1) / 3 + 1`).
//! 4. The old epoch's validators attest the transition via a QuorumCertificate.
//!
//! Historical epoch configs are retained so that old-epoch signatures remain
//! verifiable against the signing key roots that were active at the time.

use serde::{Deserialize, Serialize};

use crate::types::{PublicKey, QuorumCertificate, Signature, SigningKey, sign};

// =============================================================================
// Constants
// =============================================================================

/// Default number of blocks per epoch.
pub const DEFAULT_EPOCH_LENGTH: u64 = 10000;

// =============================================================================
// Epoch Configuration
// =============================================================================

/// Configuration for a single epoch of the federation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochConfig {
    /// Number of blocks per epoch.
    pub epoch_length: u64,
    /// The current epoch number (0-indexed).
    pub current_epoch: u64,
    /// The block height at which this epoch started.
    pub epoch_start_height: u64,
    /// The active validator set for this epoch.
    pub members: Vec<ValidatorInfo>,
    /// BFT threshold: minimum votes needed to finalize.
    pub threshold: usize,
}

/// Information about a validator in the federation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidatorInfo {
    /// The validator's Ed25519 public key (identity).
    pub public_key: PublicKey,
    /// Root hash of the validator's XMSS signing tree for this epoch.
    /// A fresh tree is generated at each epoch boundary for forward secrecy.
    pub signing_key_root: [u8; 32],
    /// Validator's stake (for weighted threshold schemes).
    pub stake: u64,
    /// The epoch in which this validator first joined the federation.
    pub joined_epoch: u64,
}

// =============================================================================
// Epoch Transition
// =============================================================================

/// A transition between two consecutive epochs.
///
/// Proposed by the epoch-boundary block proposer, voted on by old-epoch validators,
/// and applied once the QC is formed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochTransition {
    /// The epoch being departed.
    pub from_epoch: u64,
    /// The epoch being entered.
    pub to_epoch: u64,
    /// Validators joining in the new epoch.
    pub added_validators: Vec<ValidatorInfo>,
    /// Public keys of validators being removed.
    pub removed_validators: Vec<PublicKey>,
    /// The new threshold for the next epoch.
    pub new_threshold: usize,
    /// QC from old-epoch validators attesting this transition.
    pub attestation: QuorumCertificate,
}

impl EpochTransition {
    /// Compute the canonical signing message for an epoch transition.
    ///
    /// Old-epoch validators sign this message to attest the transition.
    pub fn signing_message(
        from_epoch: u64,
        to_epoch: u64,
        added: &[ValidatorInfo],
        removed: &[PublicKey],
        new_threshold: usize,
    ) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-epoch-transition-v1");
        msg.extend_from_slice(&from_epoch.to_le_bytes());
        msg.extend_from_slice(&to_epoch.to_le_bytes());
        msg.extend_from_slice(&(new_threshold as u64).to_le_bytes());
        for v in added {
            msg.extend_from_slice(&v.public_key.0);
            msg.extend_from_slice(&v.signing_key_root);
            msg.extend_from_slice(&v.stake.to_le_bytes());
            msg.extend_from_slice(&v.joined_epoch.to_le_bytes());
        }
        for pk in removed {
            msg.extend_from_slice(&pk.0);
        }
        msg
    }
}

// =============================================================================
// Errors
// =============================================================================

/// Errors that can occur during epoch transitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EpochError {
    /// The transition targets the wrong epoch.
    EpochMismatch { expected: u64, got: u64 },
    /// The new member set would be empty.
    EmptyMemberSet,
    /// A validator being removed is not in the current set.
    ValidatorNotFound,
    /// A validator being added is already in the current set.
    ValidatorAlreadyExists,
    /// The attestation QC does not have enough votes.
    InsufficientAttestation,
    /// The attestation QC references the wrong content.
    InvalidAttestation,
    /// The new threshold is invalid for the member count.
    InvalidThreshold { members: usize, threshold: usize },
}

impl std::fmt::Display for EpochError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EpochMismatch { expected, got } => {
                write!(f, "epoch mismatch: expected {expected}, got {got}")
            }
            Self::EmptyMemberSet => write!(f, "new member set cannot be empty"),
            Self::ValidatorNotFound => write!(f, "validator to remove not found in current set"),
            Self::ValidatorAlreadyExists => write!(f, "validator to add already exists in set"),
            Self::InsufficientAttestation => {
                write!(f, "attestation QC does not meet threshold")
            }
            Self::InvalidAttestation => write!(f, "attestation QC is invalid"),
            Self::InvalidThreshold { members, threshold } => {
                write!(f, "invalid threshold {threshold} for {members} members")
            }
        }
    }
}

impl std::error::Error for EpochError {}

// =============================================================================
// Epoch Boundary Detection
// =============================================================================

/// Returns `true` if the given block height is an epoch boundary.
///
/// An epoch boundary occurs at heights that are exact multiples of the epoch length.
/// Height 0 is NOT a boundary (it is genesis).
pub fn is_epoch_boundary(height: u64, epoch_length: u64) -> bool {
    height > 0 && epoch_length > 0 && height % epoch_length == 0
}

/// Compute the epoch number for a given block height.
pub fn compute_epoch(height: u64, epoch_length: u64) -> u64 {
    if epoch_length == 0 {
        return 0;
    }
    height / epoch_length
}

// =============================================================================
// Threshold Computation
// =============================================================================

/// Compute the BFT threshold for a given number of members.
///
/// Delegates to [`crate::quorum_threshold`], the canonical formula:
/// `threshold = n - floor((n-1)/3)`.
///
/// For n=1: threshold=1, n=2: threshold=2, n=3: threshold=2, n=4: threshold=3, n=7: threshold=5, n=10: threshold=7.
pub fn compute_bft_threshold(member_count: usize) -> usize {
    crate::quorum_threshold(member_count)
}

// =============================================================================
// Epoch Transition Logic
// =============================================================================

/// Propose an epoch transition based on pending membership changes.
///
/// Computes the new member set, adjusts the threshold, and constructs a
/// transition struct (without the attestation QC, which must be collected
/// separately via the consensus voting mechanism).
pub fn propose_epoch_transition(
    current_config: &EpochConfig,
    pending_joins: &[ValidatorInfo],
    pending_leaves: &[PublicKey],
) -> Result<EpochTransition, EpochError> {
    // Validate removals: each must exist in current set.
    for pk in pending_leaves {
        if !current_config.members.iter().any(|m| &m.public_key == pk) {
            return Err(EpochError::ValidatorNotFound);
        }
    }

    // Validate additions: each must NOT exist in current set.
    for v in pending_joins {
        if current_config
            .members
            .iter()
            .any(|m| m.public_key == v.public_key)
        {
            return Err(EpochError::ValidatorAlreadyExists);
        }
    }

    // Compute new member set.
    let mut new_members: Vec<ValidatorInfo> = current_config
        .members
        .iter()
        .filter(|m| !pending_leaves.contains(&m.public_key))
        .cloned()
        .collect();
    new_members.extend(pending_joins.iter().cloned());

    if new_members.is_empty() {
        return Err(EpochError::EmptyMemberSet);
    }

    let new_threshold = compute_bft_threshold(new_members.len());

    Ok(EpochTransition {
        from_epoch: current_config.current_epoch,
        to_epoch: current_config.current_epoch + 1,
        added_validators: pending_joins.to_vec(),
        removed_validators: pending_leaves.to_vec(),
        new_threshold,
        // Attestation placeholder -- must be filled by the caller after
        // collecting votes from old-epoch validators.
        attestation: QuorumCertificate {
            block_hash: [0u8; 32],
            height: 0,
            view: 0,
            aggregate_qc: None,
            votes: Vec::new(),
            threshold: current_config.threshold,
        },
    })
}

/// Apply a verified epoch transition to the current configuration.
///
/// Updates the epoch config in-place: advances the epoch number, updates
/// the member set, and adjusts the threshold.
pub fn apply_epoch_transition(
    config: &mut EpochConfig,
    transition: &EpochTransition,
) -> Result<(), EpochError> {
    // Verify epoch numbers match.
    if transition.from_epoch != config.current_epoch {
        return Err(EpochError::EpochMismatch {
            expected: config.current_epoch,
            got: transition.from_epoch,
        });
    }
    if transition.to_epoch != config.current_epoch + 1 {
        return Err(EpochError::EpochMismatch {
            expected: config.current_epoch + 1,
            got: transition.to_epoch,
        });
    }

    // Remove departed validators.
    config
        .members
        .retain(|m| !transition.removed_validators.contains(&m.public_key));

    // Add new validators.
    config.members.extend(transition.added_validators.clone());

    if config.members.is_empty() {
        return Err(EpochError::EmptyMemberSet);
    }

    // Validate the new threshold.
    let expected_threshold = compute_bft_threshold(config.members.len());
    if transition.new_threshold != expected_threshold {
        return Err(EpochError::InvalidThreshold {
            members: config.members.len(),
            threshold: transition.new_threshold,
        });
    }

    // Apply the transition.
    config.current_epoch = transition.to_epoch;
    config.epoch_start_height += config.epoch_length;
    config.threshold = transition.new_threshold;

    Ok(())
}

/// Verify an epoch transition against the old configuration.
///
/// Checks:
/// 1. The attestation QC has enough votes from old-epoch validators.
/// 2. Each vote's Ed25519 signature is verified against the member's public key.
/// 3. The transition epoch numbers are sequential.
/// 4. The new threshold is correct for the resulting member count.
pub fn verify_epoch_transition(transition: &EpochTransition, old_config: &EpochConfig) -> bool {
    // Check epoch sequencing.
    if transition.from_epoch != old_config.current_epoch {
        return false;
    }
    if transition.to_epoch != old_config.current_epoch + 1 {
        return false;
    }

    // Verify the attestation QC has enough votes (count check).
    if transition.attestation.votes.len() < old_config.threshold {
        return false;
    }

    // Verify each vote's signature against old-epoch member keys.
    // This prevents forged attestations where votes are merely counted without
    // verifying that the signers are actually members of the old epoch.
    let member_keys: Vec<PublicKey> = old_config
        .members
        .iter()
        .map(|v| v.public_key.clone())
        .collect();
    let vote_message = QuorumCertificate::vote_message(
        &transition.attestation.block_hash,
        transition.attestation.height,
        transition.attestation.view,
    );
    for (voter_id, sig) in &transition.attestation.votes {
        match member_keys.get(*voter_id) {
            Some(pk) => {
                if !pk.verify(&vote_message, sig) {
                    return false;
                }
            }
            None => return false,
        }
    }

    // Verify removed validators exist in old config.
    for pk in &transition.removed_validators {
        if !old_config.members.iter().any(|m| &m.public_key == pk) {
            return false;
        }
    }

    // Verify added validators are NOT already in old config.
    for v in &transition.added_validators {
        if old_config
            .members
            .iter()
            .any(|m| m.public_key == v.public_key)
        {
            return false;
        }
    }

    // Compute expected new member count and threshold.
    let new_count = old_config.members.len() + transition.added_validators.len()
        - transition.removed_validators.len();
    if new_count == 0 {
        return false;
    }
    let expected_threshold = compute_bft_threshold(new_count);
    if transition.new_threshold != expected_threshold {
        return false;
    }

    true
}

// =============================================================================
// XMSS Key Rotation
// =============================================================================

/// Generate a new XMSS tree root for a validator entering a new epoch.
///
/// In production, this would generate a full XMSS tree with the given height
/// (number of one-time signatures available). For now, we derive a deterministic
/// root from the seed and epoch using BLAKE3.
///
/// # Parameters
/// - `seed`: The validator's long-term secret seed (32 bytes).
/// - `epoch`: The epoch number for which the tree is generated.
/// - `tree_height`: The XMSS tree height (e.g., 10 for 1024 signatures per epoch).
pub fn new_epoch_tree(seed: &[u8; 32], epoch: u64, tree_height: u32) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-xmss-epoch-tree-v1");
    hasher.update(seed);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(&tree_height.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Rotate signing keys for all continuing validators in an epoch transition.
///
/// Returns a new member list with updated `signing_key_root` values for
/// validators that persist across the epoch boundary. New validators keep
/// the root they were provisioned with.
pub fn rotate_signing_keys(
    members: &[ValidatorInfo],
    seeds: &[[u8; 32]],
    new_epoch: u64,
    tree_height: u32,
) -> Vec<ValidatorInfo> {
    members
        .iter()
        .enumerate()
        .map(|(i, v)| {
            if let Some(seed) = seeds.get(i) {
                let new_root = new_epoch_tree(seed, new_epoch, tree_height);
                ValidatorInfo {
                    signing_key_root: new_root,
                    ..v.clone()
                }
            } else {
                v.clone()
            }
        })
        .collect()
}

// =============================================================================
// Epoch History
// =============================================================================

/// Historical epoch record, retained for verifying old-epoch signatures.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochRecord {
    /// The epoch number.
    pub epoch: u64,
    /// The configuration that was active during this epoch.
    pub config: EpochConfig,
    /// The transition that ended this epoch (None for the current epoch).
    pub transition: Option<EpochTransition>,
}

/// Tracks epoch history for signature verification against historical configs.
#[derive(Clone, Debug, Default)]
pub struct EpochHistory {
    /// All past epoch records, ordered by epoch number.
    pub records: Vec<EpochRecord>,
}

impl EpochHistory {
    /// Create a new empty epoch history.
    pub fn new() -> Self {
        Self {
            records: Vec::new(),
        }
    }

    /// Record a completed epoch.
    pub fn record_epoch(&mut self, config: EpochConfig, transition: Option<EpochTransition>) {
        self.records.push(EpochRecord {
            epoch: config.current_epoch,
            config,
            transition,
        });
    }

    /// Look up the configuration that was active at a given epoch.
    pub fn config_at_epoch(&self, epoch: u64) -> Option<&EpochConfig> {
        self.records
            .iter()
            .find(|r| r.epoch == epoch)
            .map(|r| &r.config)
    }

    /// Look up the validator info for a public key at a given epoch.
    ///
    /// Used to verify historical signatures: the `signing_key_root` at that
    /// epoch is needed to validate XMSS signatures produced during that epoch.
    pub fn validator_at_epoch(&self, epoch: u64, public_key: &PublicKey) -> Option<&ValidatorInfo> {
        self.config_at_epoch(epoch)
            .and_then(|c| c.members.iter().find(|m| &m.public_key == public_key))
    }
}

// =============================================================================
// Pending Membership Changes (Governance)
// =============================================================================

/// Tracks pending join/leave requests that will be applied at the next epoch boundary.
#[derive(Clone, Debug, Default)]
pub struct PendingMembershipChanges {
    /// Validators requesting to join (approved by threshold vote).
    pub pending_joins: Vec<ValidatorInfo>,
    /// Validators announcing departure.
    pub pending_leaves: Vec<PublicKey>,
}

impl PendingMembershipChanges {
    /// Create a new empty set of pending changes.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a validator's intent to join. Must be approved by threshold vote
    /// before being included in `pending_joins`.
    pub fn request_join(&mut self, validator: ValidatorInfo) {
        // Avoid duplicate join requests.
        if !self
            .pending_joins
            .iter()
            .any(|v| v.public_key == validator.public_key)
        {
            self.pending_joins.push(validator);
        }
    }

    /// Register a validator's intent to leave.
    pub fn request_leave(&mut self, public_key: PublicKey) {
        if !self.pending_leaves.contains(&public_key) {
            self.pending_leaves.push(public_key);
        }
    }

    /// Clear all pending changes (after they have been applied).
    pub fn clear(&mut self) {
        self.pending_joins.clear();
        self.pending_leaves.clear();
    }

    /// Whether there are any pending changes.
    pub fn is_empty(&self) -> bool {
        self.pending_joins.is_empty() && self.pending_leaves.is_empty()
    }
}

// =============================================================================
// EpochConfig constructors
// =============================================================================

impl EpochConfig {
    /// Create a genesis epoch configuration.
    pub fn genesis(members: Vec<ValidatorInfo>, epoch_length: u64) -> Self {
        let threshold = compute_bft_threshold(members.len());
        Self {
            epoch_length,
            current_epoch: 0,
            epoch_start_height: 0,
            members,
            threshold,
        }
    }

    /// Create with default epoch length.
    pub fn genesis_default(members: Vec<ValidatorInfo>) -> Self {
        Self::genesis(members, DEFAULT_EPOCH_LENGTH)
    }

    /// Extract the public keys of all members (for compatibility with ConsensusConfig).
    pub fn member_public_keys(&self) -> Vec<PublicKey> {
        self.members.iter().map(|m| m.public_key.clone()).collect()
    }

    /// The height at which the current epoch ends (exclusive).
    pub fn epoch_end_height(&self) -> u64 {
        self.epoch_start_height + self.epoch_length
    }

    /// Check if a given height falls within this epoch.
    pub fn contains_height(&self, height: u64) -> bool {
        height >= self.epoch_start_height && height < self.epoch_end_height()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::generate_keypair;

    /// Helper to create a ValidatorInfo with a random keypair.
    fn make_validator(epoch: u64) -> (ValidatorInfo, SigningKey) {
        let (sk, pk) = generate_keypair();
        let mut root = [0u8; 32];
        getrandom::fill(&mut root).unwrap();
        let info = ValidatorInfo {
            public_key: pk,
            signing_key_root: root,
            stake: 1,
            joined_epoch: epoch,
        };
        (info, sk)
    }

    #[test]
    fn test_is_epoch_boundary() {
        assert!(!is_epoch_boundary(0, 10000));
        assert!(is_epoch_boundary(10000, 10000));
        assert!(is_epoch_boundary(20000, 10000));
        assert!(!is_epoch_boundary(9999, 10000));
        assert!(!is_epoch_boundary(10001, 10000));
        assert!(is_epoch_boundary(5, 5));
        assert!(!is_epoch_boundary(3, 5));
    }

    #[test]
    fn test_compute_epoch() {
        assert_eq!(compute_epoch(0, 10000), 0);
        assert_eq!(compute_epoch(9999, 10000), 0);
        assert_eq!(compute_epoch(10000, 10000), 1);
        assert_eq!(compute_epoch(10001, 10000), 1);
        assert_eq!(compute_epoch(20000, 10000), 2);
        assert_eq!(compute_epoch(25000, 10000), 2);
    }

    #[test]
    fn test_compute_bft_threshold() {
        assert_eq!(compute_bft_threshold(0), 0);
        assert_eq!(compute_bft_threshold(1), 1);
        assert_eq!(compute_bft_threshold(2), 2);
        assert_eq!(compute_bft_threshold(3), 2);
        assert_eq!(compute_bft_threshold(4), 3);
        assert_eq!(compute_bft_threshold(5), 4);
        assert_eq!(compute_bft_threshold(6), 4);
        assert_eq!(compute_bft_threshold(7), 5);
        assert_eq!(compute_bft_threshold(10), 7);
    }

    #[test]
    fn test_add_validator_epoch_transition() {
        let (v0, _sk0) = make_validator(0);
        let (v1, _sk1) = make_validator(0);
        let (v2, _sk2) = make_validator(0);
        let (v3, _sk3) = make_validator(0);

        let mut config = EpochConfig::genesis(vec![v0.clone(), v1.clone(), v2.clone()], 100);
        assert_eq!(config.threshold, 2); // quorum_threshold(3) = 3 - 0 = 2 (was wrong: 1)

        // Propose adding v3.
        let transition = propose_epoch_transition(&config, &[v3.clone()], &[]).unwrap();

        assert_eq!(transition.from_epoch, 0);
        assert_eq!(transition.to_epoch, 1);
        assert_eq!(transition.added_validators.len(), 1);
        assert_eq!(transition.removed_validators.len(), 0);
        assert_eq!(transition.new_threshold, 3); // quorum_threshold(4) = 4 - 1 = 3

        // Fill in a valid-looking attestation.
        let mut transition = transition;
        transition.attestation.threshold = config.threshold;
        transition.attestation.votes = vec![(0, Signature([0u8; 64])), (1, Signature([0u8; 64]))];

        // Apply it.
        apply_epoch_transition(&mut config, &transition).unwrap();

        assert_eq!(config.current_epoch, 1);
        assert_eq!(config.members.len(), 4);
        assert_eq!(config.threshold, 3);
        assert!(config.members.contains(&v3));
    }

    #[test]
    fn test_remove_validator_epoch_transition() {
        let (v0, _sk0) = make_validator(0);
        let (v1, _sk1) = make_validator(0);
        let (v2, _sk2) = make_validator(0);
        let (v3, _sk3) = make_validator(0);

        let mut config =
            EpochConfig::genesis(vec![v0.clone(), v1.clone(), v2.clone(), v3.clone()], 100);
        assert_eq!(config.threshold, 3); // quorum_threshold(4) = 4 - 1 = 3

        // Remove v3.
        let transition = propose_epoch_transition(&config, &[], &[v3.public_key.clone()]).unwrap();

        assert_eq!(transition.new_threshold, 2); // quorum_threshold(3) = 3 - 0 = 2

        let mut transition = transition;
        transition.attestation.threshold = config.threshold;
        transition.attestation.votes = vec![
            (0, Signature([0u8; 64])),
            (1, Signature([0u8; 64])),
            (2, Signature([0u8; 64])),
        ];

        apply_epoch_transition(&mut config, &transition).unwrap();

        assert_eq!(config.current_epoch, 1);
        assert_eq!(config.members.len(), 3);
        assert_eq!(config.threshold, 2);
        assert!(!config.members.iter().any(|m| m.public_key == v3.public_key));
    }

    #[test]
    fn test_threshold_adjusts_correctly() {
        // 4 members -> threshold 3
        assert_eq!(compute_bft_threshold(4), 3);
        // 7 members -> threshold 5
        assert_eq!(compute_bft_threshold(7), 5);
        // 10 members -> threshold 7
        assert_eq!(compute_bft_threshold(10), 7);
        // 13 members -> threshold 9
        assert_eq!(compute_bft_threshold(13), 9);
    }

    #[test]
    fn test_epoch_transition_requires_attestation() {
        let (v0, sk0) = make_validator(0);
        let (v1, _sk1) = make_validator(0);
        let (v2, _sk2) = make_validator(0);
        let (v3, _sk3) = make_validator(1);

        let config = EpochConfig::genesis(vec![v0.clone(), v1.clone(), v2.clone()], 100);

        let mut transition = propose_epoch_transition(&config, &[v3.clone()], &[]).unwrap();

        // Empty attestation should fail verification.
        assert!(!verify_epoch_transition(&transition, &config));

        // Add a properly signed vote to the attestation.
        // The vote message must match what QuorumCertificate::vote_message produces.
        let vote_message = QuorumCertificate::vote_message(
            &transition.attestation.block_hash,
            transition.attestation.height,
            transition.attestation.view,
        );
        let sig0 = sign(&sk0, &vote_message);
        transition.attestation.threshold = config.threshold;
        transition.attestation.votes = vec![(0, sig0)];
        assert!(verify_epoch_transition(&transition, &config));
    }

    #[test]
    fn test_key_rotation() {
        let seed_a = [1u8; 32];
        let seed_b = [2u8; 32];

        let root_epoch_0_a = new_epoch_tree(&seed_a, 0, 10);
        let root_epoch_1_a = new_epoch_tree(&seed_a, 1, 10);
        let root_epoch_0_b = new_epoch_tree(&seed_b, 0, 10);

        // Different epochs produce different roots.
        assert_ne!(root_epoch_0_a, root_epoch_1_a);
        // Different seeds produce different roots.
        assert_ne!(root_epoch_0_a, root_epoch_0_b);
        // Same inputs produce same output (deterministic).
        assert_eq!(root_epoch_0_a, new_epoch_tree(&seed_a, 0, 10));
    }

    #[test]
    fn test_old_signatures_verifiable_via_history() {
        let (v0, _) = make_validator(0);
        let (v1, _) = make_validator(0);
        let (v2, _) = make_validator(0);

        let config_epoch_0 = EpochConfig::genesis(vec![v0.clone(), v1.clone(), v2.clone()], 100);

        let mut history = EpochHistory::new();
        history.record_epoch(config_epoch_0.clone(), None);

        // After epoch 0, we can look up v0's signing_key_root.
        let found = history.validator_at_epoch(0, &v0.public_key);
        assert!(found.is_some());
        assert_eq!(found.unwrap().signing_key_root, v0.signing_key_root);

        // Epoch 1 hasn't been recorded yet.
        assert!(history.config_at_epoch(1).is_none());
    }

    #[test]
    fn test_pending_membership_changes() {
        let (v0, _) = make_validator(0);
        let (v1, _) = make_validator(1);

        let mut pending = PendingMembershipChanges::new();
        assert!(pending.is_empty());

        pending.request_join(v0.clone());
        assert!(!pending.is_empty());
        assert_eq!(pending.pending_joins.len(), 1);

        // Duplicate join request is ignored.
        pending.request_join(v0.clone());
        assert_eq!(pending.pending_joins.len(), 1);

        pending.request_leave(v1.public_key.clone());
        assert_eq!(pending.pending_leaves.len(), 1);

        // Duplicate leave request is ignored.
        pending.request_leave(v1.public_key.clone());
        assert_eq!(pending.pending_leaves.len(), 1);

        pending.clear();
        assert!(pending.is_empty());
    }

    #[test]
    fn test_epoch_config_height_math() {
        let (v0, _) = make_validator(0);
        let config = EpochConfig::genesis(vec![v0], 100);

        assert_eq!(config.epoch_start_height, 0);
        assert_eq!(config.epoch_end_height(), 100);
        assert!(config.contains_height(0));
        assert!(config.contains_height(99));
        assert!(!config.contains_height(100));
    }

    #[test]
    fn test_propose_errors() {
        let (v0, _) = make_validator(0);
        let (v1, _) = make_validator(0);
        let (v_new, _) = make_validator(1);

        let config = EpochConfig::genesis(vec![v0.clone(), v1.clone()], 100);

        // Removing a validator not in the set.
        let result = propose_epoch_transition(&config, &[], &[v_new.public_key.clone()]);
        assert!(matches!(result, Err(EpochError::ValidatorNotFound)));

        // Adding a validator already in the set.
        let result = propose_epoch_transition(&config, &[v0.clone()], &[]);
        assert!(matches!(result, Err(EpochError::ValidatorAlreadyExists)));

        // Removing all validators.
        let result = propose_epoch_transition(
            &config,
            &[],
            &[v0.public_key.clone(), v1.public_key.clone()],
        );
        assert!(matches!(result, Err(EpochError::EmptyMemberSet)));
    }

    #[test]
    fn test_rotate_signing_keys() {
        let (v0, _) = make_validator(0);
        let (v1, _) = make_validator(0);

        let seed_0 = [10u8; 32];
        let seed_1 = [20u8; 32];
        let seeds = vec![seed_0, seed_1];

        let original_root_0 = v0.signing_key_root;
        let original_root_1 = v1.signing_key_root;

        let rotated = rotate_signing_keys(&[v0, v1], &seeds, 1, 10);

        // Roots should have changed.
        assert_ne!(rotated[0].signing_key_root, original_root_0);
        assert_ne!(rotated[1].signing_key_root, original_root_1);

        // Should match what new_epoch_tree produces.
        assert_eq!(rotated[0].signing_key_root, new_epoch_tree(&seed_0, 1, 10));
        assert_eq!(rotated[1].signing_key_root, new_epoch_tree(&seed_1, 1, 10));
    }
}
