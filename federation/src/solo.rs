//! Solo federation mode: single-node operation for devnets.
//!
//! When running with `FederationMode::Solo`, the local node processes all turns
//! without waiting for BFT quorum. This trades safety (no Byzantine fault tolerance)
//! for liveness (100% uptime with a single node).
//!
//! # Safety Argument
//!
//! Solo mode is safe when:
//! - There is exactly one operator (no Byzantine adversaries)
//! - Single-owner turns cannot harm others regardless of mode
//! - The nullifier log provides replay protection on rejoin
//!
//! # Rejoin Protocol
//!
//! When peers come back online:
//! 1. They receive the solo node's signed nullifier log
//! 2. They validate each entry (no double-spends, valid signatures)
//! 3. Tentative receipts are promoted to Final if no conflicts
//! 4. The federation upgrades back to Full mode

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

// =============================================================================
// Solo Mode — Now A Property of Committee Size
// =============================================================================
//
// Per FEDERATION-UNIFICATION-DESIGN.md §3, the legacy `FederationMode { Full,
// Solo }` enum and `effective_quorum_threshold(mode, n)` helper are gone.
// "Solo" is no longer a runtime mode — it is a property of `members.len() == 1`
// (equivalently, `Federation::is_solo()`). Callers compute threshold via
// `quorum_threshold(num_nodes)` (which returns 1 for n=1 naturally) or read
// it directly from `Federation::threshold()`.

/// True when a federation of `num_nodes` is operating in degenerate-committee
/// ("solo") mode. Convenience predicate for the call sites that historically
/// switched on `FederationMode::Solo`.
pub fn is_solo_committee(num_nodes: usize) -> bool {
    num_nodes <= 1
}

// =============================================================================
// Nullifier Log (solo mode sequencer)
// =============================================================================

/// A signed entry in the solo-mode nullifier log.
///
/// Each entry records a nullifier insertion with the sequencing node's signature.
/// On rejoin, peers replay this log to validate no conflicts.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NullifierLogEntry {
    /// The nullifier being inserted (BLAKE3 hash of the spent note).
    pub nullifier: [u8; 32],
    /// The turn hash that consumed this nullifier.
    pub turn_hash: [u8; 32],
    /// Sequence number (monotonically increasing within an epoch).
    pub sequence: u64,
    /// Block height at which this entry was produced.
    pub height: u64,
    /// BLAKE3-keyed MAC from the sequencing node (not a full Ed25519 sig for perf).
    /// Verifiers who trust the solo node can validate this cheaply.
    pub node_signature: [u8; 32],
}

/// The nullifier log maintained by a solo-mode node.
///
/// This is the authoritative ordering of nullifier insertions during solo operation.
/// It prevents double-spend: if the same nullifier appears twice, the second is rejected.
#[derive(Clone, Debug, Default)]
pub struct NullifierLog {
    /// All entries in sequence order.
    entries: Vec<NullifierLogEntry>,
    /// Fast lookup set for conflict detection.
    seen: HashSet<[u8; 32]>,
    /// Current sequence counter.
    next_sequence: u64,
    /// Signing key for entry authentication (BLAKE3-keyed hash).
    signing_key: [u8; 32],
}

impl NullifierLog {
    /// Create a new empty nullifier log with the given signing key.
    pub fn new(signing_key: [u8; 32]) -> Self {
        Self {
            entries: Vec::new(),
            seen: HashSet::new(),
            next_sequence: 0,
            signing_key,
        }
    }

    /// Attempt to insert a nullifier. Returns Ok(entry) if novel, Err if duplicate.
    pub fn insert(
        &mut self,
        nullifier: [u8; 32],
        turn_hash: [u8; 32],
        height: u64,
    ) -> Result<&NullifierLogEntry, NullifierConflict> {
        if self.seen.contains(&nullifier) {
            return Err(NullifierConflict { nullifier });
        }

        let sequence = self.next_sequence;
        self.next_sequence += 1;

        let node_signature = self.sign_entry(&nullifier, &turn_hash, sequence, height);

        self.seen.insert(nullifier);
        self.entries.push(NullifierLogEntry {
            nullifier,
            turn_hash,
            sequence,
            height,
            node_signature,
        });

        Ok(self.entries.last().unwrap())
    }

    /// Check if a nullifier has already been consumed.
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.seen.contains(nullifier)
    }

    /// Get all entries (for syncing to rejoining peers).
    pub fn entries(&self) -> &[NullifierLogEntry] {
        &self.entries
    }

    /// Number of entries in the log.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the log is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Validate a set of entries from a peer (used during rejoin).
    /// Returns Ok if all entries are valid and conflict-free, Err on first conflict.
    pub fn validate_remote_entries(
        &self,
        entries: &[NullifierLogEntry],
        remote_key: &[u8; 32],
    ) -> Result<(), NullifierConflict> {
        let mut local_seen = self.seen.clone();
        for entry in entries {
            // Verify signature.
            let expected_sig = Self::compute_signature(
                remote_key,
                &entry.nullifier,
                &entry.turn_hash,
                entry.sequence,
                entry.height,
            );
            if expected_sig != entry.node_signature {
                return Err(NullifierConflict {
                    nullifier: entry.nullifier,
                });
            }
            // Check for conflicts with our local state.
            if local_seen.contains(&entry.nullifier) {
                return Err(NullifierConflict {
                    nullifier: entry.nullifier,
                });
            }
            local_seen.insert(entry.nullifier);
        }
        Ok(())
    }

    /// Merge validated remote entries into the local log.
    /// Call this only after `validate_remote_entries` succeeds.
    pub fn merge_validated(&mut self, entries: Vec<NullifierLogEntry>) {
        for entry in entries {
            if !self.seen.contains(&entry.nullifier) {
                self.seen.insert(entry.nullifier);
                self.entries.push(entry);
            }
        }
        // Re-sort by sequence for consistent ordering.
        self.entries.sort_by_key(|e| e.sequence);
        // Update next_sequence to be past the maximum.
        if let Some(max_seq) = self.entries.last().map(|e| e.sequence) {
            self.next_sequence = max_seq + 1;
        }
    }

    fn sign_entry(
        &self,
        nullifier: &[u8; 32],
        turn_hash: &[u8; 32],
        sequence: u64,
        height: u64,
    ) -> [u8; 32] {
        Self::compute_signature(&self.signing_key, nullifier, turn_hash, sequence, height)
    }

    fn compute_signature(
        key: &[u8; 32],
        nullifier: &[u8; 32],
        turn_hash: &[u8; 32],
        sequence: u64,
        height: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_keyed(key);
        hasher.update(b"pyana-nullifier-log-entry-v1");
        hasher.update(nullifier);
        hasher.update(turn_hash);
        hasher.update(&sequence.to_le_bytes());
        hasher.update(&height.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// Error returned when a nullifier has already been consumed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NullifierConflict {
    pub nullifier: [u8; 32],
}

impl std::fmt::Display for NullifierConflict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "nullifier conflict: {} already consumed",
            hex::encode(&self.nullifier[..8])
        )
    }
}

impl std::error::Error for NullifierConflict {}

// =============================================================================
// Solo Consensus State
// =============================================================================

/// Solo-mode consensus state: a thin wrapper that auto-finalizes without quorum.
///
/// When operating with a committee of one (solo), the node:
/// 1. Produces blocks unilaterally (it is always the leader)
/// 2. Signs blocks with its own key only (no waiting for votes)
/// 3. Produces Tentative receipts for consensus-path turns
/// 4. Maintains a nullifier log for ordering
///
/// Solo is detected by inspecting the federation committee size, not a separate
/// mode enum (see FEDERATION-UNIFICATION-DESIGN.md §3).
#[derive(Clone, Debug)]
pub struct SoloConsensusState {
    /// Is the node currently operating as solo (committee of one)? Flipped to
    /// `false` by `detect_peers` when a peer joins.
    pub is_solo: bool,
    /// Current block height (increments on each finalized block).
    pub height: u64,
    /// Signing key for this node.
    pub signing_key: [u8; 32],
    /// The nullifier log.
    pub nullifier_log: NullifierLog,
    /// Whether this node has detected peers and should upgrade.
    pub peers_detected: bool,
}

impl SoloConsensusState {
    /// Create a new solo consensus state.
    pub fn new(signing_key: [u8; 32]) -> Self {
        Self {
            is_solo: true,
            height: 0,
            signing_key,
            nullifier_log: NullifierLog::new(signing_key),
            peers_detected: false,
        }
    }

    /// Signal that peers have been detected. The node should upgrade to multi-
    /// node operation.
    pub fn detect_peers(&mut self) {
        self.peers_detected = true;
        tracing::info!(
            "peers detected at height {}: leaving solo (committee-of-one) operation",
            self.height
        );
        self.is_solo = false;
    }

    /// Get the effective quorum threshold for the current committee size.
    pub fn effective_threshold(&self, num_nodes: usize) -> usize {
        if self.is_solo {
            1
        } else {
            crate::quorum_threshold(num_nodes)
        }
    }

    /// Advance height (called after processing a turn in solo mode).
    pub fn advance_height(&mut self) {
        self.height += 1;
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_solo_committee() {
        assert!(is_solo_committee(0));
        assert!(is_solo_committee(1));
        assert!(!is_solo_committee(2));
        assert!(!is_solo_committee(7));
    }

    #[test]
    fn test_nullifier_log_insert_and_conflict() {
        let key = [0xAA; 32];
        let mut log = NullifierLog::new(key);

        let nullifier = [0x01; 32];
        let turn_hash = [0x02; 32];

        // First insert succeeds.
        let result = log.insert(nullifier, turn_hash, 100);
        assert!(result.is_ok());
        let entry = result.unwrap();
        assert_eq!(entry.sequence, 0);
        assert_eq!(entry.nullifier, nullifier);

        // Second insert of same nullifier fails.
        let result2 = log.insert(nullifier, [0x03; 32], 101);
        assert!(result2.is_err());
        assert_eq!(result2.unwrap_err().nullifier, nullifier);
    }

    #[test]
    fn test_nullifier_log_ordering() {
        let key = [0xBB; 32];
        let mut log = NullifierLog::new(key);

        for i in 0..5u8 {
            let nullifier = [i; 32];
            log.insert(nullifier, [0xFF; 32], 100 + i as u64).unwrap();
        }

        assert_eq!(log.len(), 5);
        for (i, entry) in log.entries().iter().enumerate() {
            assert_eq!(entry.sequence, i as u64);
        }
    }

    #[test]
    fn test_nullifier_log_validate_remote() {
        let key_a = [0xAA; 32];
        let key_b = [0xBB; 32];

        let mut log_a = NullifierLog::new(key_a);
        let mut log_b = NullifierLog::new(key_b);

        // Node A inserts nullifier 1.
        log_a.insert([0x01; 32], [0xF1; 32], 100).unwrap();

        // Node B inserts nullifier 2.
        log_b.insert([0x02; 32], [0xF2; 32], 100).unwrap();

        // Node A validates node B's entries (no conflict).
        let result = log_a.validate_remote_entries(log_b.entries(), &key_b);
        assert!(result.is_ok());

        // Now insert a conflicting nullifier on B.
        log_b.insert([0x01; 32], [0xF3; 32], 101).unwrap();

        // Node A validates again -- now there's a conflict on nullifier 0x01.
        let result2 = log_a.validate_remote_entries(log_b.entries(), &key_b);
        assert!(result2.is_err());
    }

    #[test]
    fn test_solo_state_upgrade_to_full() {
        let key = [0xCC; 32];
        let mut state = SoloConsensusState::new(key);
        assert!(state.is_solo);
        assert_eq!(state.effective_threshold(3), 1);

        state.detect_peers();
        assert!(!state.is_solo);
        assert_eq!(state.effective_threshold(3), 2);
    }

    #[test]
    fn test_nullifier_log_merge() {
        let key_a = [0xAA; 32];
        let key_b = [0xBB; 32];

        let mut log_a = NullifierLog::new(key_a);
        let mut log_b = NullifierLog::new(key_b);

        log_a.insert([0x01; 32], [0xF1; 32], 100).unwrap();
        log_b.insert([0x02; 32], [0xF2; 32], 100).unwrap();
        log_b.insert([0x03; 32], [0xF3; 32], 101).unwrap();

        // Validate and merge.
        assert!(
            log_a
                .validate_remote_entries(log_b.entries(), &key_b)
                .is_ok()
        );
        log_a.merge_validated(log_b.entries().to_vec());

        // Now log_a should have all 3 nullifiers.
        assert!(log_a.contains(&[0x01; 32]));
        assert!(log_a.contains(&[0x02; 32]));
        assert!(log_a.contains(&[0x03; 32]));
        assert_eq!(log_a.len(), 3);
    }

    // =========================================================================
    // Integration-style tests demonstrating full solo-mode scenarios
    // =========================================================================

    #[test]
    fn test_solo_mode_single_node_processes_turn_tentative() {
        // Scenario: Solo mode node processes a turn, receipt has Tentative finality.
        use pyana_turn::Finality;

        let key = [0xCC; 32];
        let mut state = SoloConsensusState::new(key);

        // In solo mode, threshold = 1.
        assert_eq!(state.effective_threshold(3), 1);
        assert!(state.is_solo);

        // Simulate processing a turn: the node is the sole sequencer.
        let nullifier = [0x42; 32];
        let turn_hash = [0xAB; 32];
        let entry = state
            .nullifier_log
            .insert(nullifier, turn_hash, state.height);
        assert!(entry.is_ok());
        state.advance_height();
        assert_eq!(state.height, 1);

        // In solo mode, consensus-path receipts should have Tentative finality.
        let finality = if state.is_solo {
            Finality::Tentative
        } else {
            Finality::Final
        };
        assert_eq!(finality, Finality::Tentative);
    }

    #[test]
    fn test_solo_fast_path_single_signature_sufficient() {
        // Solo: 1 signature is enough for fast-path certificate.
        let key = [0xCC; 32];
        let state = SoloConsensusState::new(key);
        assert_eq!(state.effective_threshold(3), 1);
    }

    #[test]
    fn test_mode_upgrade_solo_to_full() {
        // Scenario: Start solo, peer joins, switch to multi-node operation.
        use pyana_turn::Finality;

        let key = [0xDD; 32];
        let mut state = SoloConsensusState::new(key);

        // Initially solo.
        assert!(state.is_solo);

        // Process a turn in solo mode -> Tentative.
        let finality_before = if state.is_solo {
            Finality::Tentative
        } else {
            Finality::Final
        };
        assert_eq!(finality_before, Finality::Tentative);

        // Peer joins -> upgrade.
        state.detect_peers();
        assert!(!state.is_solo);

        let finality_after = if state.is_solo {
            Finality::Tentative
        } else {
            Finality::Final
        };
        assert_eq!(finality_after, Finality::Final);

        // Threshold is now standard BFT.
        assert_eq!(state.effective_threshold(3), 2);
    }

    #[test]
    fn test_tentative_distinct_from_final() {
        // Scenario: API consumers can distinguish Tentative from Final.
        use pyana_turn::Finality;

        let tentative = Finality::Tentative;
        let final_ = Finality::Final;

        // They are different enum variants.
        assert_ne!(tentative, final_);

        // Serialize differently.
        let t_bytes = postcard::to_allocvec(&tentative).unwrap();
        let f_bytes = postcard::to_allocvec(&final_).unwrap();
        assert_ne!(t_bytes, f_bytes);

        // Round-trip.
        let t_back: Finality = postcard::from_bytes(&t_bytes).unwrap();
        let f_back: Finality = postcard::from_bytes(&f_bytes).unwrap();
        assert_eq!(t_back, Finality::Tentative);
        assert_eq!(f_back, Finality::Final);
    }

    #[test]
    fn test_nullifier_double_spend_prevented_solo() {
        // Scenario: Solo mode prevents double-spend via nullifier log.
        let key = [0xEE; 32];
        let mut state = SoloConsensusState::new(key);

        let nullifier = [0x99; 32];
        let turn_hash_1 = [0xA1; 32];
        let turn_hash_2 = [0xA2; 32];

        // First spend succeeds.
        assert!(
            state
                .nullifier_log
                .insert(nullifier, turn_hash_1, 0)
                .is_ok()
        );

        // Second spend of same nullifier is REJECTED (double-spend attempt).
        let result = state.nullifier_log.insert(nullifier, turn_hash_2, 1);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().nullifier, nullifier);
    }
}
