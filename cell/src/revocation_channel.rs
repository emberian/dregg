//! RevocationChannel: opt-in synchrony primitive for instant capability revocation.
//!
//! A RevocationChannel is a circuit breaker between a revoker and one or more subjects.
//! Subjects voluntarily subscribe and check channel state before exercising delegated
//! capabilities. This provides O(1) revocation lookup without requiring synchronous
//! communication with the revoker.
//!
//! # Lifecycle
//!
//! 1. **Creation**: Revoker creates a channel, declaring a `channel_id`.
//! 2. **Subscription**: A subject adds `channel_id` to their `DelegatedRef`.
//! 3. **Steady state**: Before exercising a gated capability, the subject checks channel state.
//! 4. **Trip**: Revoker calls `trip()` on the channel. All subscribers see it on next check.
//! 5. **Post-trip**: Subjects whose channel is tripped MUST NOT act on gated capabilities.
//!
//! # Integration with staleness
//!
//! The channel degrades gracefully when connectivity is unavailable:
//! - Subject caches `(channel_state, attestation_height, last_checked_at)`.
//! - If `now - last_checked_at <= max_staleness`: act freely (channel was active at last check).
//! - If stale: must re-check channel state before acting on the gated capability.
//!
//! This means the channel does NOT break offline operation. It bounds the window during
//! which a tripped channel goes unnoticed to `max_staleness`, exactly as epoch-based
//! revocation does today. The improvement is targeted (per-channel) and provable.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::id::CellId;

/// Unique identifier for a revocation channel.
/// Derived as: BLAKE3("pyana-revocation-channel" || revoker || nonce)
pub type ChannelId = [u8; 32];

/// The state of a revocation channel.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChannelState {
    /// Channel is active -- capabilities gated by this channel are valid.
    Active,
    /// Channel has been tripped -- capabilities gated by this channel are revoked.
    Tripped {
        /// Reason hash for the revocation (opaque to the channel).
        reason: [u8; 32],
        /// Height (or timestamp) at which the channel was tripped.
        tripped_at: u64,
    },
}

impl ChannelState {
    /// Returns true if the channel is active (not tripped).
    pub fn is_active(&self) -> bool {
        matches!(self, ChannelState::Active)
    }

    /// Returns true if the channel has been tripped.
    pub fn is_tripped(&self) -> bool {
        matches!(self, ChannelState::Tripped { .. })
    }
}

/// A revocation channel: tracks the revocation state for a set of subscribers.
///
/// This is the in-process data structure that provides O(1) lookup for whether a
/// capability has been revoked via its channel. The network broadcast and federation
/// attestation are handled separately by the `net` layer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevocationChannel {
    /// Unique channel identifier.
    pub channel_id: ChannelId,
    /// The cell authorized to trip this channel.
    pub revoker: CellId,
    /// Current state of the channel.
    pub state: ChannelState,
    /// Cells subscribed to this channel.
    pub subscribers: Vec<CellId>,
    /// When the channel was created (height or timestamp).
    pub created_at: u64,
}

impl RevocationChannel {
    /// Create a new active revocation channel.
    ///
    /// The `channel_id` is derived deterministically from the revoker and a nonce:
    /// `BLAKE3("pyana-revocation-channel" || revoker.as_bytes() || nonce.to_le_bytes())`
    pub fn new(revoker: CellId, nonce: u64, created_at: u64) -> Self {
        let channel_id = Self::derive_channel_id(&revoker, nonce);
        RevocationChannel {
            channel_id,
            revoker,
            state: ChannelState::Active,
            subscribers: Vec::new(),
            created_at,
        }
    }

    /// Create a channel with an explicit channel_id (for reconstitution from storage).
    pub fn from_parts(
        channel_id: ChannelId,
        revoker: CellId,
        state: ChannelState,
        subscribers: Vec<CellId>,
        created_at: u64,
    ) -> Self {
        RevocationChannel {
            channel_id,
            revoker,
            state,
            subscribers,
            created_at,
        }
    }

    /// Derive a channel ID from revoker identity and nonce.
    pub fn derive_channel_id(revoker: &CellId, nonce: u64) -> ChannelId {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-revocation-channel");
        hasher.update(revoker.as_bytes());
        hasher.update(&nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Trip the channel, revoking all capabilities gated by it.
    ///
    /// Only the authorized revoker can trip the channel. Returns `Err` if the
    /// caller is not the revoker or the channel is already tripped.
    pub fn trip(
        &mut self,
        caller: &CellId,
        reason: [u8; 32],
        at_height: u64,
    ) -> Result<(), RevocationChannelError> {
        if caller != &self.revoker {
            return Err(RevocationChannelError::NotAuthorized {
                caller: *caller,
                revoker: self.revoker,
            });
        }
        if self.state.is_tripped() {
            return Err(RevocationChannelError::AlreadyTripped {
                channel_id: self.channel_id,
            });
        }
        self.state = ChannelState::Tripped {
            reason,
            tripped_at: at_height,
        };
        Ok(())
    }

    /// Subscribe a cell to this channel.
    ///
    /// Idempotent: if the cell is already subscribed, this is a no-op.
    pub fn subscribe(&mut self, cell: CellId) {
        if !self.subscribers.contains(&cell) {
            self.subscribers.push(cell);
        }
    }

    /// Unsubscribe a cell from this channel.
    pub fn unsubscribe(&mut self, cell: &CellId) {
        self.subscribers.retain(|s| s != cell);
    }

    /// Check if this channel is active (not tripped).
    pub fn is_active(&self) -> bool {
        self.state.is_active()
    }

    /// Check if a specific cell is subscribed to this channel.
    pub fn is_subscriber(&self, cell: &CellId) -> bool {
        self.subscribers.contains(cell)
    }
}

/// The RevocationChannelSet: an in-process registry of all active revocation channels.
///
/// This provides O(1) lookup by channel_id to determine if a capability gated by
/// a given channel has been revoked. The executor queries this set during
/// `ExerciseViaCapability` and delegation access checks.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RevocationChannelSet {
    /// Channels indexed by their ID for O(1) lookup.
    channels: HashMap<ChannelId, RevocationChannel>,
}

impl RevocationChannelSet {
    /// Create an empty channel set.
    pub fn new() -> Self {
        Self {
            channels: HashMap::new(),
        }
    }

    /// Register a new revocation channel.
    ///
    /// Returns the channel_id on success, or an error if a channel with that ID
    /// already exists.
    pub fn register(
        &mut self,
        channel: RevocationChannel,
    ) -> Result<ChannelId, RevocationChannelError> {
        let id = channel.channel_id;
        if self.channels.contains_key(&id) {
            return Err(RevocationChannelError::ChannelAlreadyExists { channel_id: id });
        }
        self.channels.insert(id, channel);
        Ok(id)
    }

    /// Look up a channel by ID.
    pub fn get(&self, channel_id: &ChannelId) -> Option<&RevocationChannel> {
        self.channels.get(channel_id)
    }

    /// Look up a channel mutably by ID.
    pub fn get_mut(&mut self, channel_id: &ChannelId) -> Option<&mut RevocationChannel> {
        self.channels.get_mut(channel_id)
    }

    /// Check if a channel is active (not tripped). Returns:
    /// - `Ok(true)` if the channel exists and is active.
    /// - `Ok(false)` if the channel exists and is tripped.
    /// - `Err(ChannelNotFound)` if the channel does not exist.
    pub fn is_channel_active(
        &self,
        channel_id: &ChannelId,
    ) -> Result<bool, RevocationChannelError> {
        match self.channels.get(channel_id) {
            Some(ch) => Ok(ch.is_active()),
            None => Err(RevocationChannelError::ChannelNotFound {
                channel_id: *channel_id,
            }),
        }
    }

    /// Check if a capability gated by `channel_id` can be exercised.
    ///
    /// This is the main query the executor uses. It checks:
    /// 1. Does the channel exist?
    /// 2. Is the channel active (not tripped)?
    /// 3. Is the staleness window still valid (if `last_checked_at` and `max_staleness` provided)?
    ///
    /// Returns `Ok(())` if the capability may be exercised, or an error describing why not.
    pub fn check_exercise_permitted(
        &self,
        channel_id: &ChannelId,
        now: u64,
        last_checked_at: u64,
        max_staleness: u64,
    ) -> Result<(), RevocationChannelError> {
        let channel =
            self.channels
                .get(channel_id)
                .ok_or(RevocationChannelError::ChannelNotFound {
                    channel_id: *channel_id,
                })?;

        match &channel.state {
            ChannelState::Active => {
                // Channel is active. If max_staleness > 0 and the subject's last check
                // is within the staleness window, they can act freely.
                // If max_staleness == 0, the subject must always have a fresh check
                // (we accept if `last_checked_at == now`).
                if max_staleness == 0 {
                    // "always check" mode: the last_checked_at must be the current time.
                    // In practice this means the subject just refreshed.
                    if last_checked_at < now {
                        return Err(RevocationChannelError::StaleChannelCheck {
                            channel_id: *channel_id,
                            last_checked_at,
                            max_staleness,
                            now,
                        });
                    }
                } else if now.saturating_sub(last_checked_at) > max_staleness {
                    return Err(RevocationChannelError::StaleChannelCheck {
                        channel_id: *channel_id,
                        last_checked_at,
                        max_staleness,
                        now,
                    });
                }
                Ok(())
            }
            ChannelState::Tripped { tripped_at, .. } => {
                Err(RevocationChannelError::ChannelTripped {
                    channel_id: *channel_id,
                    tripped_at: *tripped_at,
                })
            }
        }
    }

    /// Trip a channel. Only the authorized revoker may do this.
    pub fn trip_channel(
        &mut self,
        channel_id: &ChannelId,
        caller: &CellId,
        reason: [u8; 32],
        at_height: u64,
    ) -> Result<(), RevocationChannelError> {
        let channel =
            self.channels
                .get_mut(channel_id)
                .ok_or(RevocationChannelError::ChannelNotFound {
                    channel_id: *channel_id,
                })?;
        channel.trip(caller, reason, at_height)
    }

    /// Subscribe a cell to a channel.
    pub fn subscribe(
        &mut self,
        channel_id: &ChannelId,
        cell: CellId,
    ) -> Result<(), RevocationChannelError> {
        let channel =
            self.channels
                .get_mut(channel_id)
                .ok_or(RevocationChannelError::ChannelNotFound {
                    channel_id: *channel_id,
                })?;
        channel.subscribe(cell);
        Ok(())
    }

    /// Number of channels in the set.
    pub fn len(&self) -> usize {
        self.channels.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.channels.is_empty()
    }

    /// Iterate over all channels.
    pub fn iter(&self) -> impl Iterator<Item = (&ChannelId, &RevocationChannel)> {
        self.channels.iter()
    }

    /// Remove a channel from the set (e.g., after all subscribers have been notified
    /// and the channel is no longer needed).
    pub fn remove(&mut self, channel_id: &ChannelId) -> Option<RevocationChannel> {
        self.channels.remove(channel_id)
    }
}

/// Errors that can occur when operating on revocation channels.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RevocationChannelError {
    /// The caller is not authorized to trip this channel.
    NotAuthorized { caller: CellId, revoker: CellId },
    /// The channel has already been tripped.
    AlreadyTripped { channel_id: ChannelId },
    /// The channel does not exist in the set.
    ChannelNotFound { channel_id: ChannelId },
    /// A channel with this ID already exists.
    ChannelAlreadyExists { channel_id: ChannelId },
    /// The channel is tripped -- the capability is revoked.
    ChannelTripped {
        channel_id: ChannelId,
        tripped_at: u64,
    },
    /// The subject's last channel check is too stale.
    StaleChannelCheck {
        channel_id: ChannelId,
        last_checked_at: u64,
        max_staleness: u64,
        now: u64,
    },
}

impl core::fmt::Display for RevocationChannelError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RevocationChannelError::NotAuthorized { caller, revoker } => {
                write!(
                    f,
                    "not authorized: caller {caller} is not the revoker {revoker}"
                )
            }
            RevocationChannelError::AlreadyTripped { channel_id } => {
                write!(
                    f,
                    "channel already tripped: {:02x}{:02x}...",
                    channel_id[0], channel_id[1]
                )
            }
            RevocationChannelError::ChannelNotFound { channel_id } => {
                write!(
                    f,
                    "channel not found: {:02x}{:02x}...",
                    channel_id[0], channel_id[1]
                )
            }
            RevocationChannelError::ChannelAlreadyExists { channel_id } => {
                write!(
                    f,
                    "channel already exists: {:02x}{:02x}...",
                    channel_id[0], channel_id[1]
                )
            }
            RevocationChannelError::ChannelTripped {
                channel_id,
                tripped_at,
            } => {
                write!(
                    f,
                    "channel {:02x}{:02x}... tripped at height {tripped_at}",
                    channel_id[0], channel_id[1]
                )
            }
            RevocationChannelError::StaleChannelCheck {
                channel_id,
                last_checked_at,
                max_staleness,
                now,
            } => {
                write!(
                    f,
                    "stale channel check for {:02x}{:02x}...: last_checked_at={last_checked_at}, \
                     max_staleness={max_staleness}, now={now}",
                    channel_id[0], channel_id[1]
                )
            }
        }
    }
}

impl std::error::Error for RevocationChannelError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(37);
        let mut token = [0u8; 32];
        token[0] = seed;
        token[1] = 0xAA;
        CellId::derive_raw(&pk, &token)
    }

    #[test]
    fn test_channel_creation_and_id_derivation() {
        let revoker = make_cell_id(1);
        let ch = RevocationChannel::new(revoker, 0, 100);

        assert_eq!(ch.revoker, revoker);
        assert!(ch.is_active());
        assert!(ch.subscribers.is_empty());
        assert_eq!(ch.created_at, 100);

        // ID should be deterministic.
        let expected_id = RevocationChannel::derive_channel_id(&revoker, 0);
        assert_eq!(ch.channel_id, expected_id);

        // Different nonce -> different ID.
        let ch2 = RevocationChannel::new(revoker, 1, 100);
        assert_ne!(ch.channel_id, ch2.channel_id);
    }

    #[test]
    fn test_trip_channel() {
        let revoker = make_cell_id(1);
        let mut ch = RevocationChannel::new(revoker, 0, 100);

        let reason = [0xABu8; 32];
        assert!(ch.trip(&revoker, reason, 200).is_ok());
        assert!(ch.state.is_tripped());

        match &ch.state {
            ChannelState::Tripped {
                reason: r,
                tripped_at,
            } => {
                assert_eq!(*r, reason);
                assert_eq!(*tripped_at, 200);
            }
            _ => panic!("expected Tripped state"),
        }
    }

    #[test]
    fn test_trip_unauthorized() {
        let revoker = make_cell_id(1);
        let imposter = make_cell_id(2);
        let mut ch = RevocationChannel::new(revoker, 0, 100);

        let result = ch.trip(&imposter, [0u8; 32], 200);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::NotAuthorized { .. }
        ));
        assert!(ch.is_active()); // unchanged
    }

    #[test]
    fn test_trip_already_tripped() {
        let revoker = make_cell_id(1);
        let mut ch = RevocationChannel::new(revoker, 0, 100);

        ch.trip(&revoker, [0u8; 32], 200).unwrap();
        let result = ch.trip(&revoker, [1u8; 32], 300);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::AlreadyTripped { .. }
        ));
    }

    #[test]
    fn test_subscribe_and_unsubscribe() {
        let revoker = make_cell_id(1);
        let subject_a = make_cell_id(2);
        let subject_b = make_cell_id(3);
        let mut ch = RevocationChannel::new(revoker, 0, 100);

        ch.subscribe(subject_a);
        ch.subscribe(subject_b);
        assert!(ch.is_subscriber(&subject_a));
        assert!(ch.is_subscriber(&subject_b));
        assert_eq!(ch.subscribers.len(), 2);

        // Idempotent.
        ch.subscribe(subject_a);
        assert_eq!(ch.subscribers.len(), 2);

        ch.unsubscribe(&subject_a);
        assert!(!ch.is_subscriber(&subject_a));
        assert!(ch.is_subscriber(&subject_b));
    }

    #[test]
    fn test_channel_set_register_and_lookup() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();
        assert!(set.is_empty());

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        assert_eq!(set.len(), 1);
        assert!(set.get(&channel_id).is_some());
        assert!(set.is_channel_active(&channel_id).unwrap());
    }

    #[test]
    fn test_channel_set_duplicate_register() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        set.register(ch.clone()).unwrap();

        let result = set.register(ch);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::ChannelAlreadyExists { .. }
        ));
    }

    #[test]
    fn test_check_exercise_permitted_active() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        // Within staleness window.
        assert!(set
            .check_exercise_permitted(&channel_id, 150, 140, 60)
            .is_ok());

        // Exactly at the boundary.
        assert!(set
            .check_exercise_permitted(&channel_id, 200, 140, 60)
            .is_ok());
    }

    #[test]
    fn test_check_exercise_permitted_stale() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        // Beyond staleness window.
        let result = set.check_exercise_permitted(&channel_id, 250, 140, 60);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::StaleChannelCheck { .. }
        ));
    }

    #[test]
    fn test_check_exercise_permitted_tripped() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        // Trip the channel.
        set.trip_channel(&channel_id, &revoker, [0xFFu8; 32], 200)
            .unwrap();

        // Even with a fresh check, exercise is denied.
        let result = set.check_exercise_permitted(&channel_id, 200, 200, 60);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::ChannelTripped { .. }
        ));
    }

    #[test]
    fn test_check_exercise_channel_not_found() {
        let set = RevocationChannelSet::new();
        let fake_id = [0xDDu8; 32];

        let result = set.check_exercise_permitted(&fake_id, 100, 100, 60);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            RevocationChannelError::ChannelNotFound { .. }
        ));
    }

    #[test]
    fn test_zero_staleness_requires_current_check() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        // max_staleness=0 means "always check". last_checked_at must equal now.
        assert!(set
            .check_exercise_permitted(&channel_id, 200, 200, 0)
            .is_ok());

        // Even 1 unit behind is stale.
        let result = set.check_exercise_permitted(&channel_id, 200, 199, 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_channel_set_remove() {
        let revoker = make_cell_id(1);
        let mut set = RevocationChannelSet::new();

        let ch = RevocationChannel::new(revoker, 0, 100);
        let channel_id = ch.channel_id;
        set.register(ch).unwrap();

        let removed = set.remove(&channel_id);
        assert!(removed.is_some());
        assert!(set.is_empty());
        assert!(set.get(&channel_id).is_none());
    }
}
