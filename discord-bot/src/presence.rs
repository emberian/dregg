//! Presence tracking and cryptographic attestation system.
//!
//! Tracks Discord presence updates (online/idle/dnd/offline) and issues signed
//! attestations that can be used as dischargeable caveats in pyana's capability model.

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

/// Current presence status as observed by the bot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PresenceStatus {
    Online,
    Idle,
    Dnd,
    Offline,
}

impl PresenceStatus {
    /// Whether this status counts as "online" for attestation purposes.
    /// Online, Idle, and Dnd all count — only Offline does not.
    pub fn is_online(self) -> bool {
        !matches!(self, PresenceStatus::Offline)
    }
}

impl std::fmt::Display for PresenceStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PresenceStatus::Online => write!(f, "Online"),
            PresenceStatus::Idle => write!(f, "Idle"),
            PresenceStatus::Dnd => write!(f, "Do Not Disturb"),
            PresenceStatus::Offline => write!(f, "Offline"),
        }
    }
}

/// A record of a user's presence state.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresenceRecord {
    pub user_id: u64,
    pub status: PresenceStatus,
    /// Unix timestamp when the user was last observed online (or None if never seen).
    pub last_online: Option<i64>,
    /// Unix timestamp when the status last changed.
    pub last_changed: i64,
    /// Cumulative seconds online in the current session (resets on offline->online transition).
    pub online_duration_secs: u64,
    /// Timestamp when the current online session started (None if offline).
    session_start: Option<i64>,
}

/// What is being attested about a user's presence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PresenceClaim {
    /// User is currently online right now.
    CurrentlyOnline,
    /// User was online at a specific timestamp.
    WasOnlineAt { timestamp: i64 },
    /// User has been online for at least N seconds continuously.
    OnlineForAtLeast { duration_secs: u64 },
    /// User was online within the last N seconds.
    OnlineWithin { window_secs: u64 },
}

impl std::fmt::Display for PresenceClaim {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PresenceClaim::CurrentlyOnline => write!(f, "CurrentlyOnline"),
            PresenceClaim::WasOnlineAt { timestamp } => write!(f, "WasOnlineAt({timestamp})"),
            PresenceClaim::OnlineForAtLeast { duration_secs } => {
                write!(f, "OnlineForAtLeast({duration_secs}s)")
            }
            PresenceClaim::OnlineWithin { window_secs } => {
                write!(f, "OnlineWithin({window_secs}s)")
            }
        }
    }
}

/// A signed attestation of a user's presence.
///
/// Self-contained and verifiable without contacting the bot — just check the
/// BLAKE3-keyed MAC against the bot's public signing key.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresenceAttestation {
    /// The Discord user ID this attests.
    pub user_id: u64,
    /// The user's pyana cell ID (derived from their wallet).
    pub cell_id: [u8; 32],
    /// What is being attested.
    pub claim: PresenceClaim,
    /// Unix timestamp when this attestation was issued.
    pub issued_at: i64,
    /// Unix timestamp when this attestation expires.
    pub expires_at: i64,
    /// BLAKE3-keyed MAC over the attestation content.
    pub signature: [u8; 32],
}

impl PresenceAttestation {
    /// Serialize the attestation to hex for transport.
    pub fn to_hex(&self) -> String {
        let bytes = self.to_bytes();
        hex::encode(bytes)
    }

    /// Deserialize an attestation from hex.
    pub fn from_hex(s: &str) -> Option<Self> {
        let bytes = hex::decode(s).ok()?;
        Self::from_bytes(&bytes)
    }

    /// Serialize to a compact binary format.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(128);
        buf.extend_from_slice(&self.user_id.to_le_bytes());
        buf.extend_from_slice(&self.cell_id);
        // Encode claim type + data
        match &self.claim {
            PresenceClaim::CurrentlyOnline => {
                buf.push(0);
            }
            PresenceClaim::WasOnlineAt { timestamp } => {
                buf.push(1);
                buf.extend_from_slice(&timestamp.to_le_bytes());
            }
            PresenceClaim::OnlineForAtLeast { duration_secs } => {
                buf.push(2);
                buf.extend_from_slice(&duration_secs.to_le_bytes());
            }
            PresenceClaim::OnlineWithin { window_secs } => {
                buf.push(3);
                buf.extend_from_slice(&window_secs.to_le_bytes());
            }
        }
        buf.extend_from_slice(&self.issued_at.to_le_bytes());
        buf.extend_from_slice(&self.expires_at.to_le_bytes());
        buf.extend_from_slice(&self.signature);
        buf
    }

    /// Deserialize from compact binary format.
    pub fn from_bytes(data: &[u8]) -> Option<Self> {
        if data.len() < 8 + 32 + 1 + 8 + 8 + 32 {
            return None;
        }
        let mut pos = 0;

        let user_id = u64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;

        let cell_id: [u8; 32] = data[pos..pos + 32].try_into().ok()?;
        pos += 32;

        let claim_type = data[pos];
        pos += 1;

        let claim = match claim_type {
            0 => PresenceClaim::CurrentlyOnline,
            1 => {
                if data.len() < pos + 8 + 8 + 8 + 32 {
                    return None;
                }
                let timestamp = i64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
                pos += 8;
                PresenceClaim::WasOnlineAt { timestamp }
            }
            2 => {
                if data.len() < pos + 8 + 8 + 8 + 32 {
                    return None;
                }
                let duration_secs = u64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
                pos += 8;
                PresenceClaim::OnlineForAtLeast { duration_secs }
            }
            3 => {
                if data.len() < pos + 8 + 8 + 8 + 32 {
                    return None;
                }
                let window_secs = u64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
                pos += 8;
                PresenceClaim::OnlineWithin { window_secs }
            }
            _ => return None,
        };

        if data.len() < pos + 8 + 8 + 32 {
            return None;
        }

        let issued_at = i64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;
        let expires_at = i64::from_le_bytes(data[pos..pos + 8].try_into().ok()?);
        pos += 8;
        let signature: [u8; 32] = data[pos..pos + 32].try_into().ok()?;

        Some(Self {
            user_id,
            cell_id,
            claim,
            issued_at,
            expires_at,
            signature,
        })
    }

    /// Compute the content hash (the message that gets signed).
    fn content_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(96);
        buf.extend_from_slice(&self.user_id.to_le_bytes());
        buf.extend_from_slice(&self.cell_id);
        match &self.claim {
            PresenceClaim::CurrentlyOnline => buf.push(0),
            PresenceClaim::WasOnlineAt { timestamp } => {
                buf.push(1);
                buf.extend_from_slice(&timestamp.to_le_bytes());
            }
            PresenceClaim::OnlineForAtLeast { duration_secs } => {
                buf.push(2);
                buf.extend_from_slice(&duration_secs.to_le_bytes());
            }
            PresenceClaim::OnlineWithin { window_secs } => {
                buf.push(3);
                buf.extend_from_slice(&window_secs.to_le_bytes());
            }
        }
        buf.extend_from_slice(&self.issued_at.to_le_bytes());
        buf.extend_from_slice(&self.expires_at.to_le_bytes());
        buf
    }

    /// Verify this attestation's signature against a signing key.
    pub fn verify(&self, signing_key: &[u8; 32]) -> bool {
        let content = self.content_bytes();
        let expected = blake3::keyed_hash(signing_key, &content);
        self.signature == *expected.as_bytes()
    }
}

/// A caveat that requires presence attestation for discharge.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresenceCaveat {
    /// The bot's signing key (public — used to verify attestations).
    pub bot_key: [u8; 32],
    /// The required claim type.
    pub required_claim: PresenceClaim,
    /// The user/cell this caveat applies to.
    pub user_id: u64,
    pub cell_id: [u8; 32],
}

/// Check if a presence attestation satisfies a caveat.
pub fn discharge_presence_caveat(
    attestation: &PresenceAttestation,
    caveat: &PresenceCaveat,
    current_time: i64,
) -> bool {
    // 1. Verify signature against bot key
    if !attestation.verify(&caveat.bot_key) {
        return false;
    }

    // 2. Check not expired
    if attestation.expires_at < current_time {
        return false;
    }

    // 3. Check user/cell match
    if attestation.user_id != caveat.user_id || attestation.cell_id != caveat.cell_id {
        return false;
    }

    // 4. Check claim satisfies requirement
    claim_satisfies(&attestation.claim, &caveat.required_claim)
}

/// Check whether an attested claim satisfies a required claim.
fn claim_satisfies(attested: &PresenceClaim, required: &PresenceClaim) -> bool {
    match (attested, required) {
        // Exact match always works
        (a, b) if a == b => true,
        // CurrentlyOnline satisfies OnlineWithin for any window
        (PresenceClaim::CurrentlyOnline, PresenceClaim::OnlineWithin { .. }) => true,
        // OnlineForAtLeast(N) satisfies OnlineForAtLeast(M) if N >= M
        (
            PresenceClaim::OnlineForAtLeast {
                duration_secs: attested_dur,
            },
            PresenceClaim::OnlineForAtLeast {
                duration_secs: required_dur,
            },
        ) => attested_dur >= required_dur,
        // OnlineWithin(N) satisfies OnlineWithin(M) if N <= M (tighter window is stronger)
        (
            PresenceClaim::OnlineWithin {
                window_secs: attested_window,
            },
            PresenceClaim::OnlineWithin {
                window_secs: required_window,
            },
        ) => attested_window <= required_window,
        // CurrentlyOnline does NOT satisfy OnlineForAtLeast (different semantic)
        (PresenceClaim::CurrentlyOnline, PresenceClaim::OnlineForAtLeast { .. }) => false,
        _ => false,
    }
}

/// Rate limiter for attestation requests.
struct RateLimiter {
    /// Last attestation time per user (unix timestamp).
    last_attestation: HashMap<u64, i64>,
    /// Minimum interval between attestations in seconds.
    min_interval_secs: i64,
}

impl RateLimiter {
    fn new(min_interval_secs: i64) -> Self {
        Self {
            last_attestation: HashMap::new(),
            min_interval_secs,
        }
    }

    fn check_and_record(&mut self, user_id: u64, now: i64) -> Result<(), i64> {
        if let Some(&last) = self.last_attestation.get(&user_id) {
            let elapsed = now - last;
            if elapsed < self.min_interval_secs {
                return Err(self.min_interval_secs - elapsed);
            }
        }
        self.last_attestation.insert(user_id, now);
        Ok(())
    }
}

/// History entry for a presence change.
#[derive(Clone, Debug)]
pub struct PresenceHistoryEntry {
    pub user_id: u64,
    pub status: PresenceStatus,
    pub timestamp: i64,
}

/// The main presence tracker. Maintains per-user presence state and issues attestations.
pub struct PresenceTracker {
    /// Last known status per user.
    statuses: HashMap<u64, PresenceRecord>,
    /// Bot secret for signing attestations (BLAKE3 keyed MAC).
    signing_key: [u8; 32],
    /// Rate limiter for attestation requests.
    rate_limiter: RateLimiter,
    /// Default attestation TTL in seconds.
    default_ttl_secs: i64,
    /// Presence change history (ring buffer, last 24h).
    history: Vec<PresenceHistoryEntry>,
    /// Max history entries to retain.
    max_history: usize,
    /// Optional channel ID to post presence notifications to.
    pub notification_channel: Option<u64>,
}

impl PresenceTracker {
    /// Create a new presence tracker with the given signing key.
    pub fn new(signing_key: [u8; 32]) -> Self {
        Self {
            statuses: HashMap::new(),
            signing_key,
            rate_limiter: RateLimiter::new(60), // 1 attestation per minute
            default_ttl_secs: 300,              // 5 minute expiry
            history: Vec::new(),
            max_history: 10_000,
            notification_channel: None,
        }
    }

    /// Create with custom TTL and rate limit.
    #[allow(dead_code)]
    pub fn with_config(signing_key: [u8; 32], rate_limit_secs: i64, default_ttl_secs: i64) -> Self {
        Self {
            statuses: HashMap::new(),
            signing_key,
            rate_limiter: RateLimiter::new(rate_limit_secs),
            default_ttl_secs,
            history: Vec::new(),
            max_history: 10_000,
            notification_channel: None,
        }
    }

    /// Get the current unix timestamp.
    fn now() -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    }

    /// Update presence for a user. Called on every Discord PresenceUpdate event.
    ///
    /// Returns the previous status (if any) and the new status.
    pub fn update(
        &mut self,
        user_id: u64,
        new_status: PresenceStatus,
    ) -> (Option<PresenceStatus>, PresenceStatus) {
        let now = Self::now();
        let old_status = self.statuses.get(&user_id).map(|r| r.status);

        let record = self
            .statuses
            .entry(user_id)
            .or_insert_with(|| PresenceRecord {
                user_id,
                status: PresenceStatus::Offline,
                last_online: None,
                last_changed: now,
                online_duration_secs: 0,
                session_start: None,
            });

        // If status didn't change, nothing to do.
        if record.status == new_status {
            return (old_status, new_status);
        }

        let old = record.status;

        // Accumulate online duration if transitioning away from online.
        if old.is_online() {
            if let Some(start) = record.session_start {
                let duration = (now - start).max(0) as u64;
                record.online_duration_secs += duration;
            }
        }

        // Update the record.
        record.status = new_status;
        record.last_changed = now;

        if new_status.is_online() {
            record.last_online = Some(now);
            if !old.is_online() {
                // Starting a new online session.
                record.online_duration_secs = 0;
                record.session_start = Some(now);
            }
        } else {
            // Going offline.
            record.session_start = None;
        }

        // Record in history.
        self.history.push(PresenceHistoryEntry {
            user_id,
            status: new_status,
            timestamp: now,
        });
        if self.history.len() > self.max_history {
            let drop_count = self.max_history / 10;
            self.history.drain(..drop_count);
        }

        (old_status, new_status)
    }

    /// Get the presence record for a user.
    #[allow(dead_code)]
    pub fn get(&self, user_id: u64) -> Option<&PresenceRecord> {
        self.statuses.get(&user_id)
    }

    /// Get a snapshot of the current record with up-to-date duration.
    pub fn get_snapshot(&self, user_id: u64) -> Option<PresenceRecord> {
        let record = self.statuses.get(&user_id)?;
        let mut snapshot = record.clone();

        // If currently online, add elapsed time to duration.
        if record.status.is_online() {
            if let Some(start) = record.session_start {
                let now = Self::now();
                let elapsed = (now - start).max(0) as u64;
                snapshot.online_duration_secs += elapsed;
            }
        }

        Some(snapshot)
    }

    /// Get presence history for a user in the last N seconds.
    pub fn history(&self, user_id: u64, window_secs: i64) -> Vec<&PresenceHistoryEntry> {
        let cutoff = Self::now() - window_secs;
        self.history
            .iter()
            .filter(|e| e.user_id == user_id && e.timestamp >= cutoff)
            .collect()
    }

    /// Issue a presence attestation for a user.
    pub fn attest(
        &mut self,
        user_id: u64,
        cell_id: [u8; 32],
        claim: PresenceClaim,
    ) -> Result<PresenceAttestation, String> {
        let now = Self::now();

        // Rate limit check.
        if let Err(wait_secs) = self.rate_limiter.check_and_record(user_id, now) {
            return Err(format!("Rate limited. Try again in {wait_secs} second(s)."));
        }

        // Validate the claim against current state.
        self.validate_claim(user_id, &claim, now)?;

        // Build and sign the attestation.
        let attestation = self.sign_attestation(user_id, cell_id, claim, now);
        Ok(attestation)
    }

    /// Issue an attestation without rate limiting (for internal/testing use).
    #[allow(dead_code)]
    pub fn attest_unchecked(
        &self,
        user_id: u64,
        cell_id: [u8; 32],
        claim: PresenceClaim,
    ) -> Result<PresenceAttestation, String> {
        let now = Self::now();
        self.validate_claim(user_id, &claim, now)?;
        Ok(self.sign_attestation(user_id, cell_id, claim, now))
    }

    /// Validate that the bot can truthfully attest to the given claim.
    fn validate_claim(&self, user_id: u64, claim: &PresenceClaim, now: i64) -> Result<(), String> {
        let record = self.statuses.get(&user_id).ok_or_else(|| {
            "No presence data for this user. The bot has not seen you online yet.".to_string()
        })?;

        match claim {
            PresenceClaim::CurrentlyOnline => {
                if !record.status.is_online() {
                    return Err(format!(
                        "You are currently {}. Cannot attest CurrentlyOnline.",
                        record.status
                    ));
                }
            }
            PresenceClaim::WasOnlineAt { timestamp } => {
                if *timestamp > now {
                    return Err("Cannot attest future timestamps.".to_string());
                }
                match record.last_online {
                    Some(last) if last >= *timestamp => {}
                    _ => {
                        return Err(
                            "Cannot attest: the bot did not observe you online at that time."
                                .to_string(),
                        );
                    }
                }
            }
            PresenceClaim::OnlineForAtLeast { duration_secs } => {
                if !record.status.is_online() {
                    return Err("You are not currently online.".to_string());
                }
                let session_dur = match record.session_start {
                    Some(start) => (now - start).max(0) as u64,
                    None => 0,
                };
                let total = record.online_duration_secs + session_dur;
                if total < *duration_secs {
                    return Err(format!(
                        "Online for {total}s, but {duration_secs}s required."
                    ));
                }
            }
            PresenceClaim::OnlineWithin { window_secs } => match record.last_online {
                Some(last) if (now - last) <= *window_secs as i64 => {}
                _ => {
                    return Err(format!(
                        "Not seen online within the last {window_secs} seconds."
                    ));
                }
            },
        }

        Ok(())
    }

    /// Create and sign an attestation.
    fn sign_attestation(
        &self,
        user_id: u64,
        cell_id: [u8; 32],
        claim: PresenceClaim,
        now: i64,
    ) -> PresenceAttestation {
        let issued_at = now;
        let expires_at = now + self.default_ttl_secs;

        let mut attestation = PresenceAttestation {
            user_id,
            cell_id,
            claim,
            issued_at,
            expires_at,
            signature: [0u8; 32],
        };

        // Sign: BLAKE3 keyed MAC over the content.
        let content = attestation.content_bytes();
        let mac = blake3::keyed_hash(&self.signing_key, &content);
        attestation.signature = *mac.as_bytes();

        attestation
    }

    /// Verify an attestation against this tracker's signing key.
    pub fn verify_attestation(&self, attestation: &PresenceAttestation) -> bool {
        attestation.verify(&self.signing_key)
    }

    /// Get the bot's cell ID (derived from signing key with a special path).
    #[allow(dead_code)]
    pub fn bot_cell_id(&self) -> [u8; 32] {
        blake3::derive_key("pyana-presence-bot-cell-v1", &self.signing_key)
    }

    /// Get the signing key (for external verifiers to use).
    #[allow(dead_code)]
    pub fn signing_key(&self) -> &[u8; 32] {
        &self.signing_key
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_key() -> [u8; 32] {
        blake3::derive_key("test-presence-key", b"test-secret")
    }

    fn test_cell_id() -> [u8; 32] {
        [0xAB; 32]
    }

    #[test]
    fn test_presence_update_online() {
        let mut tracker = PresenceTracker::new(test_key());

        let (old, new) = tracker.update(12345, PresenceStatus::Online);
        assert_eq!(old, None);
        assert_eq!(new, PresenceStatus::Online);

        let record = tracker.get(12345).unwrap();
        assert_eq!(record.status, PresenceStatus::Online);
        assert!(record.last_online.is_some());
        assert!(record.session_start.is_some());
    }

    #[test]
    fn test_presence_update_offline_then_online() {
        let mut tracker = PresenceTracker::new(test_key());

        tracker.update(12345, PresenceStatus::Offline);
        let record = tracker.get(12345).unwrap();
        assert_eq!(record.status, PresenceStatus::Offline);
        assert!(record.session_start.is_none());

        tracker.update(12345, PresenceStatus::Online);
        let record = tracker.get(12345).unwrap();
        assert_eq!(record.status, PresenceStatus::Online);
        assert!(record.session_start.is_some());
    }

    #[test]
    fn test_attest_currently_online() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        assert_eq!(attestation.user_id, 12345);
        assert_eq!(attestation.cell_id, test_cell_id());
        assert_eq!(attestation.claim, PresenceClaim::CurrentlyOnline);
        assert!(attestation.expires_at > attestation.issued_at);
    }

    #[test]
    fn test_attest_currently_online_fails_when_offline() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Offline);

        let result = tracker.attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Offline"));
    }

    #[test]
    fn test_attest_unknown_user_fails() {
        let mut tracker = PresenceTracker::new(test_key());

        let result = tracker.attest(99999, test_cell_id(), PresenceClaim::CurrentlyOnline);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("No presence data"));
    }

    #[test]
    fn test_attestation_signature_valid() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        assert!(tracker.verify_attestation(&attestation));
        assert!(attestation.verify(&test_key()));
    }

    #[test]
    fn test_attestation_signature_fails_wrong_key() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let wrong_key = [0xFF; 32];
        assert!(!attestation.verify(&wrong_key));
    }

    #[test]
    fn test_attestation_tamper_detection() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let mut attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        // Tamper with the user_id.
        attestation.user_id = 99999;
        assert!(!attestation.verify(&test_key()));
    }

    #[test]
    fn test_attestation_roundtrip_hex() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let hex_str = attestation.to_hex();
        let recovered = PresenceAttestation::from_hex(&hex_str).unwrap();

        assert_eq!(recovered.user_id, attestation.user_id);
        assert_eq!(recovered.cell_id, attestation.cell_id);
        assert_eq!(recovered.claim, attestation.claim);
        assert_eq!(recovered.issued_at, attestation.issued_at);
        assert_eq!(recovered.expires_at, attestation.expires_at);
        assert_eq!(recovered.signature, attestation.signature);
        assert!(recovered.verify(&test_key()));
    }

    #[test]
    fn test_attestation_roundtrip_hex_with_claim_data() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);

        let claims = vec![
            PresenceClaim::CurrentlyOnline,
            PresenceClaim::OnlineWithin { window_secs: 600 },
        ];

        for claim in claims {
            let attestation = tracker
                .attest_unchecked(12345, test_cell_id(), claim.clone())
                .unwrap();
            let hex_str = attestation.to_hex();
            let recovered = PresenceAttestation::from_hex(&hex_str).unwrap();
            assert_eq!(recovered.claim, claim);
            assert!(recovered.verify(&test_key()));
        }
    }

    #[test]
    fn test_rate_limiting() {
        let mut tracker = PresenceTracker::with_config(test_key(), 60, 300);
        tracker.update(12345, PresenceStatus::Online);

        // First attestation should succeed.
        let result = tracker.attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline);
        assert!(result.is_ok());

        // Second attestation within 60s should fail.
        let result = tracker.attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Rate limited"));
    }

    #[test]
    fn test_discharge_caveat_valid() {
        let key = test_key();
        let mut tracker = PresenceTracker::new(key);
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let caveat = PresenceCaveat {
            bot_key: key,
            required_claim: PresenceClaim::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell_id(),
        };

        let now = PresenceTracker::now();
        assert!(discharge_presence_caveat(&attestation, &caveat, now));
    }

    #[test]
    fn test_discharge_caveat_expired() {
        let key = test_key();
        let mut tracker = PresenceTracker::new(key);
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let caveat = PresenceCaveat {
            bot_key: key,
            required_claim: PresenceClaim::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell_id(),
        };

        // Set current time far in the future (past expiry).
        let future = attestation.expires_at + 1000;
        assert!(!discharge_presence_caveat(&attestation, &caveat, future));
    }

    #[test]
    fn test_discharge_caveat_wrong_user() {
        let key = test_key();
        let mut tracker = PresenceTracker::new(key);
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let caveat = PresenceCaveat {
            bot_key: key,
            required_claim: PresenceClaim::CurrentlyOnline,
            user_id: 99999,
            cell_id: test_cell_id(),
        };

        let now = PresenceTracker::now();
        assert!(!discharge_presence_caveat(&attestation, &caveat, now));
    }

    #[test]
    fn test_discharge_caveat_wrong_key() {
        let key = test_key();
        let mut tracker = PresenceTracker::new(key);
        tracker.update(12345, PresenceStatus::Online);

        let attestation = tracker
            .attest(12345, test_cell_id(), PresenceClaim::CurrentlyOnline)
            .unwrap();

        let caveat = PresenceCaveat {
            bot_key: [0xFF; 32],
            required_claim: PresenceClaim::CurrentlyOnline,
            user_id: 12345,
            cell_id: test_cell_id(),
        };

        let now = PresenceTracker::now();
        assert!(!discharge_presence_caveat(&attestation, &caveat, now));
    }

    #[test]
    fn test_claim_satisfies_online_within() {
        assert!(claim_satisfies(
            &PresenceClaim::CurrentlyOnline,
            &PresenceClaim::OnlineWithin { window_secs: 3600 }
        ));
    }

    #[test]
    fn test_claim_satisfies_duration_stronger() {
        assert!(claim_satisfies(
            &PresenceClaim::OnlineForAtLeast {
                duration_secs: 7200
            },
            &PresenceClaim::OnlineForAtLeast {
                duration_secs: 3600
            },
        ));
        assert!(!claim_satisfies(
            &PresenceClaim::OnlineForAtLeast {
                duration_secs: 3600
            },
            &PresenceClaim::OnlineForAtLeast {
                duration_secs: 7200
            },
        ));
    }

    #[test]
    fn test_claim_satisfies_window_tighter() {
        assert!(claim_satisfies(
            &PresenceClaim::OnlineWithin { window_secs: 300 },
            &PresenceClaim::OnlineWithin { window_secs: 600 },
        ));
        assert!(!claim_satisfies(
            &PresenceClaim::OnlineWithin { window_secs: 600 },
            &PresenceClaim::OnlineWithin { window_secs: 300 },
        ));
    }

    #[test]
    fn test_history_tracking() {
        let mut tracker = PresenceTracker::new(test_key());
        tracker.update(12345, PresenceStatus::Online);
        tracker.update(12345, PresenceStatus::Idle);
        tracker.update(12345, PresenceStatus::Offline);

        let history = tracker.history(12345, 86400);
        assert_eq!(history.len(), 3);
        assert_eq!(history[0].status, PresenceStatus::Online);
        assert_eq!(history[1].status, PresenceStatus::Idle);
        assert_eq!(history[2].status, PresenceStatus::Offline);
    }

    #[test]
    fn test_bot_cell_id_deterministic() {
        let tracker = PresenceTracker::new(test_key());
        let id1 = tracker.bot_cell_id();
        let id2 = tracker.bot_cell_id();
        assert_eq!(id1, id2);
        assert_ne!(id1, [0u8; 32]);
    }

    #[test]
    fn test_presence_status_is_online() {
        assert!(PresenceStatus::Online.is_online());
        assert!(PresenceStatus::Idle.is_online());
        assert!(PresenceStatus::Dnd.is_online());
        assert!(!PresenceStatus::Offline.is_online());
    }
}
