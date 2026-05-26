//! Federation boundary enforcement: gossip filtering, rate limiting, and ban list.
//!
//! This module provides the security mechanisms that complement the PeerRole
//! classification in `server.rs`:
//!
//! - **GossipFilter**: Determines which messages a peer may receive based on their role.
//! - **RateLimiter**: Token-bucket rate limiting differentiated by peer role.
//! - **BanList**: Temporary IP/key bans after repeated auth failures or protocol violations.
//! - **AuthConfig**: Extended configuration for `require_auth` mode and related settings.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use tokio::sync::Mutex;

use crate::message::WireMessage;
use crate::server::PeerRole;

// =============================================================================
// Gossip Filter
// =============================================================================

/// Determines whether a given message should be sent to a peer based on their
/// authenticated role.
///
/// # Security Invariant
///
/// - Blocks (state replication): Members ONLY.
/// - CapTP messages: Members and CapTpPeers.
/// - Public messages (ping/pong, attested root requests): Everyone.
/// - All other messages: Members only (fail-closed default).
pub struct GossipFilter;

impl GossipFilter {
    /// Check if a message should be sent to a peer with the given role.
    ///
    /// Returns `true` if the message is appropriate for the peer's role,
    /// `false` if it should be withheld.
    pub fn should_send_to_peer(msg: &WireMessage, role: &PeerRole) -> bool {
        match msg {
            // Public: everyone can receive these
            WireMessage::Ping { .. } | WireMessage::Pong { .. } => true,
            WireMessage::RequestAttestedRoot => true,
            WireMessage::AttestedRoot { .. } => true,
            WireMessage::PresentationResult { .. } => true,
            WireMessage::Error { .. } => true,
            WireMessage::Welcome { .. } => true,
            WireMessage::PeerChallenge { .. }
            | WireMessage::PeerAuthResponse { .. }
            | WireMessage::PeerAuthenticated { .. } => true,
            WireMessage::NonMembershipResponse { .. } => true,
            // Receipt fetch: structured pruning-aware response.
            // Anonymous peers may query; the response is shaped so a
            // verifier can validate it without trusting the operator.
            WireMessage::RequestReceipt { .. } | WireMessage::ReceiptResponse { .. } => true,

            // CapTP: Members and CapTpPeers
            WireMessage::CapHello { .. }
            | WireMessage::CapGoodbye { .. }
            | WireMessage::EnlivenSturdyRef { .. }
            | WireMessage::EnlivenResponse { .. }
            | WireMessage::PipelinedMsg { .. }
            | WireMessage::PresentHandoff { .. }
            | WireMessage::HandoffAccepted { .. }
            | WireMessage::DropRemoteRef { .. } => role.allows_captp(),

            // State replication / blocks: Members only
            WireMessage::SubmitRevocation { .. }
            | WireMessage::RevocationAck { .. }
            | WireMessage::RequestNonMembership { .. } => role.allows_state_replication(),

            // Token presentation: public (Anonymous can present)
            WireMessage::PresentToken { .. } => true,

            // Hello: always allowed (part of handshake)
            WireMessage::Hello { .. } => true,

            // Catch-all: Members only (fail-closed)
            #[allow(unreachable_patterns)]
            _ => role.allows_state_replication(),
        }
    }
}

// =============================================================================
// Rate Limiter
// =============================================================================

/// Per-connection rate limit configuration, differentiated by role.
#[derive(Clone, Debug)]
pub struct RateLimitConfig {
    /// Maximum messages per window for Anonymous peers.
    pub anonymous_max: u32,
    /// Maximum messages per window for CapTP peers.
    pub captp_max: u32,
    /// Maximum messages per window for Members.
    pub member_max: u32,
    /// The time window over which messages are counted.
    pub window: Duration,
}

impl Default for RateLimitConfig {
    fn default() -> Self {
        Self {
            anonymous_max: 20,
            captp_max: 100,
            member_max: 1000,
            window: Duration::from_secs(10),
        }
    }
}

impl RateLimitConfig {
    /// Get the rate limit for a given role.
    pub fn limit_for_role(&self, role: &PeerRole) -> u32 {
        match role {
            PeerRole::Anonymous => self.anonymous_max,
            PeerRole::LightClient => self.anonymous_max,
            PeerRole::CapTpPeer { .. } => self.captp_max,
            PeerRole::Member { .. } => self.member_max,
        }
    }
}

/// A sliding-window rate limiter for a single connection.
///
/// Counts messages within a rolling time window. When the count exceeds
/// the limit, further messages are rejected until the window slides forward.
#[derive(Debug)]
pub struct RateLimiter {
    /// Timestamps of messages within the current window.
    timestamps: Vec<Instant>,
    /// The maximum allowed messages per window.
    max_messages: u32,
    /// The window duration.
    window: Duration,
}

impl RateLimiter {
    /// Create a new rate limiter with the given parameters.
    pub fn new(max_messages: u32, window: Duration) -> Self {
        Self {
            timestamps: Vec::with_capacity(max_messages as usize),
            max_messages,
            window,
        }
    }

    /// Create a rate limiter for a specific role using the given config.
    pub fn for_role(role: &PeerRole, config: &RateLimitConfig) -> Self {
        Self::new(config.limit_for_role(role), config.window)
    }

    /// Attempt to consume one unit. Returns `true` if allowed, `false` if rate-limited.
    pub fn check(&mut self) -> bool {
        let now = Instant::now();
        let cutoff = now - self.window;

        // Remove timestamps outside the window.
        self.timestamps.retain(|t| *t > cutoff);

        if self.timestamps.len() >= self.max_messages as usize {
            false
        } else {
            self.timestamps.push(now);
            true
        }
    }

    /// Update the limit (e.g., after role upgrade from Anonymous to Member).
    pub fn update_limit(&mut self, new_max: u32) {
        self.max_messages = new_max;
    }

    /// Get the current message count within the window.
    pub fn current_count(&self) -> usize {
        let now = Instant::now();
        let cutoff = now - self.window;
        self.timestamps.iter().filter(|t| **t > cutoff).count()
    }
}

// =============================================================================
// Ban List
// =============================================================================

/// Reason for banning a peer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BanReason {
    /// Repeated authentication failures.
    RepeatedAuthFailure { attempts: u32 },
    /// Repeated invalid messages / protocol violations.
    ProtocolViolation { violations: u32 },
    /// Rate limit exceeded persistently.
    RateLimitAbuse,
}

/// A single ban entry.
#[derive(Clone, Debug)]
pub struct BanEntry {
    /// When the ban was imposed.
    pub banned_at: Instant,
    /// How long the ban lasts.
    pub duration: Duration,
    /// Why the peer was banned.
    pub reason: BanReason,
}

impl BanEntry {
    /// Check if this ban has expired.
    pub fn is_expired(&self) -> bool {
        self.banned_at.elapsed() >= self.duration
    }

    /// Remaining time until the ban expires.
    pub fn remaining(&self) -> Duration {
        let elapsed = self.banned_at.elapsed();
        if elapsed >= self.duration {
            Duration::ZERO
        } else {
            self.duration - elapsed
        }
    }
}

/// Configuration for the ban system.
#[derive(Clone, Debug)]
pub struct BanConfig {
    /// Number of auth failures before banning.
    pub max_auth_failures: u32,
    /// Number of protocol violations before banning.
    pub max_protocol_violations: u32,
    /// Duration of ban after auth failures.
    pub auth_failure_ban_duration: Duration,
    /// Duration of ban after protocol violations.
    pub violation_ban_duration: Duration,
    /// Duration of ban after rate limit abuse.
    pub rate_limit_ban_duration: Duration,
}

impl Default for BanConfig {
    fn default() -> Self {
        Self {
            max_auth_failures: 3,
            max_protocol_violations: 10,
            auth_failure_ban_duration: Duration::from_secs(300), // 5 minutes
            violation_ban_duration: Duration::from_secs(600),    // 10 minutes
            rate_limit_ban_duration: Duration::from_secs(60),    // 1 minute
        }
    }
}

/// Tracks failure counts and active bans, keyed by IP address.
///
/// Thread-safe via `Arc<Mutex<..>>` wrapping. The ban list is periodically
/// cleaned of expired entries.
#[derive(Debug)]
pub struct BanList {
    /// Active bans by IP.
    bans: HashMap<IpAddr, BanEntry>,
    /// Auth failure counts by IP (reset on success or ban).
    auth_failures: HashMap<IpAddr, u32>,
    /// Protocol violation counts by IP.
    protocol_violations: HashMap<IpAddr, u32>,
    /// Configuration.
    config: BanConfig,
}

impl BanList {
    /// Create a new ban list with the given configuration.
    pub fn new(config: BanConfig) -> Self {
        Self {
            bans: HashMap::new(),
            auth_failures: HashMap::new(),
            protocol_violations: HashMap::new(),
            config,
        }
    }

    /// Create with default configuration.
    pub fn with_defaults() -> Self {
        Self::new(BanConfig::default())
    }

    /// Check if an IP is currently banned.
    pub fn is_banned(&self, ip: &IpAddr) -> bool {
        match self.bans.get(ip) {
            Some(entry) => !entry.is_expired(),
            None => false,
        }
    }

    /// Get the ban entry for an IP (if banned and not expired).
    pub fn get_ban(&self, ip: &IpAddr) -> Option<&BanEntry> {
        self.bans.get(ip).filter(|e| !e.is_expired())
    }

    /// Record an authentication failure for an IP.
    ///
    /// Returns `true` if the peer is now banned (threshold exceeded).
    pub fn record_auth_failure(&mut self, ip: &IpAddr) -> bool {
        let count = self.auth_failures.entry(*ip).or_insert(0);
        *count += 1;

        if *count >= self.config.max_auth_failures {
            self.bans.insert(
                *ip,
                BanEntry {
                    banned_at: Instant::now(),
                    duration: self.config.auth_failure_ban_duration,
                    reason: BanReason::RepeatedAuthFailure { attempts: *count },
                },
            );
            // Reset counter after banning.
            self.auth_failures.remove(ip);
            true
        } else {
            false
        }
    }

    /// Record a protocol violation for an IP.
    ///
    /// Returns `true` if the peer is now banned (threshold exceeded).
    pub fn record_protocol_violation(&mut self, ip: &IpAddr) -> bool {
        let count = self.protocol_violations.entry(*ip).or_insert(0);
        *count += 1;

        if *count >= self.config.max_protocol_violations {
            self.bans.insert(
                *ip,
                BanEntry {
                    banned_at: Instant::now(),
                    duration: self.config.violation_ban_duration,
                    reason: BanReason::ProtocolViolation { violations: *count },
                },
            );
            self.protocol_violations.remove(ip);
            true
        } else {
            false
        }
    }

    /// Ban an IP for rate limit abuse.
    pub fn ban_for_rate_limit(&mut self, ip: &IpAddr) {
        self.bans.insert(
            *ip,
            BanEntry {
                banned_at: Instant::now(),
                duration: self.config.rate_limit_ban_duration,
                reason: BanReason::RateLimitAbuse,
            },
        );
    }

    /// Record a successful authentication (resets the failure counter for the IP).
    pub fn record_auth_success(&mut self, ip: &IpAddr) {
        self.auth_failures.remove(ip);
    }

    /// Remove expired bans (garbage collection).
    pub fn cleanup_expired(&mut self) {
        self.bans.retain(|_, entry| !entry.is_expired());
    }

    /// Number of currently active (non-expired) bans.
    pub fn active_ban_count(&self) -> usize {
        self.bans.values().filter(|e| !e.is_expired()).count()
    }
}

/// Thread-safe wrapper around the BanList.
pub type SharedBanList = Arc<Mutex<BanList>>;

/// Create a new shared ban list with default configuration.
pub fn new_shared_ban_list() -> SharedBanList {
    Arc::new(Mutex::new(BanList::with_defaults()))
}

/// Create a new shared ban list with custom configuration.
pub fn new_shared_ban_list_with_config(config: BanConfig) -> SharedBanList {
    Arc::new(Mutex::new(BanList::new(config)))
}

// =============================================================================
// Auth Configuration Extension
// =============================================================================

/// Extended authentication configuration for the wire server.
///
/// This supplements `SiloConfig` with settings that control how strictly
/// authentication is enforced.
#[derive(Clone, Debug)]
pub struct AuthConfig {
    /// When true, connections that fail authentication are DROPPED immediately
    /// (not just classified as Anonymous). This is the production mode.
    ///
    /// When false (default, backward-compatible), failed auth peers remain
    /// connected as Anonymous with limited access.
    pub require_auth: bool,

    /// Rate limit configuration (differentiated by role).
    pub rate_limits: RateLimitConfig,

    /// Ban list configuration.
    pub ban_config: BanConfig,
}

impl Default for AuthConfig {
    fn default() -> Self {
        Self {
            require_auth: false,
            rate_limits: RateLimitConfig::default(),
            ban_config: BanConfig::default(),
        }
    }
}

impl AuthConfig {
    /// Create a strict production configuration.
    pub fn strict() -> Self {
        Self {
            require_auth: true,
            rate_limits: RateLimitConfig::default(),
            ban_config: BanConfig::default(),
        }
    }

    /// Builder: set require_auth.
    pub fn with_require_auth(mut self, require: bool) -> Self {
        self.require_auth = require;
        self
    }

    /// Builder: set rate limit config.
    pub fn with_rate_limits(mut self, config: RateLimitConfig) -> Self {
        self.rate_limits = config;
        self
    }

    /// Builder: set ban config.
    pub fn with_ban_config(mut self, config: BanConfig) -> Self {
        self.ban_config = config;
        self
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::message::WireMessage;
    use crate::server::PeerRole;
    use std::time::Duration;

    // ─── GossipFilter tests ─────────────────────────────────────────────────

    #[test]
    fn anonymous_does_not_receive_block_messages() {
        let role = PeerRole::Anonymous;

        // SubmitRevocation is a state-replication message (blocks)
        let revocation_msg = WireMessage::SubmitRevocation {
            token_id: "tok-1".to_string(),
            authority: crate::message::PublicKey([0xAA; 32]),
            authority_sig: crate::message::Signature([0xBB; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };
        assert!(
            !GossipFilter::should_send_to_peer(&revocation_msg, &role),
            "Anonymous should NOT receive state-replication messages"
        );

        // RevocationAck is also state-replication
        let ack_msg = WireMessage::RevocationAck {
            new_root: [0; 32],
            height: 1,
        };
        assert!(!GossipFilter::should_send_to_peer(&ack_msg, &role));
    }

    #[test]
    fn captp_peer_receives_captp_but_not_blocks() {
        let role = PeerRole::CapTpPeer {
            peer_strand: [0xCC; 32],
            group_id: None,
        };

        // CapTP messages: should receive
        let cap_hello = WireMessage::CapHello {
            group_id: [0xDD; 32],
            initial_exports: vec![],
        };
        assert!(GossipFilter::should_send_to_peer(&cap_hello, &role));

        let enliven = WireMessage::EnlivenSturdyRef {
            uri_bytes: vec![0; 96],
            requester_height: 100,
        };
        assert!(GossipFilter::should_send_to_peer(&enliven, &role));

        // State-replication messages: should NOT receive
        let revocation = WireMessage::SubmitRevocation {
            token_id: "tok-1".to_string(),
            authority: crate::message::PublicKey([0xAA; 32]),
            authority_sig: crate::message::Signature([0xBB; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };
        assert!(
            !GossipFilter::should_send_to_peer(&revocation, &role),
            "CapTpPeer should NOT receive state-replication messages"
        );
    }

    #[test]
    fn member_receives_everything() {
        let role = PeerRole::Member {
            participant_key: [0xAA; 32],
        };

        // State-replication
        let revocation = WireMessage::SubmitRevocation {
            token_id: "tok-1".to_string(),
            authority: crate::message::PublicKey([0xAA; 32]),
            authority_sig: crate::message::Signature([0xBB; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };
        assert!(GossipFilter::should_send_to_peer(&revocation, &role));

        // CapTP
        let cap_hello = WireMessage::CapHello {
            group_id: [0xDD; 32],
            initial_exports: vec![],
        };
        assert!(GossipFilter::should_send_to_peer(&cap_hello, &role));

        // Public
        let ping = WireMessage::Ping {
            seq: 1,
            timestamp: 100,
        };
        assert!(GossipFilter::should_send_to_peer(&ping, &role));
    }

    // ─── RateLimiter tests ──────────────────────────────────────────────────

    #[test]
    fn anonymous_gets_stricter_rate_limits() {
        let config = RateLimitConfig::default();

        let anon_limit = config.limit_for_role(&PeerRole::Anonymous);
        let member_limit = config.limit_for_role(&PeerRole::Member {
            participant_key: [0; 32],
        });

        assert!(
            anon_limit < member_limit,
            "Anonymous ({anon_limit}) should have stricter limits than Member ({member_limit})"
        );

        // Verify Anonymous actually hits the limit
        let mut limiter = RateLimiter::for_role(&PeerRole::Anonymous, &config);
        for _ in 0..anon_limit {
            assert!(limiter.check(), "should allow up to the limit");
        }
        assert!(
            !limiter.check(),
            "should reject after limit exceeded for Anonymous"
        );
    }

    #[test]
    fn member_has_higher_rate_limit() {
        let config = RateLimitConfig {
            anonymous_max: 5,
            captp_max: 20,
            member_max: 50,
            window: Duration::from_secs(10),
        };

        let mut member_limiter = RateLimiter::for_role(
            &PeerRole::Member {
                participant_key: [0; 32],
            },
            &config,
        );

        // Should allow many more messages for member
        for i in 0..50 {
            assert!(member_limiter.check(), "member should allow message {i}");
        }
        assert!(!member_limiter.check(), "member should hit limit at 50");
    }

    // ─── BanList tests ──────────────────────────────────────────────────────

    #[test]
    fn repeated_auth_failures_trigger_ban() {
        let config = BanConfig {
            max_auth_failures: 3,
            auth_failure_ban_duration: Duration::from_secs(300),
            ..Default::default()
        };
        let mut ban_list = BanList::new(config);

        let ip: IpAddr = "192.168.1.100".parse().unwrap();

        // First two failures: not banned yet
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(!ban_list.is_banned(&ip));
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(!ban_list.is_banned(&ip));

        // Third failure: banned
        assert!(ban_list.record_auth_failure(&ip));
        assert!(ban_list.is_banned(&ip));

        // Verify ban reason
        let entry = ban_list.get_ban(&ip).unwrap();
        assert_eq!(entry.reason, BanReason::RepeatedAuthFailure { attempts: 3 });
    }

    #[test]
    fn ban_expires_after_duration() {
        let config = BanConfig {
            max_auth_failures: 1,
            auth_failure_ban_duration: Duration::from_millis(10),
            ..Default::default()
        };
        let mut ban_list = BanList::new(config);

        let ip: IpAddr = "10.0.0.1".parse().unwrap();
        ban_list.record_auth_failure(&ip);
        assert!(ban_list.is_banned(&ip));

        // Wait for ban to expire
        std::thread::sleep(Duration::from_millis(15));
        assert!(!ban_list.is_banned(&ip));
    }

    #[test]
    fn auth_success_resets_failure_count() {
        let config = BanConfig {
            max_auth_failures: 3,
            ..Default::default()
        };
        let mut ban_list = BanList::new(config);

        let ip: IpAddr = "10.0.0.2".parse().unwrap();

        // Two failures
        ban_list.record_auth_failure(&ip);
        ban_list.record_auth_failure(&ip);

        // Success resets
        ban_list.record_auth_success(&ip);

        // Two more failures shouldn't ban (counter was reset)
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(!ban_list.record_auth_failure(&ip));
        assert!(!ban_list.is_banned(&ip));

        // Third failure after reset: now banned
        assert!(ban_list.record_auth_failure(&ip));
        assert!(ban_list.is_banned(&ip));
    }

    #[test]
    fn cleanup_removes_expired_bans() {
        let config = BanConfig {
            max_auth_failures: 1,
            auth_failure_ban_duration: Duration::from_millis(5),
            ..Default::default()
        };
        let mut ban_list = BanList::new(config);

        let ip1: IpAddr = "10.0.0.1".parse().unwrap();
        let ip2: IpAddr = "10.0.0.2".parse().unwrap();
        ban_list.record_auth_failure(&ip1);
        ban_list.record_auth_failure(&ip2);

        assert_eq!(ban_list.active_ban_count(), 2);

        std::thread::sleep(Duration::from_millis(10));
        ban_list.cleanup_expired();

        assert_eq!(ban_list.active_ban_count(), 0);
    }
}
