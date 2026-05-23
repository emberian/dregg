//! Production hardening for the wire protocol.
//!
//! This module provides:
//! - Message size limits (configurable, defaults to 1MB)
//! - Per-peer rate limiting (token bucket)
//! - Connection lifecycle metrics
//! - Backpressure via bounded channels
//! - Heartbeat/keepalive with timeout detection
//! - Graceful shutdown coordination
//!
//! These primitives are used by [`crate::server::SiloServer`] to prevent
//! resource exhaustion, detect dead connections, and ensure clean shutdown.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{broadcast, mpsc};

use crate::message::WireMessage;
use crate::server::PeerRole;

// =============================================================================
// Message Size Limit
// =============================================================================

/// Default maximum message size: 1 MiB.
///
/// This is more restrictive than the codec-level limit (16 MiB) and can be
/// configured per-server. A typical STARK presentation proof is ~24 KiB, so
/// 1 MiB provides headroom for batch operations while preventing abuse.
pub const DEFAULT_MAX_MESSAGE_SIZE: usize = 1024 * 1024;

// =============================================================================
// Rate Limiter (Token Bucket)
// =============================================================================

/// A token bucket rate limiter for per-peer message throttling.
///
/// Each incoming message costs at least 1 token. Expensive messages
/// (revocations, full turn submissions) can cost more. When the bucket
/// is empty, the peer is throttled.
#[derive(Debug, Clone)]
pub struct RateLimiter {
    /// Available tokens.
    tokens: u32,
    /// Maximum bucket capacity.
    max_tokens: u32,
    /// Tokens added per second.
    refill_rate: u32,
    /// Last time tokens were refilled.
    last_refill: Instant,
}

impl RateLimiter {
    /// Create a new rate limiter with the given capacity and refill rate.
    pub fn new(max_tokens: u32, refill_rate: u32) -> Self {
        Self {
            tokens: max_tokens,
            max_tokens,
            refill_rate,
            last_refill: Instant::now(),
        }
    }

    /// Attempt to consume `cost` tokens. Returns `true` if allowed, `false`
    /// if rate limited.
    pub fn try_consume(&mut self, cost: u32) -> bool {
        self.refill();
        if self.tokens >= cost {
            self.tokens -= cost;
            true
        } else {
            false
        }
    }

    /// Refill tokens based on elapsed time.
    fn refill(&mut self) {
        let now = Instant::now();
        let elapsed = now.duration_since(self.last_refill);
        let new_tokens = (elapsed.as_secs_f64() * self.refill_rate as f64) as u32;
        if new_tokens > 0 {
            self.tokens = (self.tokens + new_tokens).min(self.max_tokens);
            self.last_refill = now;
        }
    }

    /// Get the current number of available tokens.
    pub fn available_tokens(&self) -> u32 {
        self.tokens
    }

    /// Get the maximum bucket capacity.
    pub fn max_tokens(&self) -> u32 {
        self.max_tokens
    }

    /// Get the refill rate (tokens per second).
    pub fn refill_rate(&self) -> u32 {
        self.refill_rate
    }
}

/// Compute the token cost for a message variant.
///
/// Most messages cost 1 token. Expensive operations cost more to prevent
/// abuse of resource-intensive handlers.
pub fn message_cost(msg: &WireMessage) -> u32 {
    match msg {
        // Expensive: revocation requires crypto verification + state mutation
        WireMessage::SubmitRevocation { .. } => 5,
        // Expensive: proof verification is CPU-intensive
        WireMessage::PresentToken { .. } => 3,
        // Moderate: CapTP operations involve session state
        WireMessage::EnlivenSturdyRef { .. } => 2,
        WireMessage::PresentHandoff { .. } => 2,
        WireMessage::PipelinedMsg { .. } => 2,
        // Cheap: everything else
        _ => 1,
    }
}

// =============================================================================
// Connection Metrics
// =============================================================================

/// Tracks per-connection lifecycle metrics.
///
/// Created when a connection is established, updated throughout its lifetime,
/// and can be inspected for diagnostics and monitoring.
#[derive(Debug, Clone)]
pub struct ConnectionMetrics {
    /// When the connection was established.
    pub connected_at: Instant,
    /// Total messages received from this peer.
    pub messages_received: u64,
    /// Total messages sent to this peer.
    pub messages_sent: u64,
    /// Total bytes received from this peer.
    pub bytes_received: u64,
    /// Total bytes sent to this peer.
    pub bytes_sent: u64,
    /// When the last message was received or sent.
    pub last_message_at: Instant,
    /// The peer's authenticated role.
    pub role: PeerRole,
    /// The peer's rate limiter state.
    pub rate_limiter: RateLimiter,
}

impl ConnectionMetrics {
    /// Create new metrics for a freshly established connection.
    pub fn new(role: PeerRole, rate_limiter: RateLimiter) -> Self {
        let now = Instant::now();
        Self {
            connected_at: now,
            messages_received: 0,
            messages_sent: 0,
            bytes_received: 0,
            bytes_sent: 0,
            last_message_at: now,
            role,
            rate_limiter,
        }
    }

    /// Record that a message was received.
    pub fn record_receive(&mut self, bytes: u64) {
        self.messages_received += 1;
        self.bytes_received += bytes;
        self.last_message_at = Instant::now();
    }

    /// Record that a message was sent.
    pub fn record_send(&mut self, bytes: u64) {
        self.messages_sent += 1;
        self.bytes_sent += bytes;
        self.last_message_at = Instant::now();
    }

    /// How long this connection has been alive.
    pub fn uptime(&self) -> Duration {
        self.connected_at.elapsed()
    }

    /// How long since the last message was exchanged.
    pub fn idle_duration(&self) -> Duration {
        self.last_message_at.elapsed()
    }
}

// =============================================================================
// Heartbeat Configuration
// =============================================================================

/// How frequently to send keepalive pings.
pub const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(30);

/// How long to wait for a pong before considering the connection dead.
pub const HEARTBEAT_TIMEOUT: Duration = Duration::from_secs(90);

// =============================================================================
// Backpressure: Bounded Outgoing Channel
// =============================================================================

/// Default capacity for the bounded outgoing message channel per connection.
///
/// If a slow reader causes the channel to fill up, the connection is
/// considered stalled and will be disconnected.
pub const OUTGOING_CHANNEL_CAPACITY: usize = 64;

/// Messages that can be sent on the outgoing channel.
#[derive(Debug, Clone)]
pub enum OutgoingMessage {
    /// A normal wire protocol message.
    Wire(WireMessage),
    /// Close the connection (used during shutdown).
    Close,
}

/// Create a bounded channel for outgoing messages.
///
/// Returns (sender, receiver). The sender is held by the message handler;
/// the receiver is held by the write task.
pub fn outgoing_channel() -> (
    mpsc::Sender<OutgoingMessage>,
    mpsc::Receiver<OutgoingMessage>,
) {
    mpsc::channel(OUTGOING_CHANNEL_CAPACITY)
}

// =============================================================================
// Graceful Shutdown
// =============================================================================

/// Coordinates graceful shutdown of the server and all active connections.
///
/// When shutdown is initiated:
/// 1. The accept loop stops accepting new connections.
/// 2. All active connections receive a `CapGoodbye` message.
/// 3. In-flight messages are given a grace period to complete.
/// 4. Remaining connections are force-closed.
#[derive(Debug, Clone)]
pub struct ShutdownCoordinator {
    /// Signal that shutdown has been initiated.
    shutdown_signal: Arc<AtomicBool>,
    /// Broadcast channel to notify all connection tasks of shutdown.
    notify: broadcast::Sender<()>,
    /// The grace period before force-closing connections.
    grace_period: Duration,
    /// The node ID for CapGoodbye messages.
    node_id: [u8; 32],
    /// Counter for active connections (for monitoring drain progress).
    active_connections: Arc<AtomicU64>,
}

impl ShutdownCoordinator {
    /// Create a new shutdown coordinator.
    pub fn new(node_id: [u8; 32], grace_period: Duration) -> Self {
        let (notify, _) = broadcast::channel(1);
        Self {
            shutdown_signal: Arc::new(AtomicBool::new(false)),
            notify,
            grace_period,
            node_id,
            active_connections: Arc::new(AtomicU64::new(0)),
        }
    }

    /// Check whether shutdown has been initiated.
    pub fn is_shutting_down(&self) -> bool {
        self.shutdown_signal.load(Ordering::SeqCst)
    }

    /// Initiate graceful shutdown. Returns the number of active connections
    /// that will be drained.
    pub fn initiate_shutdown(&self) -> u64 {
        self.shutdown_signal.store(true, Ordering::SeqCst);
        let _ = self.notify.send(());
        self.active_connections.load(Ordering::SeqCst)
    }

    /// Subscribe to shutdown notifications.
    pub fn subscribe(&self) -> broadcast::Receiver<()> {
        self.notify.subscribe()
    }

    /// Register a new active connection.
    pub fn register_connection(&self) {
        self.active_connections.fetch_add(1, Ordering::SeqCst);
    }

    /// Unregister a connection (it has closed).
    pub fn unregister_connection(&self) {
        self.active_connections.fetch_sub(1, Ordering::SeqCst);
    }

    /// Get the number of currently active connections.
    pub fn active_count(&self) -> u64 {
        self.active_connections.load(Ordering::SeqCst)
    }

    /// Get the grace period duration.
    pub fn grace_period(&self) -> Duration {
        self.grace_period
    }

    /// Get the node ID (for CapGoodbye messages).
    pub fn node_id(&self) -> [u8; 32] {
        self.node_id
    }

    /// Build the CapGoodbye message sent during shutdown.
    pub fn goodbye_message(&self) -> WireMessage {
        WireMessage::CapGoodbye {
            group_id: self.node_id,
            reason: Some("server shutting down".to_string()),
        }
    }
}

// =============================================================================
// Hardening Configuration
// =============================================================================

/// Configuration for production hardening features.
///
/// These are applied on top of [`crate::server::SiloConfig`] to configure
/// resource limits, rate limiting, and lifecycle management.
#[derive(Debug, Clone)]
pub struct HardeningConfig {
    /// Maximum message size in bytes (default: 1 MiB).
    pub max_message_size: usize,
    /// Rate limiter: maximum tokens (bucket capacity).
    pub rate_limit_max_tokens: u32,
    /// Rate limiter: tokens refilled per second.
    pub rate_limit_refill_rate: u32,
    /// Heartbeat interval (how often to send Ping).
    pub heartbeat_interval: Duration,
    /// Heartbeat timeout (disconnect if no Pong within this duration).
    pub heartbeat_timeout: Duration,
    /// Outgoing channel capacity (backpressure threshold).
    pub outgoing_channel_capacity: usize,
    /// Grace period for graceful shutdown.
    pub shutdown_grace_period: Duration,
}

impl Default for HardeningConfig {
    fn default() -> Self {
        Self {
            max_message_size: DEFAULT_MAX_MESSAGE_SIZE,
            rate_limit_max_tokens: 100,
            rate_limit_refill_rate: 20,
            heartbeat_interval: HEARTBEAT_INTERVAL,
            heartbeat_timeout: HEARTBEAT_TIMEOUT,
            outgoing_channel_capacity: OUTGOING_CHANNEL_CAPACITY,
            shutdown_grace_period: Duration::from_secs(5),
        }
    }
}

impl HardeningConfig {
    /// Create a default hardening configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the maximum message size.
    pub fn with_max_message_size(mut self, size: usize) -> Self {
        self.max_message_size = size;
        self
    }

    /// Set rate limiting parameters.
    pub fn with_rate_limit(mut self, max_tokens: u32, refill_rate: u32) -> Self {
        self.rate_limit_max_tokens = max_tokens;
        self.rate_limit_refill_rate = refill_rate;
        self
    }

    /// Set heartbeat parameters.
    pub fn with_heartbeat(mut self, interval: Duration, timeout: Duration) -> Self {
        self.heartbeat_interval = interval;
        self.heartbeat_timeout = timeout;
        self
    }

    /// Set outgoing channel capacity.
    pub fn with_channel_capacity(mut self, capacity: usize) -> Self {
        self.outgoing_channel_capacity = capacity;
        self
    }

    /// Set shutdown grace period.
    pub fn with_grace_period(mut self, duration: Duration) -> Self {
        self.shutdown_grace_period = duration;
        self
    }

    /// Create a rate limiter from this configuration.
    pub fn new_rate_limiter(&self) -> RateLimiter {
        RateLimiter::new(self.rate_limit_max_tokens, self.rate_limit_refill_rate)
    }
}

// =============================================================================
// Error codes for hardening features
// =============================================================================

/// Error code: message exceeds the configured size limit.
pub const ERROR_MESSAGE_TOO_LARGE: u32 = 20;
/// Error code: peer is rate limited (token bucket exhausted).
pub const ERROR_RATE_LIMITED: u32 = 21;
/// Error code: heartbeat timeout (connection considered dead).
pub const ERROR_HEARTBEAT_TIMEOUT: u32 = 22;
/// Error code: server is shutting down.
pub const ERROR_SHUTTING_DOWN: u32 = 23;
/// Error code: backpressure — outgoing channel full (slow reader).
pub const ERROR_BACKPRESSURE: u32 = 24;

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rate_limiter_basic() {
        let mut rl = RateLimiter::new(10, 5);
        // Should have full capacity initially
        assert_eq!(rl.available_tokens(), 10);

        // Consume tokens
        assert!(rl.try_consume(5));
        assert_eq!(rl.available_tokens(), 5);

        // Consume remaining
        assert!(rl.try_consume(5));
        assert_eq!(rl.available_tokens(), 0);

        // Should be rate limited now
        assert!(!rl.try_consume(1));
    }

    #[test]
    fn rate_limiter_refill() {
        let mut rl = RateLimiter::new(10, 100); // 100 tokens/sec
        assert!(rl.try_consume(10));
        assert!(!rl.try_consume(1));

        // Manually set last_refill in the past
        rl.last_refill = Instant::now() - Duration::from_millis(200);

        // After 200ms at 100 tokens/sec, should have ~20 tokens (capped at max 10)
        assert!(rl.try_consume(1));
    }

    #[test]
    fn rate_limiter_does_not_exceed_max() {
        let mut rl = RateLimiter::new(10, 100);
        // Set last_refill far in the past
        rl.last_refill = Instant::now() - Duration::from_secs(60);
        rl.refill();
        // Should be capped at max_tokens
        assert_eq!(rl.available_tokens(), 10);
    }

    #[test]
    fn message_cost_variants() {
        let revocation = WireMessage::SubmitRevocation {
            token_id: "tok".to_string(),
            authority: crate::message::PublicKey([0; 32]),
            authority_sig: crate::message::Signature([0; 64]),
            nonce: [0; 16],
            timestamp: 0,
        };
        assert_eq!(message_cost(&revocation), 5);

        let ping = WireMessage::Ping {
            seq: 0,
            timestamp: 0,
        };
        assert_eq!(message_cost(&ping), 1);

        let present = WireMessage::PresentToken {
            proof: vec![],
            request: crate::message::AuthorizationRequest::new("r", "a", "p"),
            federation_root: [0; 32],
        };
        assert_eq!(message_cost(&present), 3);
    }

    #[test]
    fn connection_metrics_tracking() {
        let rl = RateLimiter::new(100, 20);
        let mut metrics = ConnectionMetrics::new(PeerRole::Anonymous, rl);

        assert_eq!(metrics.messages_received, 0);
        assert_eq!(metrics.messages_sent, 0);

        metrics.record_receive(100);
        assert_eq!(metrics.messages_received, 1);
        assert_eq!(metrics.bytes_received, 100);

        metrics.record_send(50);
        assert_eq!(metrics.messages_sent, 1);
        assert_eq!(metrics.bytes_sent, 50);
    }

    #[test]
    fn shutdown_coordinator_lifecycle() {
        let coord = ShutdownCoordinator::new([0xAA; 32], Duration::from_secs(5));
        assert!(!coord.is_shutting_down());
        assert_eq!(coord.active_count(), 0);

        coord.register_connection();
        coord.register_connection();
        assert_eq!(coord.active_count(), 2);

        let count = coord.initiate_shutdown();
        assert_eq!(count, 2);
        assert!(coord.is_shutting_down());

        coord.unregister_connection();
        assert_eq!(coord.active_count(), 1);
    }

    #[test]
    fn hardening_config_builder() {
        let config = HardeningConfig::new()
            .with_max_message_size(512 * 1024)
            .with_rate_limit(50, 10)
            .with_heartbeat(Duration::from_secs(15), Duration::from_secs(45))
            .with_channel_capacity(32)
            .with_grace_period(Duration::from_secs(3));

        assert_eq!(config.max_message_size, 512 * 1024);
        assert_eq!(config.rate_limit_max_tokens, 50);
        assert_eq!(config.rate_limit_refill_rate, 10);
        assert_eq!(config.heartbeat_interval, Duration::from_secs(15));
        assert_eq!(config.heartbeat_timeout, Duration::from_secs(45));
        assert_eq!(config.outgoing_channel_capacity, 32);
        assert_eq!(config.shutdown_grace_period, Duration::from_secs(3));
    }

    #[test]
    fn outgoing_channel_is_bounded() {
        let (tx, _rx) = outgoing_channel();
        // The channel should have bounded capacity
        assert_eq!(tx.max_capacity(), OUTGOING_CHANNEL_CAPACITY);
    }

    #[test]
    fn goodbye_message_format() {
        let coord = ShutdownCoordinator::new([0xBB; 32], Duration::from_secs(5));
        let msg = coord.goodbye_message();
        match msg {
            WireMessage::CapGoodbye {
                federation_id,
                reason,
            } => {
                assert_eq!(federation_id, [0xBB; 32]);
                assert_eq!(reason, Some("server shutting down".to_string()));
            }
            _ => panic!("expected CapGoodbye"),
        }
    }
}
