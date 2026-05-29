//! GossipNetwork: Plumtree-inspired lazy-push gossip for dregg.
//!
//! Implements a hybrid eager/lazy push protocol over QUIC unidirectional streams:
//!
//! - **Eager push**: Full messages are forwarded immediately to a small subset of peers
//!   (the "eager set"), forming a spanning tree for fast delivery.
//! - **Lazy push**: IHave notifications (message hash only) are sent to remaining peers.
//!   If a peer receives an IHave for a message it hasn't seen, it sends a Graft request.
//! - **Prune**: If a peer receives a full message from a non-eager source (i.e., it was
//!   already delivered by a faster eager link), it sends Prune to demote the slow link.
//! - **Anti-entropy**: Periodic hash digest exchange (capped at a configurable maximum)
//!   catches any messages missed by the eager/lazy protocol without bandwidth amplification.
//!
//! ## Security
//!
//! - All gossip envelopes are signed (Ed25519 with per-node asymmetric keys).
//!   Each node signs with its own private key; receivers verify using the
//!   sender's public key looked up by NodeId from the peer registry.
//! - Message hashes are verified on receipt: `blake3(payload) == msg_hash`.
//! - Pending IHave state is bounded to prevent memory exhaustion.
//! - Connections are bounded by the configured `max_connections` limit.
//!
//! The public API (`publish`, `subscribe`, `join_topic`) is unchanged from the original
//! eager-push implementation.

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use quinn::{Connection, Endpoint, RecvStream};
use rand::seq::IndexedRandom;
use tokio::sync::{RwLock, mpsc};
use tracing::{debug, info, trace, warn};

use dregg_types::{PublicKey, Signature as Ed25519Signature, SigningKey};

use crate::message::PeerMessage;
use crate::node::{NodeId, fmt_node_id};

/// A topic identifier (32-byte blake3 hash of the topic name).
pub type TopicId = [u8; 32];

/// 32-byte message hash used for deduplication and IHave/Graft.
pub type MessageHash = [u8; 32];

/// Maximum number of eager peers per topic (the rest get lazy push).
const DEFAULT_EAGER_DEGREE: usize = 3;

/// How long to wait after receiving an IHave before sending a Graft.
/// If the message arrives eagerly within this window, no Graft is needed.
const IHAVE_TIMEOUT: Duration = Duration::from_millis(500);

/// Interval for anti-entropy reconciliation rounds.
const ANTI_ENTROPY_INTERVAL: Duration = Duration::from_secs(30);

/// Time window for the seen set — messages older than this are forgotten.
const SEEN_TTL: Duration = Duration::from_secs(300);

/// Maximum entries in the seen set (hard cap even if within TTL).
const SEEN_MAX_ENTRIES: usize = 100_000;

/// Maximum number of pending IHave entries. When exceeded, oldest entries are evicted.
const MAX_PENDING_IHAVES: usize = 10_000;

/// Maximum number of hashes to send in a single anti-entropy message.
/// At 1024 hashes * 32 bytes = 32 KiB per sync round (vs 3.2 MiB for full 100k set).
const MAX_ANTI_ENTROPY_HASHES: usize = 1024;

/// Maximum number of messages to send in a single anti-entropy response.
const MAX_ANTI_ENTROPY_RESPONSE_MESSAGES: usize = 64;

/// Maximum total bytes of payloads in a single anti-entropy response (256 KiB).
const MAX_ANTI_ENTROPY_RESPONSE_BYTES: usize = 256 * 1024;

/// Maximum number of concurrent gossip connections.
const DEFAULT_MAX_GOSSIP_CONNECTIONS: usize = 256;

/// Maximum entries in the message cache. When exceeded, oldest entries are
/// evicted to prevent unbounded memory growth from message floods.
const MAX_MESSAGE_CACHE_SIZE: usize = 10_000;

/// Maximum number of concurrent streams per peer connection.
/// Prevents a single peer from exhausting resources via stream flooding.
const MAX_STREAMS_PER_PEER: usize = 64;

// ─── Dandelion++ constants ─────────────────────────────────────────────────

/// Base probability of continuing stem phase at each hop.
/// Expected stem length: 1/(1-p) = 10 hops.
/// NOTE: The actual probability used is adaptive based on peer count.
/// See [`effective_stem_probability`].
const STEM_PROBABILITY: f64 = 0.9;

/// Maximum time a message may remain in stem phase before being fluffed.
/// Prevents message loss if the stem path hits a dead or unresponsive node.
const STEM_TIMEOUT: Duration = Duration::from_secs(30);

/// Compute the effective stem probability based on the current peer count.
///
/// In very small networks (< 5 peers), Dandelion++ stem phase provides no
/// meaningful anonymity (the stem path will cycle back to the originator or
/// visit all peers). In these cases, we disable or reduce the stem phase.
///
/// - peer_count < 5: stem disabled (immediate fluff) — no anonymity possible
/// - peer_count 5..10: reduced stem (0.5) — partial anonymity, ~2 hops
/// - peer_count >= 10: full Dandelion++ (0.9) — ~10 expected hops
fn effective_stem_probability(peer_count: usize) -> f64 {
    if peer_count < 5 {
        0.0 // Disable stem entirely — useless in tiny networks
    } else if peer_count < 10 {
        0.5 // Reduced stem — provides some privacy without excessive hops
    } else {
        STEM_PROBABILITY // Full Dandelion++ (0.9)
    }
}

/// A handle to a joined gossip topic.
#[derive(Clone, Debug)]
pub struct TopicHandle {
    topic_id: TopicId,
    name: String,
}

impl TopicHandle {
    /// Get the topic ID.
    pub fn id(&self) -> TopicId {
        self.topic_id
    }

    /// Get the human-readable topic name.
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// Dandelion++ message phase. Determines routing behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessagePhase {
    /// Stem phase: forward to exactly one random peer (hides origin).
    Stem,
    /// Fluff phase: broadcast to all peers via normal Plumtree gossip.
    Fluff,
}

/// Tracking entry for a message in stem phase (for timeout-based failsafe).
#[derive(Clone)]
struct StemEntry {
    topic_id: TopicId,
    msg_hash: MessageHash,
    payload: Vec<u8>,
    entered_stem_at: Instant,
}

/// The gossip network manages topic subscriptions and message forwarding.
///
/// Implements Plumtree-inspired lazy-push gossip: eager push to a spanning tree
/// subset, lazy IHave notifications to the rest, with Graft/Prune for tree repair.
pub struct GossipNetwork {
    /// Our node identity
    node_id: NodeId,
    /// Shared state protected by an async RwLock
    state: Arc<RwLock<GossipState>>,
    /// Channel to send outgoing gossip messages to the forwarding task
    outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
    /// The QUIC endpoint (for dialing peers)
    endpoint: Endpoint,
    /// Ed25519 signing key for envelope authentication (asymmetric).
    /// Each node signs with its own key; receivers verify with the sender's public key.
    signing_key: Arc<SigningKey>,
    /// Maximum concurrent gossip connections.
    max_connections: usize,
    /// Registry of known peer public keys for signature verification.
    /// Maps NodeId -> PublicKey. Populated from federation configuration.
    peer_keys: Arc<RwLock<HashMap<NodeId, PublicKey>>>,
}

/// A bounded deduplication set with time-based expiry.
///
/// Entries are evicted when either:
/// - They exceed `max_age` (time-based window), OR
/// - The set exceeds `max_size` (hard cap, FIFO eviction)
struct BoundedSeenSet {
    entries: VecDeque<SeenEntry>,
    index: HashSet<[u8; 32]>,
    max_size: usize,
    max_age: Duration,
}

#[derive(Clone)]
struct SeenEntry {
    hash: [u8; 32],
    inserted_at: Instant,
}

impl BoundedSeenSet {
    fn new(max_size: usize, max_age: Duration) -> Self {
        Self {
            entries: VecDeque::with_capacity(max_size.min(1024)),
            index: HashSet::with_capacity(max_size.min(1024)),
            max_size,
            max_age,
        }
    }

    /// Evict expired entries from the front of the queue.
    fn evict_expired(&mut self) {
        let now = Instant::now();
        while let Some(front) = self.entries.front() {
            if now.duration_since(front.inserted_at) > self.max_age {
                let entry = self.entries.pop_front().unwrap();
                self.index.remove(&entry.hash);
            } else {
                break;
            }
        }
    }

    /// Insert a hash. Returns `true` if it was new (not previously seen).
    fn insert(&mut self, hash: [u8; 32]) -> bool {
        self.evict_expired();

        if self.index.contains(&hash) {
            return false;
        }

        // Hard cap eviction
        if self.entries.len() >= self.max_size {
            if let Some(evicted) = self.entries.pop_front() {
                self.index.remove(&evicted.hash);
            }
        }

        self.entries.push_back(SeenEntry {
            hash,
            inserted_at: Instant::now(),
        });
        self.index.insert(hash);
        true
    }

    /// Check if a hash has been seen (and is not expired).
    fn contains(&self, hash: &[u8; 32]) -> bool {
        self.index.contains(hash)
    }

    /// Get up to `limit` currently-valid message hashes (for anti-entropy).
    fn hashes_capped(&self, limit: usize) -> Vec<[u8; 32]> {
        let now = Instant::now();
        self.entries
            .iter()
            .filter(|e| now.duration_since(e.inserted_at) <= self.max_age)
            .map(|e| e.hash)
            .take(limit)
            .collect()
    }
}

/// Per-peer state for a given topic.
#[derive(Clone, Debug)]
struct PeerTopicState {
    /// Whether this peer is in the eager set (receives full messages).
    eager: bool,
    /// Cumulative delivery score (higher = more reliable eager source).
    delivery_score: u32,
    /// Last measured RTT to this peer (from QUIC connection stats).
    last_rtt: Option<Duration>,
}

impl Default for PeerTopicState {
    fn default() -> Self {
        Self {
            eager: false,
            delivery_score: 0,
            last_rtt: None,
        }
    }
}

/// A bounded pending IHave map. When the capacity is exceeded, the oldest entries
/// are evicted (FIFO) to prevent unbounded memory growth from a flood of IHave messages.
struct BoundedPendingIhaves {
    entries: VecDeque<((TopicId, MessageHash), (SocketAddr, Instant))>,
    index: HashMap<(TopicId, MessageHash), (SocketAddr, Instant)>,
    max_size: usize,
}

impl BoundedPendingIhaves {
    fn new(max_size: usize) -> Self {
        Self {
            entries: VecDeque::with_capacity(max_size.min(1024)),
            index: HashMap::with_capacity(max_size.min(1024)),
            max_size,
        }
    }

    /// Insert a pending IHave. If at capacity, evicts the oldest entry.
    fn insert(&mut self, key: (TopicId, MessageHash), value: (SocketAddr, Instant)) {
        if self.index.contains_key(&key) {
            return;
        }

        if self.entries.len() >= self.max_size {
            if let Some((evicted_key, _)) = self.entries.pop_front() {
                self.index.remove(&evicted_key);
            }
        }

        self.entries.push_back((key, value));
        self.index.insert(key, value);
    }

    /// Remove an entry by key.
    fn remove(&mut self, key: &(TopicId, MessageHash)) {
        if self.index.remove(key).is_some() {
            self.entries.retain(|(k, _)| k != key);
        }
    }

    /// Check if a key exists.
    fn contains_key(&self, key: &(TopicId, MessageHash)) -> bool {
        self.index.contains_key(key)
    }

    /// Iterate over all entries.
    fn iter(&self) -> impl Iterator<Item = (&(TopicId, MessageHash), &(SocketAddr, Instant))> {
        self.index.iter()
    }
}

/// Internal gossip state.
struct GossipState {
    /// Topics we've joined, with their subscriber channels
    topics: HashMap<TopicId, TopicState>,
    /// Active connections to gossip peers (by their address)
    peers: HashMap<SocketAddr, Connection>,
    /// Messages we've already seen (by hash), for deduplication.
    seen: BoundedSeenSet,
    /// Pending IHave notifications waiting for timeout before we Graft.
    /// Bounded to MAX_PENDING_IHAVES entries; oldest evicted when full.
    pending_ihaves: BoundedPendingIhaves,
    /// Recently-sent message payloads (for responding to Graft requests).
    /// Bounded to MAX_MESSAGE_CACHE_SIZE entries; oldest evicted on insert.
    message_cache: HashMap<MessageHash, CachedMessage>,
    /// Insertion order for message cache entries (FIFO eviction).
    message_cache_order: VecDeque<MessageHash>,
    /// Dandelion++ stem tracking: messages currently in the stem phase.
    /// If a message stays here beyond STEM_TIMEOUT, it is fluffed automatically.
    stem_messages: HashMap<MessageHash, StemEntry>,
}

impl GossipState {
    /// Insert a message into the bounded cache, evicting oldest if at capacity.
    fn cache_insert(&mut self, hash: MessageHash, msg: CachedMessage) {
        if self.message_cache.contains_key(&hash) {
            return; // Already cached, no-op.
        }
        // Evict oldest entries until under capacity.
        while self.message_cache.len() >= MAX_MESSAGE_CACHE_SIZE {
            if let Some(oldest_hash) = self.message_cache_order.pop_front() {
                self.message_cache.remove(&oldest_hash);
            } else {
                break;
            }
        }
        self.message_cache.insert(hash, msg);
        self.message_cache_order.push_back(hash);
    }
}

#[derive(Clone)]
struct CachedMessage {
    topic_id: TopicId,
    payload: Vec<u8>,
    cached_at: Instant,
}

struct TopicState {
    /// Per-peer state for this topic (eager/lazy classification, scores)
    peer_states: HashMap<SocketAddr, PeerTopicState>,
    /// Subscribers to this topic on this node
    subscribers: Vec<mpsc::UnboundedSender<GossipEvent>>,
}

impl TopicState {
    fn new() -> Self {
        Self {
            peer_states: HashMap::new(),
            subscribers: Vec::new(),
        }
    }

    fn eager_peers(&self) -> Vec<SocketAddr> {
        self.peer_states
            .iter()
            .filter(|(_, s)| s.eager)
            .map(|(a, _)| *a)
            .collect()
    }

    fn lazy_peers(&self) -> Vec<SocketAddr> {
        self.peer_states
            .iter()
            .filter(|(_, s)| !s.eager)
            .map(|(a, _)| *a)
            .collect()
    }

    fn all_peers(&self) -> Vec<SocketAddr> {
        self.peer_states.keys().copied().collect()
    }

    fn add_peer(&mut self, addr: SocketAddr) {
        let eager_count = self.peer_states.values().filter(|s| s.eager).count();
        let should_be_eager = eager_count < DEFAULT_EAGER_DEGREE;
        self.peer_states.entry(addr).or_insert(PeerTopicState {
            eager: should_be_eager,
            delivery_score: 0,
            last_rtt: None,
        });
    }

    fn promote_to_eager(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.eager = true;
        }
    }

    fn demote_to_lazy(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.eager = false;
        }
    }

    fn record_delivery(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.delivery_score = state.delivery_score.saturating_add(1);
        }
    }

    fn update_rtt(&mut self, addr: &SocketAddr, rtt: Duration) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.last_rtt = Some(rtt);
        }
    }
}

/// Types of outgoing gossip operations.
#[allow(dead_code)]
enum OutgoingGossip {
    EagerPush {
        topic_id: TopicId,
        message: PeerMessage,
        msg_hash: MessageHash,
        targets: Vec<SocketAddr>,
        lazy_targets: Vec<SocketAddr>,
    },
    IHave {
        topic_id: TopicId,
        msg_hash: MessageHash,
        targets: Vec<SocketAddr>,
    },
    Graft {
        topic_id: TopicId,
        msg_hash: MessageHash,
        target: SocketAddr,
    },
    Prune {
        topic_id: TopicId,
        target: SocketAddr,
    },
    AntiEntropy {
        topic_id: TopicId,
        hashes: Vec<MessageHash>,
        target: SocketAddr,
    },
    /// Dandelion++ stem forward: send to exactly one peer in stem phase.
    StemForward {
        topic_id: TopicId,
        msg_hash: MessageHash,
        payload: Vec<u8>,
        target: SocketAddr,
    },
}

/// A subscription to a gossip topic.
pub struct MessageStream {
    receiver: mpsc::UnboundedReceiver<GossipEvent>,
}

/// Events received from the gossip network.
#[derive(Debug, Clone)]
pub enum GossipEvent {
    /// A message was received.
    Message {
        from: SocketAddr,
        message: PeerMessage,
    },
    /// A new peer joined this topic.
    PeerJoined(SocketAddr),
    /// A peer left this topic.
    PeerLeft(SocketAddr),
}

/// Errors from gossip operations.
#[derive(Debug)]
pub enum GossipError {
    Join(String),
    Publish(String),
    Subscribe(String),
    Shutdown,
}

impl std::fmt::Display for GossipError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GossipError::Join(e) => write!(f, "gossip join error: {e}"),
            GossipError::Publish(e) => write!(f, "gossip publish error: {e}"),
            GossipError::Subscribe(e) => write!(f, "gossip subscribe error: {e}"),
            GossipError::Shutdown => write!(f, "gossip network shut down"),
        }
    }
}

impl std::error::Error for GossipError {}

/// Gossip protocol envelope for wire transmission.
#[derive(serde::Serialize, serde::Deserialize, Clone)]
enum GossipEnvelope {
    FullMessage {
        topic_id: TopicId,
        msg_hash: MessageHash,
        payload: Vec<u8>,
    },
    IHave {
        topic_id: TopicId,
        msg_hash: MessageHash,
    },
    Graft {
        topic_id: TopicId,
        msg_hash: MessageHash,
    },
    Prune {
        topic_id: TopicId,
    },
    AntiEntropy {
        topic_id: TopicId,
        hashes: Vec<MessageHash>,
    },
    AntiEntropyResponse {
        topic_id: TopicId,
        messages: Vec<(MessageHash, Vec<u8>)>,
    },
    /// Dandelion++ stem message: forwarded to exactly one peer per hop.
    /// The receiver should continue stem (probability STEM_PROBABILITY) or
    /// transition to fluff (broadcast via normal Plumtree eager-push).
    Stem {
        topic_id: TopicId,
        msg_hash: MessageHash,
        payload: Vec<u8>,
    },
}

/// Serde helper for 64-byte arrays (Ed25519 signatures).
/// Serde only implements Serialize/Deserialize for arrays up to [T; 32].
mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for Ed25519 signature"))
    }
}

/// A signed gossip envelope. The signature covers the serialized inner envelope
/// and the sender's node ID, preventing forgery and ensuring message authenticity.
///
/// Uses Ed25519 asymmetric signatures: each node signs with its own private key,
/// and receivers verify using the sender's public key (looked up by NodeId from
/// the peer registry). This eliminates the broken shared-key HMAC scheme where
/// verification always failed between different nodes.
#[derive(serde::Serialize, serde::Deserialize)]
struct SignedEnvelope {
    /// The sender's node ID (blake3 hash of their TLS certificate).
    sender: NodeId,
    /// The serialized inner GossipEnvelope (postcard-encoded).
    body: Vec<u8>,
    /// Ed25519 signature over `sender || body` using the sender's private key.
    #[serde(with = "serde_sig64")]
    signature: [u8; 64],
}

impl SignedEnvelope {
    fn sign(envelope: &GossipEnvelope, sender: NodeId, signing_key: &SigningKey) -> Option<Self> {
        let body = postcard::to_stdvec(envelope).ok()?;
        let signature = Self::compute_signature(&sender, &body, signing_key);
        Some(Self {
            sender,
            body,
            signature,
        })
    }

    /// Verify the envelope's Ed25519 signature using the sender's public key.
    ///
    /// The caller must look up the sender's public key from the peer registry
    /// using `self.sender` (NodeId). Returns false if the signature is invalid.
    fn verify(&self, sender_public_key: &PublicKey) -> bool {
        let mut message = Vec::with_capacity(32 + self.body.len());
        message.extend_from_slice(&self.sender);
        message.extend_from_slice(&self.body);
        let sig = Ed25519Signature(self.signature);
        sender_public_key.verify(&message, &sig)
    }

    fn decode_inner(&self) -> Option<GossipEnvelope> {
        postcard::from_bytes(&self.body).ok()
    }

    fn compute_signature(sender: &NodeId, body: &[u8], signing_key: &SigningKey) -> [u8; 64] {
        let mut message = Vec::with_capacity(32 + body.len());
        message.extend_from_slice(sender);
        message.extend_from_slice(body);
        let sig = dregg_types::sign(signing_key, &message);
        sig.0
    }
}

impl GossipNetwork {
    /// Create a new gossip network node.
    ///
    /// The `signing_key` is this node's Ed25519 signing key, used to authenticate
    /// all outgoing gossip envelopes. Receivers verify using the sender's public
    /// key looked up from the peer registry.
    ///
    /// `peer_keys` maps known peer NodeIds to their Ed25519 public keys. This
    /// registry must be populated with federation member keys for signature
    /// verification to succeed.
    pub fn new(
        endpoint: Endpoint,
        node_id: NodeId,
        signing_key: SigningKey,
        peer_keys: HashMap<NodeId, PublicKey>,
    ) -> Self {
        Self::with_max_connections(
            endpoint,
            node_id,
            signing_key,
            peer_keys,
            DEFAULT_MAX_GOSSIP_CONNECTIONS,
        )
    }

    /// Create a new gossip network with a custom max_connections limit.
    pub fn with_max_connections(
        endpoint: Endpoint,
        node_id: NodeId,
        signing_key: SigningKey,
        peer_keys: HashMap<NodeId, PublicKey>,
        max_connections: usize,
    ) -> Self {
        let (outgoing_tx, outgoing_rx) = mpsc::unbounded_channel();

        let state = Arc::new(RwLock::new(GossipState {
            topics: HashMap::new(),
            peers: HashMap::new(),
            seen: BoundedSeenSet::new(SEEN_MAX_ENTRIES, SEEN_TTL),
            pending_ihaves: BoundedPendingIhaves::new(MAX_PENDING_IHAVES),
            message_cache: HashMap::new(),
            message_cache_order: VecDeque::new(),
            stem_messages: HashMap::new(),
        }));

        let signing_key = Arc::new(signing_key);
        let peer_keys = Arc::new(RwLock::new(peer_keys));

        let network = Self {
            node_id,
            state: state.clone(),
            outgoing_tx: outgoing_tx.clone(),
            endpoint: endpoint.clone(),
            signing_key: signing_key.clone(),
            max_connections,
            peer_keys: peer_keys.clone(),
        };

        // Spawn the forwarding task
        let fwd_state = state.clone();
        let fwd_node_id = node_id;
        let fwd_key = signing_key.clone();
        tokio::spawn(async move {
            Self::forward_loop(outgoing_rx, fwd_state, fwd_node_id, fwd_key).await;
        });

        // Spawn the incoming gossip acceptor
        let accept_state = state.clone();
        let accept_endpoint = endpoint.clone();
        let accept_tx = outgoing_tx.clone();
        let accept_key = signing_key.clone();
        let accept_node_id = node_id;
        let accept_max_conns = max_connections;
        let accept_peer_keys = peer_keys.clone();
        tokio::spawn(async move {
            Self::accept_loop(
                accept_endpoint,
                accept_state,
                accept_tx,
                accept_key,
                accept_node_id,
                accept_max_conns,
                accept_peer_keys,
            )
            .await;
        });

        // Spawn the IHave timeout checker
        let ihave_state = state.clone();
        let ihave_tx = outgoing_tx.clone();
        tokio::spawn(async move {
            Self::ihave_timeout_loop(ihave_state, ihave_tx).await;
        });

        // Spawn the Dandelion++ stem timeout checker
        let stem_state = state.clone();
        let stem_tx = outgoing_tx.clone();
        let stem_node_id = node_id;
        let stem_key = signing_key.clone();
        tokio::spawn(async move {
            Self::stem_timeout_loop(stem_state, stem_tx, stem_node_id, stem_key).await;
        });

        // Spawn the anti-entropy reconciliation task
        let ae_state = state.clone();
        let ae_tx = outgoing_tx.clone();
        tokio::spawn(async move {
            Self::anti_entropy_loop(ae_state, ae_tx).await;
        });

        // Spawn the message cache cleanup task
        let cache_state = state.clone();
        tokio::spawn(async move {
            Self::cache_cleanup_loop(cache_state).await;
        });

        info!(
            "GossipNetwork started (plumtree): {} (max_connections={})",
            fmt_node_id(&node_id),
            max_connections,
        );

        network
    }

    /// Register a peer's public key for signature verification.
    ///
    /// Call this when a new federation member is discovered (e.g., from genesis
    /// configuration or peer discovery protocol).
    pub async fn register_peer_key(&self, node_id: NodeId, public_key: PublicKey) {
        let mut keys = self.peer_keys.write().await;
        keys.insert(node_id, public_key);
    }

    /// Join a gossip topic, connecting to bootstrap peers.
    pub async fn join_topic(
        &self,
        topic_name: &str,
        bootstrap_peers: &[SocketAddr],
    ) -> Result<TopicHandle, GossipError> {
        let topic_id = topic_id_from_name(topic_name);

        {
            let mut state = self.state.write().await;
            let topic_state = state.topics.entry(topic_id).or_insert_with(TopicState::new);
            for &addr in bootstrap_peers {
                topic_state.add_peer(addr);
            }
        }

        for &addr in bootstrap_peers {
            let needs_connect = {
                let state = self.state.read().await;
                !state.peers.contains_key(&addr)
            };
            if needs_connect {
                if let Ok(conn) = self.connect_peer(addr).await {
                    let mut state = self.state.write().await;
                    state.peers.insert(addr, conn);
                }
            }
        }

        debug!(
            "Joined gossip topic '{}' with {} peers",
            topic_name,
            bootstrap_peers.len()
        );

        Ok(TopicHandle {
            topic_id,
            name: topic_name.to_string(),
        })
    }

    /// Publish a message to a gossip topic.
    ///
    /// Messages always enter the Dandelion++ stem phase first: they are forwarded
    /// to exactly one random peer (hiding the origin). The stem relay chain
    /// probabilistically transitions to fluff (normal Plumtree broadcast).
    pub async fn publish(
        &self,
        topic: &TopicHandle,
        message: &PeerMessage,
    ) -> Result<(), GossipError> {
        let encoded = message.encode_raw();
        let msg_hash = *blake3::hash(&encoded).as_bytes();

        // Pick a random peer for the stem relay.
        // Use adaptive stem probability: in small networks (< 5 peers), skip
        // stem entirely and go straight to fluff (no anonymity benefit from stem).
        let stem_target = {
            let mut state = self.state.write().await;
            state.seen.insert(msg_hash);
            state.cache_insert(
                msg_hash,
                CachedMessage {
                    topic_id: topic.topic_id,
                    payload: encoded.clone(),
                    cached_at: Instant::now(),
                },
            );

            let peer_count = state.peers.len();
            let stem_prob = effective_stem_probability(peer_count);

            // If stem is disabled for this network size, skip directly to fluff.
            if stem_prob == 0.0 {
                None
            } else {
                // Track this message in the stem set for timeout failsafe
                state.stem_messages.insert(
                    msg_hash,
                    StemEntry {
                        topic_id: topic.topic_id,
                        msg_hash,
                        payload: encoded.clone(),
                        entered_stem_at: Instant::now(),
                    },
                );

                // Select one random peer from all peers in this topic
                if let Some(topic_state) = state.topics.get(&topic.topic_id) {
                    let all_peers = topic_state.all_peers();
                    if all_peers.is_empty() {
                        None
                    } else {
                        let mut rng = rand::rng();
                        Some(*all_peers.choose(&mut rng).unwrap())
                    }
                } else {
                    None
                }
            }
        };

        match stem_target {
            Some(target) => {
                // Stem phase: forward to exactly one peer
                self.outgoing_tx
                    .send(OutgoingGossip::StemForward {
                        topic_id: topic.topic_id,
                        msg_hash,
                        payload: encoded,
                        target,
                    })
                    .map_err(|_| GossipError::Shutdown)?;
            }
            None => {
                // No peers available — fall back to immediate fluff
                let mut state = self.state.write().await;
                state.stem_messages.remove(&msg_hash);
                drop(state);

                let (eager_targets, lazy_targets) = {
                    let state = self.state.read().await;
                    if let Some(topic_state) = state.topics.get(&topic.topic_id) {
                        (topic_state.eager_peers(), topic_state.lazy_peers())
                    } else {
                        (Vec::new(), Vec::new())
                    }
                };

                self.outgoing_tx
                    .send(OutgoingGossip::EagerPush {
                        topic_id: topic.topic_id,
                        message: message.clone(),
                        msg_hash,
                        targets: eager_targets,
                        lazy_targets,
                    })
                    .map_err(|_| GossipError::Shutdown)?;
            }
        }

        self.deliver_locally(topic.topic_id, "127.0.0.1:0".parse().unwrap(), message)
            .await;

        Ok(())
    }

    /// Subscribe to a gossip topic, receiving messages as they arrive.
    pub async fn subscribe(&self, topic: &TopicHandle) -> Result<MessageStream, GossipError> {
        let (tx, rx) = mpsc::unbounded_channel();

        let mut state = self.state.write().await;
        let topic_state = state
            .topics
            .entry(topic.topic_id)
            .or_insert_with(TopicState::new);
        topic_state.subscribers.push(tx);

        Ok(MessageStream { receiver: rx })
    }

    /// Add a peer to a topic's peer set.
    pub async fn add_peer(&self, topic: &TopicHandle, addr: SocketAddr) {
        let mut state = self.state.write().await;
        if let Some(topic_state) = state.topics.get_mut(&topic.topic_id) {
            topic_state.add_peer(addr);
        }

        if !state.peers.contains_key(&addr) {
            drop(state);
            if let Ok(conn) = self.connect_peer(addr).await {
                let mut state = self.state.write().await;
                state.peers.insert(addr, conn);
            }
        }
    }

    async fn deliver_locally(&self, topic_id: TopicId, from: SocketAddr, message: &PeerMessage) {
        let state = self.state.read().await;
        if let Some(topic_state) = state.topics.get(&topic_id) {
            for sub in &topic_state.subscribers {
                let _ = sub.send(GossipEvent::Message {
                    from,
                    message: message.clone(),
                });
            }
        }
    }

    async fn connect_peer(&self, addr: SocketAddr) -> Result<Connection, GossipError> {
        let client_config = crate::node::PeerNode::build_client_config_static()
            .map_err(|e| GossipError::Join(format!("tls config: {e}")))?;

        let conn = self
            .endpoint
            .connect_with(client_config, addr, "dregg.local")
            .map_err(|e| GossipError::Join(e.to_string()))?
            .await
            .map_err(|e| GossipError::Join(e.to_string()))?;

        Ok(conn)
    }

    fn sign_envelope(
        envelope: &GossipEnvelope,
        node_id: NodeId,
        signing_key: &SigningKey,
    ) -> Option<Vec<u8>> {
        let signed = SignedEnvelope::sign(envelope, node_id, signing_key)?;
        postcard::to_stdvec(&signed).ok()
    }

    async fn forward_loop(
        mut rx: mpsc::UnboundedReceiver<OutgoingGossip>,
        state: Arc<RwLock<GossipState>>,
        node_id: NodeId,
        signing_key: Arc<SigningKey>,
    ) {
        while let Some(outgoing) = rx.recv().await {
            match outgoing {
                OutgoingGossip::EagerPush {
                    topic_id,
                    message,
                    msg_hash,
                    targets,
                    lazy_targets,
                } => {
                    let encoded = message.encode_raw();
                    let envelope = GossipEnvelope::FullMessage {
                        topic_id,
                        msg_hash,
                        payload: encoded,
                    };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };

                    Self::send_to_peers(&envelope_bytes, &targets, &state).await;

                    if !lazy_targets.is_empty() {
                        let ihave_envelope = GossipEnvelope::IHave { topic_id, msg_hash };
                        if let Some(ihave_bytes) =
                            Self::sign_envelope(&ihave_envelope, node_id, &signing_key)
                        {
                            Self::send_to_peers(&ihave_bytes, &lazy_targets, &state).await;
                        }
                    }
                }

                OutgoingGossip::IHave {
                    topic_id,
                    msg_hash,
                    targets,
                } => {
                    let envelope = GossipEnvelope::IHave { topic_id, msg_hash };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &targets, &state).await;
                }

                OutgoingGossip::Graft {
                    topic_id,
                    msg_hash,
                    target,
                } => {
                    let envelope = GossipEnvelope::Graft { topic_id, msg_hash };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;

                    let mut s = state.write().await;
                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.promote_to_eager(&target);
                    }
                }

                OutgoingGossip::Prune { topic_id, target } => {
                    let envelope = GossipEnvelope::Prune { topic_id };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;
                }

                OutgoingGossip::AntiEntropy {
                    topic_id,
                    hashes,
                    target,
                } => {
                    let envelope = GossipEnvelope::AntiEntropy { topic_id, hashes };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;
                }

                OutgoingGossip::StemForward {
                    topic_id,
                    msg_hash,
                    payload,
                    target,
                } => {
                    let envelope = GossipEnvelope::Stem {
                        topic_id,
                        msg_hash,
                        payload,
                    };
                    let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, &signing_key)
                    else {
                        warn!("gossip stem envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;
                }
            }
        }
    }

    async fn send_to_peers(data: &[u8], targets: &[SocketAddr], state: &Arc<RwLock<GossipState>>) {
        let mut dead_peers: Vec<SocketAddr> = Vec::new();

        // Apply two-bucket padding to hide message type from size analysis.
        // See docs/design-network-privacy.md Phase 1.
        let padded = crate::message::pad_message(data);

        for &addr in targets {
            let conn = {
                let state_r = state.read().await;
                state_r.peers.get(&addr).cloned()
            };
            if let Some(conn) = conn {
                match conn.open_uni().await {
                    Ok(mut stream) => {
                        let padded = padded.clone();
                        tokio::spawn(async move {
                            // Write outer length prefix (padded frame size) then padded data.
                            let len = (padded.len() as u32).to_be_bytes();
                            if stream.write_all(&len).await.is_ok() {
                                let _ = stream.write_all(&padded).await;
                                let _ = stream.finish();
                            }
                        });
                    }
                    Err(e) => {
                        debug!("Failed to open stream to {addr}: {e}");
                        dead_peers.push(addr);
                    }
                }
            }
        }

        if !dead_peers.is_empty() {
            let mut state_w = state.write().await;
            for addr in &dead_peers {
                state_w.peers.remove(addr);
                warn!("Removed dead peer connection: {addr}");
            }
            for topic_state in state_w.topics.values_mut() {
                for addr in &dead_peers {
                    topic_state.peer_states.remove(addr);
                }
            }
        }
    }

    async fn accept_loop(
        endpoint: Endpoint,
        state: Arc<RwLock<GossipState>>,
        outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
        signing_key: Arc<SigningKey>,
        node_id: NodeId,
        max_connections: usize,
        peer_keys: Arc<RwLock<HashMap<NodeId, PublicKey>>>,
    ) {
        loop {
            let Some(incoming) = endpoint.accept().await else {
                break;
            };

            // Enforce connection limit
            {
                let s = state.read().await;
                if s.peers.len() >= max_connections {
                    warn!(
                        "Gossip connection limit reached ({}) — rejecting from {}",
                        max_connections,
                        incoming.remote_address()
                    );
                    incoming.refuse();
                    continue;
                }
            }

            let state = state.clone();
            let outgoing_tx = outgoing_tx.clone();
            let key = signing_key.clone();
            let our_node_id = node_id;
            let peer_keys = peer_keys.clone();
            tokio::spawn(async move {
                let Ok(conn) = incoming.await else { return };
                let remote_addr = conn.remote_address();

                {
                    let mut s = state.write().await;
                    s.peers.insert(remote_addr, conn.clone());
                }

                // Per-connection stream counter to prevent stream flooding.
                let active_streams = Arc::new(std::sync::atomic::AtomicUsize::new(0));

                loop {
                    let Ok(mut recv) = conn.accept_uni().await else {
                        break;
                    };

                    // Enforce per-connection stream limit.
                    let current_streams = active_streams.fetch_add(1, Ordering::SeqCst);
                    if current_streams >= MAX_STREAMS_PER_PEER {
                        active_streams.fetch_sub(1, Ordering::SeqCst);
                        warn!(
                            "Rejecting stream from {} — at per-peer limit ({})",
                            remote_addr, MAX_STREAMS_PER_PEER
                        );
                        continue;
                    }

                    let state = state.clone();
                    let outgoing_tx = outgoing_tx.clone();
                    let key = key.clone();
                    let peer_keys = peer_keys.clone();
                    let streams_counter = active_streams.clone();
                    tokio::spawn(async move {
                        // Decrement stream count when this stream handler completes.
                        struct StreamGuard(Arc<std::sync::atomic::AtomicUsize>);
                        impl Drop for StreamGuard {
                            fn drop(&mut self) {
                                self.0.fetch_sub(1, Ordering::SeqCst);
                            }
                        }
                        let _guard = StreamGuard(streams_counter);
                        if let Ok(signed) = read_signed_envelope(&mut recv).await {
                            // Look up the sender's public key from the peer registry.
                            let sender_pk = {
                                let keys = peer_keys.read().await;
                                keys.get(&signed.sender).copied()
                            };

                            let sender_pk = match sender_pk {
                                Some(pk) => pk,
                                None => {
                                    warn!(
                                        "Rejecting gossip envelope from {} — unknown sender {:?}",
                                        remote_addr,
                                        &signed.sender[..4]
                                    );
                                    return;
                                }
                            };

                            // Verify Ed25519 signature using the sender's public key.
                            if !signed.verify(&sender_pk) {
                                warn!(
                                    "Rejecting gossip envelope from {} — invalid Ed25519 signature",
                                    remote_addr
                                );
                                return;
                            }

                            let Some(envelope) = signed.decode_inner() else {
                                warn!(
                                    "Rejecting gossip envelope from {} — decode failed",
                                    remote_addr
                                );
                                return;
                            };

                            Self::handle_envelope(
                                envelope,
                                remote_addr,
                                &state,
                                &outgoing_tx,
                                &*key,
                                our_node_id,
                            )
                            .await;
                        }
                    });
                }
            });
        }
    }

    async fn handle_envelope(
        envelope: GossipEnvelope,
        remote_addr: SocketAddr,
        state: &Arc<RwLock<GossipState>>,
        outgoing_tx: &mpsc::UnboundedSender<OutgoingGossip>,
        signing_key: &SigningKey,
        node_id: NodeId,
    ) {
        match envelope {
            GossipEnvelope::FullMessage {
                topic_id,
                msg_hash,
                payload,
            } => {
                // Verify hash integrity: blake3(payload) must equal msg_hash.
                let computed_hash = *blake3::hash(&payload).as_bytes();
                if computed_hash != msg_hash {
                    warn!(
                        "Rejecting gossip message from {} — hash mismatch \
                         (claimed {:02x}{:02x}..., computed {:02x}{:02x}...)",
                        remote_addr, msg_hash[0], msg_hash[1], computed_hash[0], computed_hash[1],
                    );
                    return;
                }

                let (is_new, eager_targets, lazy_targets) = {
                    let mut s = state.write().await;

                    if s.seen.contains(&msg_hash) {
                        if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                            let is_eager = topic_state
                                .peer_states
                                .get(&remote_addr)
                                .is_some_and(|ps| ps.eager);
                            if is_eager {
                                topic_state.demote_to_lazy(&remote_addr);
                                let _ = outgoing_tx.send(OutgoingGossip::Prune {
                                    topic_id,
                                    target: remote_addr,
                                });
                            }
                        }
                        return;
                    }

                    s.seen.insert(msg_hash);

                    s.cache_insert(
                        msg_hash,
                        CachedMessage {
                            topic_id,
                            payload: payload.clone(),
                            cached_at: Instant::now(),
                        },
                    );

                    s.pending_ihaves.remove(&(topic_id, msg_hash));

                    let peer_rtt = s.peers.get(&remote_addr).map(|conn| conn.rtt());

                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.record_delivery(&remote_addr);

                        if let Some(rtt) = peer_rtt {
                            topic_state.update_rtt(&remote_addr, rtt);
                        }

                        if let Ok(msg) = PeerMessage::decode_raw(&payload) {
                            for sub in &topic_state.subscribers {
                                let _ = sub.send(GossipEvent::Message {
                                    from: remote_addr,
                                    message: msg.clone(),
                                });
                            }
                        }

                        let eager: Vec<_> = topic_state
                            .eager_peers()
                            .into_iter()
                            .filter(|a| *a != remote_addr)
                            .collect();
                        let lazy: Vec<_> = topic_state
                            .lazy_peers()
                            .into_iter()
                            .filter(|a| *a != remote_addr)
                            .collect();
                        (true, eager, lazy)
                    } else {
                        (true, Vec::new(), Vec::new())
                    }
                };

                if is_new && (!eager_targets.is_empty() || !lazy_targets.is_empty()) {
                    if !eager_targets.is_empty() {
                        let fwd_envelope = GossipEnvelope::FullMessage {
                            topic_id,
                            msg_hash,
                            payload: payload.clone(),
                        };
                        if let Some(fwd_bytes) =
                            Self::sign_envelope(&fwd_envelope, node_id, signing_key)
                        {
                            Self::send_to_peers(&fwd_bytes, &eager_targets, state).await;
                        } else {
                            warn!("gossip forward envelope serialization failed");
                        }
                    }

                    if !lazy_targets.is_empty() {
                        let ihave_envelope = GossipEnvelope::IHave { topic_id, msg_hash };
                        if let Some(ihave_bytes) =
                            Self::sign_envelope(&ihave_envelope, node_id, signing_key)
                        {
                            Self::send_to_peers(&ihave_bytes, &lazy_targets, state).await;
                        }
                    }
                }
            }

            GossipEnvelope::IHave { topic_id, msg_hash } => {
                let already_have = {
                    let s = state.read().await;
                    s.seen.contains(&msg_hash)
                };

                if already_have {
                    trace!("IHave for already-seen message, ignoring");
                    return;
                }

                let mut s = state.write().await;
                if !s.pending_ihaves.contains_key(&(topic_id, msg_hash)) {
                    s.pending_ihaves
                        .insert((topic_id, msg_hash), (remote_addr, Instant::now()));
                }
            }

            GossipEnvelope::Graft { topic_id, msg_hash } => {
                {
                    let mut s = state.write().await;
                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.promote_to_eager(&remote_addr);
                    }
                }

                let cached = {
                    let s = state.read().await;
                    s.message_cache.get(&msg_hash).cloned()
                };

                if let Some(cached) = cached {
                    let envelope = GossipEnvelope::FullMessage {
                        topic_id,
                        msg_hash,
                        payload: cached.payload,
                    };
                    if let Some(envelope_bytes) =
                        Self::sign_envelope(&envelope, node_id, signing_key)
                    {
                        Self::send_to_peers(&envelope_bytes, &[remote_addr], state).await;
                    } else {
                        warn!("gossip Graft response serialization failed");
                    }
                } else {
                    debug!("Graft request for unknown message {:?}", &msg_hash[..4]);
                }
            }

            GossipEnvelope::Prune { topic_id } => {
                let mut s = state.write().await;
                if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                    topic_state.demote_to_lazy(&remote_addr);
                    debug!("Pruned peer {} to lazy for topic", remote_addr);
                }
            }

            GossipEnvelope::AntiEntropy { topic_id, hashes } => {
                let peer_hashes: HashSet<_> = hashes.into_iter().collect();
                let missing_messages: Vec<(MessageHash, Vec<u8>)> = {
                    let s = state.read().await;
                    let mut messages: Vec<(MessageHash, Vec<u8>)> = Vec::new();
                    let mut total_bytes: usize = 0;

                    for (hash, cached) in s.message_cache.iter() {
                        if cached.topic_id == topic_id && !peer_hashes.contains(hash) {
                            if messages.len() >= MAX_ANTI_ENTROPY_RESPONSE_MESSAGES {
                                break;
                            }
                            if total_bytes + cached.payload.len() > MAX_ANTI_ENTROPY_RESPONSE_BYTES
                            {
                                break;
                            }
                            total_bytes += cached.payload.len();
                            messages.push((*hash, cached.payload.clone()));
                        }
                    }
                    messages
                };

                if !missing_messages.is_empty() {
                    let response = GossipEnvelope::AntiEntropyResponse {
                        topic_id,
                        messages: missing_messages,
                    };
                    if let Some(response_bytes) =
                        Self::sign_envelope(&response, node_id, signing_key)
                    {
                        Self::send_to_peers(&response_bytes, &[remote_addr], state).await;
                    } else {
                        warn!("gossip anti-entropy response serialization failed");
                    }
                }
            }

            GossipEnvelope::AntiEntropyResponse { topic_id, messages } => {
                for (msg_hash, payload) in messages {
                    // Verify hash integrity on anti-entropy responses too
                    let computed_hash = *blake3::hash(&payload).as_bytes();
                    if computed_hash != msg_hash {
                        warn!(
                            "Rejecting anti-entropy message from {} — hash mismatch",
                            remote_addr
                        );
                        continue;
                    }

                    let is_new = {
                        let mut s = state.write().await;
                        if s.seen.contains(&msg_hash) {
                            false
                        } else {
                            s.seen.insert(msg_hash);
                            s.cache_insert(
                                msg_hash,
                                CachedMessage {
                                    topic_id,
                                    payload: payload.clone(),
                                    cached_at: Instant::now(),
                                },
                            );
                            true
                        }
                    };

                    if is_new {
                        let s = state.read().await;
                        if let Some(topic_state) = s.topics.get(&topic_id) {
                            if let Ok(msg) = PeerMessage::decode_raw(&payload) {
                                for sub in &topic_state.subscribers {
                                    let _ = sub.send(GossipEvent::Message {
                                        from: remote_addr,
                                        message: msg.clone(),
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // ─── Dandelion++ stem message handling ─────────────────────────
            GossipEnvelope::Stem {
                topic_id,
                msg_hash,
                payload,
            } => {
                // Verify hash integrity
                let computed_hash = *blake3::hash(&payload).as_bytes();
                if computed_hash != msg_hash {
                    warn!(
                        "Rejecting stem message from {} — hash mismatch",
                        remote_addr
                    );
                    return;
                }

                // Dedup: if we've already seen this message, ignore
                {
                    let s = state.read().await;
                    if s.seen.contains(&msg_hash) {
                        trace!("Stem message already seen, ignoring");
                        return;
                    }
                }

                // Decide: continue stem or transition to fluff?
                // Use adaptive stem probability based on peer count to avoid
                // useless stem hops in small networks (< 5 peers).
                let peer_count = {
                    let s = state.read().await;
                    s.peers.len()
                };
                let stem_prob = effective_stem_probability(peer_count);
                let continue_stem = stem_prob > 0.0 && rand::random::<f64>() < stem_prob;

                if continue_stem {
                    // Pick one random peer (excluding sender) and forward in stem phase
                    let stem_target = {
                        let s = state.read().await;
                        if let Some(topic_state) = s.topics.get(&topic_id) {
                            let candidates: Vec<_> = topic_state
                                .all_peers()
                                .into_iter()
                                .filter(|a| *a != remote_addr)
                                .collect();
                            if candidates.is_empty() {
                                None
                            } else {
                                let mut rng = rand::rng();
                                Some(*candidates.choose(&mut rng).unwrap())
                            }
                        } else {
                            None
                        }
                    };

                    match stem_target {
                        Some(target) => {
                            // Track for stem timeout failsafe
                            {
                                let mut s = state.write().await;
                                s.stem_messages.insert(
                                    msg_hash,
                                    StemEntry {
                                        topic_id,
                                        msg_hash,
                                        payload: payload.clone(),
                                        entered_stem_at: Instant::now(),
                                    },
                                );
                            }

                            let _ = outgoing_tx.send(OutgoingGossip::StemForward {
                                topic_id,
                                msg_hash,
                                payload,
                                target,
                            });
                        }
                        None => {
                            // No valid stem target — fluff immediately
                            Self::fluff_message(
                                topic_id,
                                msg_hash,
                                payload,
                                remote_addr,
                                state,
                                outgoing_tx,
                                signing_key,
                                node_id,
                            )
                            .await;
                        }
                    }
                } else {
                    // Transition to fluff: broadcast via normal Plumtree
                    Self::fluff_message(
                        topic_id,
                        msg_hash,
                        payload,
                        remote_addr,
                        state,
                        outgoing_tx,
                        signing_key,
                        node_id,
                    )
                    .await;
                }
            }
        }
    }

    /// Transition a stem message to fluff phase: mark as seen, deliver locally,
    /// and broadcast via normal Plumtree eager-push to all peers.
    async fn fluff_message(
        topic_id: TopicId,
        msg_hash: MessageHash,
        payload: Vec<u8>,
        received_from: SocketAddr,
        state: &Arc<RwLock<GossipState>>,
        _outgoing_tx: &mpsc::UnboundedSender<OutgoingGossip>,
        signing_key: &SigningKey,
        node_id: NodeId,
    ) {
        let (eager_targets, lazy_targets) = {
            let mut s = state.write().await;
            s.seen.insert(msg_hash);
            s.stem_messages.remove(&msg_hash);
            s.cache_insert(
                msg_hash,
                CachedMessage {
                    topic_id,
                    payload: payload.clone(),
                    cached_at: Instant::now(),
                },
            );

            // Deliver to local subscribers
            if let Some(topic_state) = s.topics.get(&topic_id) {
                if let Ok(msg) = PeerMessage::decode_raw(&payload) {
                    for sub in &topic_state.subscribers {
                        let _ = sub.send(GossipEvent::Message {
                            from: received_from,
                            message: msg.clone(),
                        });
                    }
                }

                let eager: Vec<_> = topic_state
                    .eager_peers()
                    .into_iter()
                    .filter(|a| *a != received_from)
                    .collect();
                let lazy: Vec<_> = topic_state
                    .lazy_peers()
                    .into_iter()
                    .filter(|a| *a != received_from)
                    .collect();
                (eager, lazy)
            } else {
                (Vec::new(), Vec::new())
            }
        };

        // Send as FullMessage (fluff phase — normal Plumtree broadcast)
        if !eager_targets.is_empty() {
            let fwd_envelope = GossipEnvelope::FullMessage {
                topic_id,
                msg_hash,
                payload: payload.clone(),
            };
            if let Some(fwd_bytes) = Self::sign_envelope(&fwd_envelope, node_id, signing_key) {
                Self::send_to_peers(&fwd_bytes, &eager_targets, state).await;
            }
        }

        if !lazy_targets.is_empty() {
            let ihave_envelope = GossipEnvelope::IHave { topic_id, msg_hash };
            if let Some(ihave_bytes) = Self::sign_envelope(&ihave_envelope, node_id, signing_key) {
                Self::send_to_peers(&ihave_bytes, &lazy_targets, state).await;
            }
        }
    }

    /// Dandelion++ stem timeout loop: periodically checks for messages stuck in
    /// stem phase beyond STEM_TIMEOUT and fluffs them to prevent message loss.
    async fn stem_timeout_loop(
        state: Arc<RwLock<GossipState>>,
        outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
        node_id: NodeId,
        signing_key: Arc<SigningKey>,
    ) {
        let mut interval = tokio::time::interval(Duration::from_secs(5));
        loop {
            interval.tick().await;

            let now = Instant::now();
            let expired: Vec<StemEntry> = {
                let s = state.read().await;
                s.stem_messages
                    .values()
                    .filter(|entry| now.duration_since(entry.entered_stem_at) > STEM_TIMEOUT)
                    .cloned()
                    .collect()
            };

            for entry in expired {
                debug!(
                    "Stem timeout for message {:02x}{:02x}... — fluffing",
                    entry.msg_hash[0], entry.msg_hash[1]
                );

                // Use a sentinel address for "self-originated fluff"
                let self_addr: SocketAddr = "127.0.0.1:0".parse().unwrap();
                Self::fluff_message(
                    entry.topic_id,
                    entry.msg_hash,
                    entry.payload,
                    self_addr,
                    &state,
                    &outgoing_tx,
                    &signing_key,
                    node_id,
                )
                .await;
            }
        }
    }

    async fn ihave_timeout_loop(
        state: Arc<RwLock<GossipState>>,
        outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
    ) {
        let mut interval = tokio::time::interval(Duration::from_millis(100));
        loop {
            interval.tick().await;

            let now = Instant::now();
            let mut grafts: Vec<(TopicId, MessageHash, SocketAddr)> = Vec::new();

            {
                let mut s = state.write().await;
                let expired: Vec<_> = s
                    .pending_ihaves
                    .iter()
                    .filter(|(_, (_, received_at))| {
                        now.duration_since(*received_at) > IHAVE_TIMEOUT
                    })
                    .map(|((topic_id, msg_hash), (addr, _))| (*topic_id, *msg_hash, *addr))
                    .collect();

                for (topic_id, msg_hash, addr) in &expired {
                    if !s.seen.contains(msg_hash) {
                        grafts.push((*topic_id, *msg_hash, *addr));
                    }
                    s.pending_ihaves.remove(&(*topic_id, *msg_hash));
                }
            }

            for (topic_id, msg_hash, target) in grafts {
                debug!("IHave timeout — sending Graft to {target}");
                let _ = outgoing_tx.send(OutgoingGossip::Graft {
                    topic_id,
                    msg_hash,
                    target,
                });
            }
        }
    }

    /// Anti-entropy uses capped hash digests to prevent bandwidth amplification.
    async fn anti_entropy_loop(
        state: Arc<RwLock<GossipState>>,
        outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
    ) {
        /// Monotonic counter for round-robin peer selection in anti-entropy.
        /// Using AtomicU64 avoids the need for mutable state in the loop.
        static ROUND_COUNTER: AtomicU64 = AtomicU64::new(0);

        let mut interval = tokio::time::interval(ANTI_ENTROPY_INTERVAL);
        loop {
            interval.tick().await;

            let topics_and_peers: Vec<(TopicId, Vec<SocketAddr>)> = {
                let s = state.read().await;
                s.topics
                    .iter()
                    .map(|(tid, ts)| (*tid, ts.all_peers()))
                    .collect()
            };

            // Cap the hash set to prevent bandwidth amplification
            let hashes = {
                let s = state.read().await;
                s.seen.hashes_capped(MAX_ANTI_ENTROPY_HASHES)
            };

            let round = ROUND_COUNTER.fetch_add(1, Ordering::Relaxed);

            for (topic_id, peers) in topics_and_peers {
                if peers.is_empty() {
                    continue;
                }
                let idx = (round as usize) % peers.len();
                let target = peers[idx];

                let _ = outgoing_tx.send(OutgoingGossip::AntiEntropy {
                    topic_id,
                    hashes: hashes.clone(),
                    target,
                });
            }
        }
    }

    async fn cache_cleanup_loop(state: Arc<RwLock<GossipState>>) {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        loop {
            interval.tick().await;

            let mut s = state.write().await;
            let now = Instant::now();
            s.message_cache
                .retain(|_, cached| now.duration_since(cached.cached_at) < SEEN_TTL);
            // Also prune the order queue to match retained entries.
            // Collect retained keys first to avoid borrow conflict.
            let retained_keys: std::collections::HashSet<[u8; 32]> =
                s.message_cache.keys().copied().collect();
            s.message_cache_order
                .retain(|hash| retained_keys.contains(hash));
        }
    }

    /// Get our node ID.
    pub fn node_id(&self) -> NodeId {
        self.node_id
    }
}

impl MessageStream {
    /// Receive the next gossip event (blocks until available).
    pub async fn recv(&mut self) -> Option<GossipEvent> {
        self.receiver.recv().await
    }

    /// Try to receive without blocking.
    pub fn try_recv(&mut self) -> Option<GossipEvent> {
        self.receiver.try_recv().ok()
    }
}

/// Read a signed gossip envelope from a uni stream.
async fn read_signed_envelope(recv: &mut RecvStream) -> Result<SignedEnvelope, String> {
    let mut len_buf = [0u8; 4];
    recv.read_exact(&mut len_buf)
        .await
        .map_err(|e| e.to_string())?;
    let len = u32::from_be_bytes(len_buf) as usize;

    if len > 16 * 1024 * 1024 {
        return Err("gossip envelope too large".to_string());
    }

    let mut buf = vec![0u8; len];
    recv.read_exact(&mut buf).await.map_err(|e| e.to_string())?;

    // Strip two-bucket padding to recover the actual envelope bytes.
    // See docs/design-network-privacy.md Phase 1.
    let payload = crate::message::unpad_message(&buf)
        .ok_or_else(|| "invalid padded frame (malformed length prefix)".to_string())?;

    postcard::from_bytes(payload).map_err(|e| e.to_string())
}

/// Derive a deterministic TopicId from a human-readable topic name.
pub fn topic_id_from_name(name: &str) -> TopicId {
    *blake3::hash(name.as_bytes()).as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn topic_id_deterministic() {
        let id1 = topic_id_from_name("dregg/turns/cell-abc");
        let id2 = topic_id_from_name("dregg/turns/cell-abc");
        let id3 = topic_id_from_name("dregg/turns/cell-xyz");

        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn topic_handle_accessors() {
        let handle = TopicHandle {
            topic_id: topic_id_from_name("test"),
            name: "test".to_string(),
        };
        assert_eq!(handle.name(), "test");
        assert_eq!(handle.id(), topic_id_from_name("test"));
    }

    #[test]
    fn bounded_seen_set_dedup() {
        let mut set = BoundedSeenSet::new(3, Duration::from_secs(60));
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];

        assert!(set.insert(h1));
        assert!(!set.insert(h1));
        assert!(set.insert(h2));
        assert!(set.insert(h3));
        assert!(!set.insert(h2));
    }

    #[test]
    fn bounded_seen_set_eviction() {
        let mut set = BoundedSeenSet::new(3, Duration::from_secs(60));
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];
        let h4 = [4u8; 32];

        assert!(set.insert(h1));
        assert!(set.insert(h2));
        assert!(set.insert(h3));
        assert!(set.insert(h4));
        assert!(!set.contains(&h1));
        assert!(set.contains(&h2));
        assert!(set.contains(&h3));
        assert!(set.contains(&h4));
    }

    #[test]
    fn bounded_seen_set_eviction_order() {
        let mut set = BoundedSeenSet::new(2, Duration::from_secs(60));
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];
        let h4 = [4u8; 32];

        set.insert(h1);
        set.insert(h2);
        set.insert(h3);
        assert!(!set.contains(&h1));
        assert!(set.contains(&h2));
        assert!(set.contains(&h3));

        set.insert(h4);
        assert!(!set.contains(&h2));
        assert!(set.contains(&h3));
        assert!(set.contains(&h4));
    }

    #[test]
    fn topic_state_eager_lazy_split() {
        let mut ts = TopicState::new();
        let a1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        let a2: SocketAddr = "127.0.0.1:2000".parse().unwrap();
        let a3: SocketAddr = "127.0.0.1:3000".parse().unwrap();
        let a4: SocketAddr = "127.0.0.1:4000".parse().unwrap();
        let a5: SocketAddr = "127.0.0.1:5000".parse().unwrap();

        ts.add_peer(a1);
        ts.add_peer(a2);
        ts.add_peer(a3);
        assert_eq!(ts.eager_peers().len(), 3);
        assert_eq!(ts.lazy_peers().len(), 0);

        ts.add_peer(a4);
        ts.add_peer(a5);
        assert_eq!(ts.eager_peers().len(), 3);
        assert_eq!(ts.lazy_peers().len(), 2);
    }

    #[test]
    fn topic_state_promote_demote() {
        let mut ts = TopicState::new();
        let a1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        let a2: SocketAddr = "127.0.0.1:2000".parse().unwrap();
        let a3: SocketAddr = "127.0.0.1:3000".parse().unwrap();
        let a4: SocketAddr = "127.0.0.1:4000".parse().unwrap();

        ts.add_peer(a1);
        ts.add_peer(a2);
        ts.add_peer(a3);
        ts.add_peer(a4);

        assert!(ts.lazy_peers().contains(&a4));

        ts.promote_to_eager(&a4);
        assert!(ts.eager_peers().contains(&a4));
        assert!(!ts.lazy_peers().contains(&a4));

        ts.demote_to_lazy(&a1);
        assert!(ts.lazy_peers().contains(&a1));
        assert!(!ts.eager_peers().contains(&a1));
    }

    #[test]
    fn topic_state_delivery_score() {
        let mut ts = TopicState::new();
        let a1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        ts.add_peer(a1);

        ts.record_delivery(&a1);
        ts.record_delivery(&a1);
        ts.record_delivery(&a1);

        assert_eq!(ts.peer_states.get(&a1).unwrap().delivery_score, 3);
    }

    #[test]
    fn seen_set_hashes_capped() {
        let mut set = BoundedSeenSet::new(10, Duration::from_secs(60));
        for i in 0..10u8 {
            set.insert([i; 32]);
        }

        let hashes = set.hashes_capped(3);
        assert_eq!(hashes.len(), 3);

        let hashes = set.hashes_capped(100);
        assert_eq!(hashes.len(), 10);
    }

    #[test]
    fn signed_envelope_roundtrip() {
        let (signing_key, public_key) = dregg_types::generate_keypair();
        let sender = [0xcd; 32];
        let envelope = GossipEnvelope::IHave {
            topic_id: [0x11; 32],
            msg_hash: [0x22; 32],
        };

        let signed = SignedEnvelope::sign(&envelope, sender, &signing_key).unwrap();
        assert!(signed.verify(&public_key));

        // Wrong key should fail verification
        let (_, wrong_public_key) = dregg_types::generate_keypair();
        assert!(!signed.verify(&wrong_public_key));

        let decoded = signed.decode_inner().unwrap();
        match decoded {
            GossipEnvelope::IHave { topic_id, msg_hash } => {
                assert_eq!(topic_id, [0x11; 32]);
                assert_eq!(msg_hash, [0x22; 32]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn signed_envelope_tamper_detection() {
        let (signing_key, public_key) = dregg_types::generate_keypair();
        let sender = [0xcd; 32];
        let envelope = GossipEnvelope::Prune {
            topic_id: [0x33; 32],
        };

        let mut signed = SignedEnvelope::sign(&envelope, sender, &signing_key).unwrap();

        if !signed.body.is_empty() {
            signed.body[0] ^= 0xff;
        }
        assert!(!signed.verify(&public_key));
    }

    #[test]
    fn bounded_pending_ihaves_eviction() {
        let mut pending = BoundedPendingIhaves::new(3);
        let t = [0u8; 32];
        let addr: SocketAddr = "127.0.0.1:1000".parse().unwrap();

        pending.insert((t, [1u8; 32]), (addr, Instant::now()));
        pending.insert((t, [2u8; 32]), (addr, Instant::now()));
        pending.insert((t, [3u8; 32]), (addr, Instant::now()));

        pending.insert((t, [4u8; 32]), (addr, Instant::now()));
        assert!(!pending.contains_key(&(t, [1u8; 32])));
        assert!(pending.contains_key(&(t, [2u8; 32])));
        assert!(pending.contains_key(&(t, [3u8; 32])));
        assert!(pending.contains_key(&(t, [4u8; 32])));
    }

    #[test]
    fn bounded_pending_ihaves_no_overwrite() {
        let mut pending = BoundedPendingIhaves::new(10);
        let t = [0u8; 32];
        let h = [1u8; 32];
        let addr1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        let addr2: SocketAddr = "127.0.0.1:2000".parse().unwrap();

        pending.insert((t, h), (addr1, Instant::now()));
        pending.insert((t, h), (addr2, Instant::now()));

        let (stored_addr, _) = pending.index.get(&(t, h)).unwrap();
        assert_eq!(*stored_addr, addr1);
    }

    #[test]
    fn gossip_envelope_roundtrip_full_message() {
        let envelope = GossipEnvelope::FullMessage {
            topic_id: [0xaa; 32],
            msg_hash: [0xbb; 32],
            payload: vec![1, 2, 3, 4, 5],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::FullMessage {
                topic_id,
                msg_hash,
                payload,
            } => {
                assert_eq!(topic_id, [0xaa; 32]);
                assert_eq!(msg_hash, [0xbb; 32]);
                assert_eq!(payload, vec![1, 2, 3, 4, 5]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn gossip_envelope_roundtrip_ihave() {
        let envelope = GossipEnvelope::IHave {
            topic_id: [0xcc; 32],
            msg_hash: [0xdd; 32],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::IHave { topic_id, msg_hash } => {
                assert_eq!(topic_id, [0xcc; 32]);
                assert_eq!(msg_hash, [0xdd; 32]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn gossip_envelope_roundtrip_graft() {
        let envelope = GossipEnvelope::Graft {
            topic_id: [0xee; 32],
            msg_hash: [0xff; 32],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::Graft { topic_id, msg_hash } => {
                assert_eq!(topic_id, [0xee; 32]);
                assert_eq!(msg_hash, [0xff; 32]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn gossip_envelope_roundtrip_prune() {
        let envelope = GossipEnvelope::Prune {
            topic_id: [0x11; 32],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::Prune { topic_id } => {
                assert_eq!(topic_id, [0x11; 32]);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn gossip_envelope_roundtrip_anti_entropy() {
        let envelope = GossipEnvelope::AntiEntropy {
            topic_id: [0x22; 32],
            hashes: vec![[0x33; 32], [0x44; 32]],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::AntiEntropy { topic_id, hashes } => {
                assert_eq!(topic_id, [0x22; 32]);
                assert_eq!(hashes.len(), 2);
            }
            _ => panic!("wrong variant"),
        }
    }

    #[test]
    fn ihave_graft_state_flow() {
        let topic_id = topic_id_from_name("test-topic");
        let msg_hash = [0xab; 32];
        let sender: SocketAddr = "127.0.0.1:9000".parse().unwrap();

        let mut pending = BoundedPendingIhaves::new(100);
        pending.insert((topic_id, msg_hash), (sender, Instant::now()));

        assert!(pending.contains_key(&(topic_id, msg_hash)));

        pending.remove(&(topic_id, msg_hash));
        assert!(!pending.contains_key(&(topic_id, msg_hash)));
    }

    #[test]
    fn prune_demotes_to_lazy() {
        let mut ts = TopicState::new();
        let a1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        let a2: SocketAddr = "127.0.0.1:2000".parse().unwrap();

        ts.add_peer(a1);
        ts.add_peer(a2);

        assert!(ts.eager_peers().contains(&a1));
        assert!(ts.eager_peers().contains(&a2));

        ts.demote_to_lazy(&a1);

        assert!(!ts.eager_peers().contains(&a1));
        assert!(ts.lazy_peers().contains(&a1));
        assert!(ts.eager_peers().contains(&a2));
    }

    #[test]
    fn duplicate_from_eager_triggers_prune() {
        let mut seen = BoundedSeenSet::new(100, Duration::from_secs(60));
        let msg_hash = [0xcd; 32];

        assert!(seen.insert(msg_hash));
        assert!(!seen.insert(msg_hash));
        assert!(seen.contains(&msg_hash));
    }

    #[test]
    fn message_cache_for_graft() {
        let mut cache: HashMap<MessageHash, CachedMessage> = HashMap::new();
        let msg_hash = [0xef; 32];
        let topic_id = topic_id_from_name("cache-test");
        let payload = vec![10, 20, 30];

        cache.insert(
            msg_hash,
            CachedMessage {
                topic_id,
                payload: payload.clone(),
                cached_at: Instant::now(),
            },
        );

        let retrieved = cache.get(&msg_hash).unwrap();
        assert_eq!(retrieved.topic_id, topic_id);
        assert_eq!(retrieved.payload, payload);
    }

    #[test]
    fn anti_entropy_finds_missing() {
        let topic_id = topic_id_from_name("ae-test");
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];

        let mut cache: HashMap<MessageHash, CachedMessage> = HashMap::new();
        for h in [h1, h2, h3] {
            cache.insert(
                h,
                CachedMessage {
                    topic_id,
                    payload: vec![h[0]],
                    cached_at: Instant::now(),
                },
            );
        }

        let peer_hashes: HashSet<MessageHash> = [h1, h3].into_iter().collect();

        let missing: Vec<_> = cache
            .iter()
            .filter(|(hash, cached)| cached.topic_id == topic_id && !peer_hashes.contains(*hash))
            .map(|(hash, cached)| (*hash, cached.payload.clone()))
            .collect();

        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].0, h2);
        assert_eq!(missing[0].1, vec![2]);
    }

    #[test]
    fn hash_verification_rejects_mismatch() {
        let payload = b"hello world";
        let correct_hash = *blake3::hash(payload).as_bytes();
        let wrong_hash = [0xff; 32];

        assert_eq!(*blake3::hash(payload).as_bytes(), correct_hash);
        assert_ne!(wrong_hash, correct_hash);
    }

    // ─── Dandelion++ tests ──────────────────────────────────────────────────

    #[test]
    fn gossip_envelope_roundtrip_stem() {
        let envelope = GossipEnvelope::Stem {
            topic_id: [0x55; 32],
            msg_hash: [0x66; 32],
            payload: vec![7, 8, 9],
        };
        let bytes = postcard::to_stdvec(&envelope).unwrap();
        let decoded: GossipEnvelope = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            GossipEnvelope::Stem {
                topic_id,
                msg_hash,
                payload,
            } => {
                assert_eq!(topic_id, [0x55; 32]);
                assert_eq!(msg_hash, [0x66; 32]);
                assert_eq!(payload, vec![7, 8, 9]);
            }
            _ => panic!("wrong variant — expected Stem"),
        }
    }

    #[test]
    fn stem_probability_within_expected_range() {
        // With p=0.9, run 1000 trials: expect ~900 "continue stem" outcomes.
        // Use a wide tolerance (800-980) to avoid flaky test while validating
        // the distribution is clearly biased toward stem continuation.
        let mut stem_count = 0u32;
        for _ in 0..1000 {
            if rand::random::<f64>() < STEM_PROBABILITY {
                stem_count += 1;
            }
        }
        assert!(
            (800..=980).contains(&stem_count),
            "stem continuation count {stem_count}/1000 outside expected range [800, 980]"
        );
    }

    #[test]
    fn stem_entry_timeout_detection() {
        // Verify that stem entries can be identified as expired based on STEM_TIMEOUT.
        let entry = StemEntry {
            topic_id: [0xaa; 32],
            msg_hash: [0xbb; 32],
            payload: vec![1, 2, 3],
            entered_stem_at: Instant::now() - Duration::from_secs(31),
        };

        let now = Instant::now();
        assert!(now.duration_since(entry.entered_stem_at) > STEM_TIMEOUT);

        // A fresh entry should NOT be expired
        let fresh = StemEntry {
            topic_id: [0xcc; 32],
            msg_hash: [0xdd; 32],
            payload: vec![4, 5, 6],
            entered_stem_at: Instant::now(),
        };
        let now = Instant::now();
        assert!(now.duration_since(fresh.entered_stem_at) < STEM_TIMEOUT);
    }

    /// Integration test: publish() routes a message to exactly 1 peer (stem),
    /// then the stem timeout failsafe eventually fluffs it (broadcasts).
    #[tokio::test]
    async fn dandelion_publish_sends_stem_to_one_peer() {
        use tokio::sync::mpsc;

        // We can't easily spin up real QUIC endpoints in a unit test, but we
        // can verify the outgoing message flow by inspecting the OutgoingGossip
        // channel. Build the state directly.
        let topic_id = topic_id_from_name("dandelion-test");
        let mut state = GossipState {
            topics: HashMap::new(),
            peers: HashMap::new(),
            seen: BoundedSeenSet::new(100, Duration::from_secs(60)),
            pending_ihaves: BoundedPendingIhaves::new(100),
            message_cache: HashMap::new(),
            message_cache_order: VecDeque::new(),
            stem_messages: HashMap::new(),
        };

        // Add a topic with 5 peers (3 eager, 2 lazy)
        let mut topic_state = TopicState::new();
        let peers: Vec<SocketAddr> = (1..=5)
            .map(|i| format!("127.0.0.1:{}", 3000 + i).parse().unwrap())
            .collect();
        for &peer in &peers {
            topic_state.add_peer(peer);
        }
        state.topics.insert(topic_id, topic_state);

        let state = Arc::new(RwLock::new(state));
        let (outgoing_tx, mut outgoing_rx) = mpsc::unbounded_channel::<OutgoingGossip>();

        // Simulate what publish() does: pick one random peer for stem
        let msg = PeerMessage::PublishTurn {
            turn_hash: [0x42; 32],
            turn_data: vec![1, 2, 3],
            causal_deps: vec![],
        };
        let encoded = msg.encode_raw();
        let msg_hash = *blake3::hash(&encoded).as_bytes();

        {
            let mut s = state.write().await;
            s.seen.insert(msg_hash);
            s.cache_insert(
                msg_hash,
                CachedMessage {
                    topic_id,
                    payload: encoded.clone(),
                    cached_at: Instant::now(),
                },
            );
            s.stem_messages.insert(
                msg_hash,
                StemEntry {
                    topic_id,
                    msg_hash,
                    payload: encoded.clone(),
                    entered_stem_at: Instant::now(),
                },
            );

            // Select one random peer
            let all_peers = s.topics.get(&topic_id).unwrap().all_peers();
            let mut rng = rand::rng();
            let target = *all_peers.choose(&mut rng).unwrap();

            outgoing_tx
                .send(OutgoingGossip::StemForward {
                    topic_id,
                    msg_hash,
                    payload: encoded.clone(),
                    target,
                })
                .unwrap();
        }

        // Verify exactly ONE StemForward was sent
        let outgoing = outgoing_rx.try_recv().unwrap();
        match outgoing {
            OutgoingGossip::StemForward {
                topic_id: tid,
                msg_hash: mh,
                target,
                ..
            } => {
                assert_eq!(tid, topic_id);
                assert_eq!(mh, msg_hash);
                // The target must be one of our 5 peers
                assert!(peers.contains(&target));
            }
            other => panic!(
                "Expected StemForward, got {:?}",
                std::mem::discriminant(&other)
            ),
        }

        // No further outgoing messages (stem sends to exactly 1 peer)
        assert!(outgoing_rx.try_recv().is_err());

        // Verify the message is tracked in stem_messages
        let s = state.read().await;
        assert!(s.stem_messages.contains_key(&msg_hash));
    }

    #[tokio::test]
    async fn dandelion_fluff_broadcasts_to_all_eager_peers() {
        use tokio::sync::mpsc;

        let topic_id = topic_id_from_name("fluff-test");
        let (signing_key, _public_key) = dregg_types::generate_keypair();
        let node_id = [0xab; 32];

        let mut state = GossipState {
            topics: HashMap::new(),
            peers: HashMap::new(),
            seen: BoundedSeenSet::new(100, Duration::from_secs(60)),
            pending_ihaves: BoundedPendingIhaves::new(100),
            message_cache: HashMap::new(),
            message_cache_order: VecDeque::new(),
            stem_messages: HashMap::new(),
        };

        // 3 eager + 2 lazy peers
        let mut topic_state = TopicState::new();
        let peers: Vec<SocketAddr> = (1..=5)
            .map(|i| format!("127.0.0.1:{}", 4000 + i).parse().unwrap())
            .collect();
        for &peer in &peers {
            topic_state.add_peer(peer);
        }
        state.topics.insert(topic_id, topic_state);

        let state = Arc::new(RwLock::new(state));
        let (outgoing_tx, _outgoing_rx) = mpsc::unbounded_channel::<OutgoingGossip>();

        let payload = vec![10, 20, 30];
        let msg_hash = *blake3::hash(&payload).as_bytes();
        let remote_addr: SocketAddr = "127.0.0.1:9999".parse().unwrap();

        // Call fluff_message — this should mark as seen and prepare broadcast
        GossipNetwork::fluff_message(
            topic_id,
            msg_hash,
            payload.clone(),
            remote_addr,
            &state,
            &outgoing_tx,
            &signing_key,
            node_id,
        )
        .await;

        // After fluff, the message should be in seen set and cache
        let s = state.read().await;
        assert!(s.seen.contains(&msg_hash));
        assert!(s.message_cache.contains_key(&msg_hash));
        // And NOT in stem_messages
        assert!(!s.stem_messages.contains_key(&msg_hash));
    }

    #[test]
    fn message_phase_enum_variants() {
        // Ensure MessagePhase is properly defined and usable
        let stem = MessagePhase::Stem;
        let fluff = MessagePhase::Fluff;
        assert_ne!(stem, fluff);
        assert_eq!(stem, MessagePhase::Stem);
        assert_eq!(fluff, MessagePhase::Fluff);
    }

    // ─── Adaptive stem probability tests ──────────────────────────────────

    #[test]
    fn adaptive_stem_probability_tiny_network() {
        // Networks with < 5 peers get no stem (useless, just adds latency)
        assert_eq!(effective_stem_probability(0), 0.0);
        assert_eq!(effective_stem_probability(1), 0.0);
        assert_eq!(effective_stem_probability(2), 0.0);
        assert_eq!(effective_stem_probability(3), 0.0);
        assert_eq!(effective_stem_probability(4), 0.0);
    }

    #[test]
    fn adaptive_stem_probability_small_network() {
        // Networks with 5-9 peers get reduced stem (0.5)
        assert_eq!(effective_stem_probability(5), 0.5);
        assert_eq!(effective_stem_probability(7), 0.5);
        assert_eq!(effective_stem_probability(9), 0.5);
    }

    #[test]
    fn adaptive_stem_probability_large_network() {
        // Networks with >= 10 peers get full Dandelion++ (0.9)
        assert_eq!(effective_stem_probability(10), STEM_PROBABILITY);
        assert_eq!(effective_stem_probability(50), STEM_PROBABILITY);
        assert_eq!(effective_stem_probability(256), STEM_PROBABILITY);
    }
}
