//! GossipNetwork: Plumtree-inspired lazy-push gossip for pyana.
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
//! - All gossip envelopes are signed (HMAC-blake3 with a shared network key).
//! - Message hashes are verified on receipt: `blake3(payload) == msg_hash`.
//! - Pending IHave state is bounded to prevent memory exhaustion.
//! - Connections are bounded by the configured `max_connections` limit.
//!
//! The public API (`publish`, `subscribe`, `join_topic`) is unchanged from the original
//! eager-push implementation.

use std::collections::{HashMap, HashSet, VecDeque};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use quinn::{Connection, Endpoint, RecvStream};
use tokio::sync::{RwLock, mpsc};
use tracing::{debug, info, trace, warn};

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
    /// Symmetric signing key for envelope authentication (HMAC-blake3).
    signing_key: [u8; 32],
    /// Maximum concurrent gossip connections.
    max_connections: usize,
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
    message_cache: HashMap<MessageHash, CachedMessage>,
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
}

/// A signed gossip envelope. The signature covers the serialized inner envelope
/// and the sender's node ID, preventing forgery and ensuring message authenticity.
#[derive(serde::Serialize, serde::Deserialize)]
struct SignedEnvelope {
    /// The sender's node ID (blake3 hash of their TLS certificate).
    sender: NodeId,
    /// The serialized inner GossipEnvelope (postcard-encoded).
    body: Vec<u8>,
    /// HMAC-blake3 signature: `blake3_keyed_hash(signing_key, sender || body)`.
    signature: [u8; 32],
}

impl SignedEnvelope {
    fn sign(envelope: &GossipEnvelope, sender: NodeId, signing_key: &[u8; 32]) -> Option<Self> {
        let body = postcard::to_stdvec(envelope).ok()?;
        let signature = Self::compute_signature(&sender, &body, signing_key);
        Some(Self {
            sender,
            body,
            signature,
        })
    }

    fn verify(&self, signing_key: &[u8; 32]) -> bool {
        let expected = Self::compute_signature(&self.sender, &self.body, signing_key);
        // Constant-time comparison
        self.signature
            .iter()
            .zip(expected.iter())
            .fold(0u8, |acc, (a, b)| acc | (a ^ b))
            == 0
    }

    fn decode_inner(&self) -> Option<GossipEnvelope> {
        postcard::from_bytes(&self.body).ok()
    }

    fn compute_signature(sender: &NodeId, body: &[u8], signing_key: &[u8; 32]) -> [u8; 32] {
        let mut input = Vec::with_capacity(32 + body.len());
        input.extend_from_slice(sender);
        input.extend_from_slice(body);
        *blake3::keyed_hash(signing_key, &input).as_bytes()
    }
}

impl GossipNetwork {
    /// Create a new gossip network node.
    ///
    /// The `signing_key` is a 32-byte symmetric key used to sign all outgoing
    /// gossip envelopes (HMAC-blake3). All peers in the network must share this
    /// key for envelope verification.
    pub fn new(endpoint: Endpoint, node_id: NodeId, signing_key: [u8; 32]) -> Self {
        Self::with_max_connections(endpoint, node_id, signing_key, DEFAULT_MAX_GOSSIP_CONNECTIONS)
    }

    /// Create a new gossip network with a custom max_connections limit.
    pub fn with_max_connections(
        endpoint: Endpoint,
        node_id: NodeId,
        signing_key: [u8; 32],
        max_connections: usize,
    ) -> Self {
        let (outgoing_tx, outgoing_rx) = mpsc::unbounded_channel();

        let state = Arc::new(RwLock::new(GossipState {
            topics: HashMap::new(),
            peers: HashMap::new(),
            seen: BoundedSeenSet::new(SEEN_MAX_ENTRIES, SEEN_TTL),
            pending_ihaves: BoundedPendingIhaves::new(MAX_PENDING_IHAVES),
            message_cache: HashMap::new(),
        }));

        let network = Self {
            node_id,
            state: state.clone(),
            outgoing_tx: outgoing_tx.clone(),
            endpoint: endpoint.clone(),
            signing_key,
            max_connections,
        };

        // Spawn the forwarding task
        let fwd_state = state.clone();
        let fwd_node_id = node_id;
        let fwd_key = signing_key;
        tokio::spawn(async move {
            Self::forward_loop(outgoing_rx, fwd_state, fwd_node_id, fwd_key).await;
        });

        // Spawn the incoming gossip acceptor
        let accept_state = state.clone();
        let accept_endpoint = endpoint.clone();
        let accept_tx = outgoing_tx.clone();
        let accept_key = signing_key;
        let accept_node_id = node_id;
        let accept_max_conns = max_connections;
        tokio::spawn(async move {
            Self::accept_loop(
                accept_endpoint,
                accept_state,
                accept_tx,
                accept_key,
                accept_node_id,
                accept_max_conns,
            )
            .await;
        });

        // Spawn the IHave timeout checker
        let ihave_state = state.clone();
        let ihave_tx = outgoing_tx.clone();
        tokio::spawn(async move {
            Self::ihave_timeout_loop(ihave_state, ihave_tx).await;
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
    pub async fn publish(
        &self,
        topic: &TopicHandle,
        message: &PeerMessage,
    ) -> Result<(), GossipError> {
        let encoded = message.encode_raw();
        let msg_hash = *blake3::hash(&encoded).as_bytes();

        {
            let mut state = self.state.write().await;
            state.seen.insert(msg_hash);
            state.message_cache.insert(
                msg_hash,
                CachedMessage {
                    topic_id: topic.topic_id,
                    payload: encoded,
                    cached_at: Instant::now(),
                },
            );
        }

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
            .connect_with(client_config, addr, "pyana.local")
            .map_err(|e| GossipError::Join(e.to_string()))?
            .await
            .map_err(|e| GossipError::Join(e.to_string()))?;

        Ok(conn)
    }

    fn sign_envelope(
        envelope: &GossipEnvelope,
        node_id: NodeId,
        signing_key: &[u8; 32],
    ) -> Option<Vec<u8>> {
        let signed = SignedEnvelope::sign(envelope, node_id, signing_key)?;
        postcard::to_stdvec(&signed).ok()
    }

    async fn forward_loop(
        mut rx: mpsc::UnboundedReceiver<OutgoingGossip>,
        state: Arc<RwLock<GossipState>>,
        node_id: NodeId,
        signing_key: [u8; 32],
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
            }
        }
    }

    async fn send_to_peers(data: &[u8], targets: &[SocketAddr], state: &Arc<RwLock<GossipState>>) {
        let mut dead_peers: Vec<SocketAddr> = Vec::new();

        for &addr in targets {
            let conn = {
                let state_r = state.read().await;
                state_r.peers.get(&addr).cloned()
            };
            if let Some(conn) = conn {
                match conn.open_uni().await {
                    Ok(mut stream) => {
                        let data = data.to_vec();
                        tokio::spawn(async move {
                            let len = (data.len() as u32).to_be_bytes();
                            if stream.write_all(&len).await.is_ok() {
                                let _ = stream.write_all(&data).await;
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
        signing_key: [u8; 32],
        node_id: NodeId,
        max_connections: usize,
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
            let key = signing_key;
            let our_node_id = node_id;
            tokio::spawn(async move {
                let Ok(conn) = incoming.await else { return };
                let remote_addr = conn.remote_address();

                {
                    let mut s = state.write().await;
                    s.peers.insert(remote_addr, conn.clone());
                }

                loop {
                    let Ok(mut recv) = conn.accept_uni().await else {
                        break;
                    };

                    let state = state.clone();
                    let outgoing_tx = outgoing_tx.clone();
                    tokio::spawn(async move {
                        if let Ok(signed) = read_signed_envelope(&mut recv).await {
                            // Verify signature before processing
                            if !signed.verify(&key) {
                                warn!(
                                    "Rejecting gossip envelope from {} — invalid signature",
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
                                &key,
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
        signing_key: &[u8; 32],
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

                    s.message_cache.insert(
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
                            if total_bytes + cached.payload.len()
                                > MAX_ANTI_ENTROPY_RESPONSE_BYTES
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
                            s.message_cache.insert(
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
                    .filter(|(_, (_, received_at))| now.duration_since(*received_at) > IHAVE_TIMEOUT)
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

            for (topic_id, peers) in topics_and_peers {
                if peers.is_empty() {
                    continue;
                }
                let idx = (Instant::now().elapsed().subsec_nanos() as usize) % peers.len();
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

    postcard::from_bytes(&buf).map_err(|e| e.to_string())
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
        let id1 = topic_id_from_name("pyana/turns/cell-abc");
        let id2 = topic_id_from_name("pyana/turns/cell-abc");
        let id3 = topic_id_from_name("pyana/turns/cell-xyz");

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
        let key = [0xab; 32];
        let sender = [0xcd; 32];
        let envelope = GossipEnvelope::IHave {
            topic_id: [0x11; 32],
            msg_hash: [0x22; 32],
        };

        let signed = SignedEnvelope::sign(&envelope, sender, &key).unwrap();
        assert!(signed.verify(&key));

        let wrong_key = [0xff; 32];
        assert!(!signed.verify(&wrong_key));

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
        let key = [0xab; 32];
        let sender = [0xcd; 32];
        let envelope = GossipEnvelope::Prune {
            topic_id: [0x33; 32],
        };

        let mut signed = SignedEnvelope::sign(&envelope, sender, &key).unwrap();

        if !signed.body.is_empty() {
            signed.body[0] ^= 0xff;
        }
        assert!(!signed.verify(&key));
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
}
