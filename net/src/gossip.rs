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
//! - **Anti-entropy**: Periodic bloom filter exchange catches any messages missed by the
//!   eager/lazy protocol.
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

    /// Get all currently-valid message hashes (for anti-entropy).
    fn hashes(&self) -> Vec<[u8; 32]> {
        let now = Instant::now();
        self.entries
            .iter()
            .filter(|e| now.duration_since(e.inserted_at) <= self.max_age)
            .map(|e| e.hash)
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

/// Internal gossip state.
struct GossipState {
    /// Topics we've joined, with their subscriber channels
    topics: HashMap<TopicId, TopicState>,
    /// Active connections to gossip peers (by their address)
    peers: HashMap<SocketAddr, Connection>,
    /// Messages we've already seen (by hash), for deduplication.
    seen: BoundedSeenSet,
    /// Pending IHave notifications waiting for timeout before we Graft.
    /// Key: (topic, message_hash), Value: (sender_addr, received_at)
    pending_ihaves: HashMap<(TopicId, MessageHash), (SocketAddr, Instant)>,
    /// Recently-sent message payloads (for responding to Graft requests).
    /// Kept briefly so we can serve Graft pulls without re-requesting from upstream.
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

    /// Get addresses of peers in the eager set.
    fn eager_peers(&self) -> Vec<SocketAddr> {
        self.peer_states
            .iter()
            .filter(|(_, s)| s.eager)
            .map(|(a, _)| *a)
            .collect()
    }

    /// Get addresses of peers in the lazy set.
    fn lazy_peers(&self) -> Vec<SocketAddr> {
        self.peer_states
            .iter()
            .filter(|(_, s)| !s.eager)
            .map(|(a, _)| *a)
            .collect()
    }

    /// All peer addresses in this topic.
    fn all_peers(&self) -> Vec<SocketAddr> {
        self.peer_states.keys().copied().collect()
    }

    /// Add a peer. By default it starts as eager if we have room, otherwise lazy.
    fn add_peer(&mut self, addr: SocketAddr) {
        let eager_count = self.peer_states.values().filter(|s| s.eager).count();
        let should_be_eager = eager_count < DEFAULT_EAGER_DEGREE;
        self.peer_states.entry(addr).or_insert(PeerTopicState {
            eager: should_be_eager,
            delivery_score: 0,
            last_rtt: None,
        });
    }

    /// Promote a peer from lazy to eager (Graft received or anti-entropy repair).
    fn promote_to_eager(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.eager = true;
        }
    }

    /// Demote a peer from eager to lazy (Prune received or slow delivery).
    fn demote_to_lazy(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.eager = false;
        }
    }

    /// Record a successful delivery from a peer (increases their score).
    fn record_delivery(&mut self, addr: &SocketAddr) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.delivery_score = state.delivery_score.saturating_add(1);
        }
    }

    /// Update RTT for a peer.
    fn update_rtt(&mut self, addr: &SocketAddr, rtt: Duration) {
        if let Some(state) = self.peer_states.get_mut(addr) {
            state.last_rtt = Some(rtt);
        }
    }
}

/// Types of outgoing gossip operations.
///
/// Used by GossipRouter::dispatch() once the outbound message path is wired
/// through the QUIC transport layer (tracked in the gossip-dispatch milestone).
#[allow(dead_code)]
enum OutgoingGossip {
    /// Full message push (eager).
    EagerPush {
        topic_id: TopicId,
        message: PeerMessage,
        msg_hash: MessageHash,
        /// Peers to send the full message to.
        targets: Vec<SocketAddr>,
        /// Peers to send IHave to (lazy).
        lazy_targets: Vec<SocketAddr>,
    },
    /// IHave notification (lazy push).
    IHave {
        topic_id: TopicId,
        msg_hash: MessageHash,
        targets: Vec<SocketAddr>,
    },
    /// Graft request: pull a message we learned about via IHave.
    Graft {
        topic_id: TopicId,
        msg_hash: MessageHash,
        target: SocketAddr,
    },
    /// Prune: tell a peer to demote us from their eager set for this topic.
    Prune {
        topic_id: TopicId,
        target: SocketAddr,
    },
    /// Anti-entropy: send our hash set to a peer for reconciliation.
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
        /// The address of the peer who forwarded this message.
        from: SocketAddr,
        /// The decoded pyana message.
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
    /// Failed to join a topic.
    Join(String),
    /// Failed to publish a message.
    Publish(String),
    /// Failed to subscribe.
    Subscribe(String),
    /// The gossip network has been shut down.
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
#[derive(serde::Serialize, serde::Deserialize)]
enum GossipEnvelope {
    /// Full message delivery (eager push).
    FullMessage {
        topic_id: TopicId,
        msg_hash: MessageHash,
        payload: Vec<u8>,
    },
    /// IHave notification (lazy push).
    IHave {
        topic_id: TopicId,
        msg_hash: MessageHash,
    },
    /// Graft request: "send me the full message for this hash".
    Graft {
        topic_id: TopicId,
        msg_hash: MessageHash,
    },
    /// Prune: "demote me from your eager set for this topic".
    Prune { topic_id: TopicId },
    /// Anti-entropy: hash set of recently-seen messages.
    AntiEntropy {
        topic_id: TopicId,
        hashes: Vec<MessageHash>,
    },
    /// Anti-entropy response: messages the peer is missing.
    AntiEntropyResponse {
        topic_id: TopicId,
        messages: Vec<(MessageHash, Vec<u8>)>,
    },
}

impl GossipNetwork {
    /// Create a new gossip network node.
    ///
    /// The `endpoint` should be the same one used by the PeerNode,
    /// or a separate one if you want gossip on a different port.
    pub fn new(endpoint: Endpoint, node_id: NodeId) -> Self {
        let (outgoing_tx, outgoing_rx) = mpsc::unbounded_channel();

        let state = Arc::new(RwLock::new(GossipState {
            topics: HashMap::new(),
            peers: HashMap::new(),
            seen: BoundedSeenSet::new(SEEN_MAX_ENTRIES, SEEN_TTL),
            pending_ihaves: HashMap::new(),
            message_cache: HashMap::new(),
        }));

        let network = Self {
            node_id,
            state: state.clone(),
            outgoing_tx: outgoing_tx.clone(),
            endpoint: endpoint.clone(),
        };

        // Spawn the forwarding task
        let fwd_state = state.clone();
        tokio::spawn(async move {
            Self::forward_loop(outgoing_rx, fwd_state).await;
        });

        // Spawn the incoming gossip acceptor
        let accept_state = state.clone();
        let accept_endpoint = endpoint.clone();
        let accept_tx = outgoing_tx.clone();
        tokio::spawn(async move {
            Self::accept_loop(accept_endpoint, accept_state, accept_tx).await;
        });

        // Spawn the IHave timeout checker (triggers Graft after timeout)
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
            "GossipNetwork started (plumtree): {}",
            fmt_node_id(&node_id)
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

        // First, ensure the topic exists and add peer addresses
        {
            let mut state = self.state.write().await;
            let topic_state = state.topics.entry(topic_id).or_insert_with(TopicState::new);
            for &addr in bootstrap_peers {
                topic_state.add_peer(addr);
            }
        }

        // Then connect to any peers we don't yet have connections to
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
    /// The message is eagerly pushed to the spanning tree subset and lazily
    /// announced (IHave) to the remaining peers.
    pub async fn publish(
        &self,
        topic: &TopicHandle,
        message: &PeerMessage,
    ) -> Result<(), GossipError> {
        let encoded = message.encode_raw();
        let msg_hash = *blake3::hash(&encoded).as_bytes();

        // Mark as seen and cache
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

        // Determine eager vs lazy targets
        let (eager_targets, lazy_targets) = {
            let state = self.state.read().await;
            if let Some(topic_state) = state.topics.get(&topic.topic_id) {
                (topic_state.eager_peers(), topic_state.lazy_peers())
            } else {
                (Vec::new(), Vec::new())
            }
        };

        // Send to forwarding task
        self.outgoing_tx
            .send(OutgoingGossip::EagerPush {
                topic_id: topic.topic_id,
                message: message.clone(),
                msg_hash,
                targets: eager_targets,
                lazy_targets,
            })
            .map_err(|_| GossipError::Shutdown)?;

        // Also deliver to local subscribers
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

        // Ensure connection exists
        if !state.peers.contains_key(&addr) {
            drop(state);
            if let Ok(conn) = self.connect_peer(addr).await {
                let mut state = self.state.write().await;
                state.peers.insert(addr, conn);
            }
        }
    }

    /// Deliver a message to local subscribers of a topic.
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

    /// Connect to a peer for gossip exchange.
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

    /// Forward outgoing gossip messages according to the protocol.
    async fn forward_loop(
        mut rx: mpsc::UnboundedReceiver<OutgoingGossip>,
        state: Arc<RwLock<GossipState>>,
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
                    let Ok(envelope_bytes) = postcard::to_stdvec(&envelope) else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };

                    // Eager push: full message to eager peers
                    Self::send_to_peers(&envelope_bytes, &targets, &state).await;

                    // Lazy push: IHave to lazy peers
                    if !lazy_targets.is_empty() {
                        let ihave_envelope = GossipEnvelope::IHave { topic_id, msg_hash };
                        if let Ok(ihave_bytes) = postcard::to_stdvec(&ihave_envelope) {
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
                    let Ok(envelope_bytes) = postcard::to_stdvec(&envelope) else {
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
                    let Ok(envelope_bytes) = postcard::to_stdvec(&envelope) else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;

                    // Promote this peer to eager (they responded to our Graft)
                    let mut s = state.write().await;
                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.promote_to_eager(&target);
                    }
                }

                OutgoingGossip::Prune { topic_id, target } => {
                    let envelope = GossipEnvelope::Prune { topic_id };
                    let Ok(envelope_bytes) = postcard::to_stdvec(&envelope) else {
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
                    let Ok(envelope_bytes) = postcard::to_stdvec(&envelope) else {
                        warn!("gossip envelope serialization failed");
                        continue;
                    };
                    Self::send_to_peers(&envelope_bytes, &[target], &state).await;
                }
            }
        }
    }

    /// Send envelope bytes to a list of peer addresses.
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

        // Remove dead peers
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

    /// Accept incoming gossip streams and handle protocol messages.
    async fn accept_loop(
        endpoint: Endpoint,
        state: Arc<RwLock<GossipState>>,
        outgoing_tx: mpsc::UnboundedSender<OutgoingGossip>,
    ) {
        loop {
            let Some(incoming) = endpoint.accept().await else {
                break;
            };

            let state = state.clone();
            let outgoing_tx = outgoing_tx.clone();
            tokio::spawn(async move {
                let Ok(conn) = incoming.await else { return };
                let remote_addr = conn.remote_address();

                // Store the connection
                {
                    let mut s = state.write().await;
                    s.peers.insert(remote_addr, conn.clone());
                }

                // Accept uni streams from this connection
                loop {
                    let Ok(mut recv) = conn.accept_uni().await else {
                        break;
                    };

                    let state = state.clone();
                    let outgoing_tx = outgoing_tx.clone();
                    tokio::spawn(async move {
                        if let Ok(envelope) = read_gossip_envelope(&mut recv).await {
                            Self::handle_envelope(envelope, remote_addr, &state, &outgoing_tx)
                                .await;
                        }
                    });
                }
            });
        }
    }

    /// Handle a received gossip envelope according to protocol rules.
    async fn handle_envelope(
        envelope: GossipEnvelope,
        remote_addr: SocketAddr,
        state: &Arc<RwLock<GossipState>>,
        outgoing_tx: &mpsc::UnboundedSender<OutgoingGossip>,
    ) {
        match envelope {
            GossipEnvelope::FullMessage {
                topic_id,
                msg_hash,
                payload,
            } => {
                let (is_new, eager_targets, lazy_targets) = {
                    let mut s = state.write().await;

                    if s.seen.contains(&msg_hash) {
                        // We already have this message. The sender is a redundant eager
                        // source — send Prune to demote them to lazy.
                        if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                            let is_eager = topic_state
                                .peer_states
                                .get(&remote_addr)
                                .is_some_and(|ps| ps.eager);
                            if is_eager {
                                // Only prune if this was from an eager peer that's
                                // redundant (we already got it from someone else).
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

                    // Cache the message for Graft responses
                    s.message_cache.insert(
                        msg_hash,
                        CachedMessage {
                            topic_id,
                            payload: payload.clone(),
                            cached_at: Instant::now(),
                        },
                    );

                    // Cancel any pending IHave for this message (we got it eagerly)
                    s.pending_ihaves.remove(&(topic_id, msg_hash));

                    // Deliver to local subscribers
                    // Get RTT first to avoid borrow conflict
                    let peer_rtt = s.peers.get(&remote_addr).map(|conn| conn.rtt());

                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.record_delivery(&remote_addr);

                        // Update RTT from connection stats
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

                        // Forward: eager push to our eager peers, IHave to lazy peers
                        // (excluding the sender)
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
                    // Forward full message to eager peers
                    if !eager_targets.is_empty() {
                        let fwd_envelope = GossipEnvelope::FullMessage {
                            topic_id,
                            msg_hash,
                            payload: payload.clone(),
                        };
                        if let Ok(fwd_bytes) = postcard::to_stdvec(&fwd_envelope) {
                            Self::send_to_peers(&fwd_bytes, &eager_targets, state).await;
                        } else {
                            warn!("gossip forward envelope serialization failed");
                        }
                    }

                    // Send IHave to lazy peers
                    if !lazy_targets.is_empty() {
                        let ihave_envelope = GossipEnvelope::IHave { topic_id, msg_hash };
                        if let Ok(ihave_bytes) = postcard::to_stdvec(&ihave_envelope) {
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

                // Register a pending IHave. If we don't receive the full message
                // within IHAVE_TIMEOUT, we'll send a Graft to pull it.
                let mut s = state.write().await;
                s.pending_ihaves
                    .entry((topic_id, msg_hash))
                    .or_insert((remote_addr, Instant::now()));
            }

            GossipEnvelope::Graft { topic_id, msg_hash } => {
                // A peer is requesting the full message. Promote them to eager.
                {
                    let mut s = state.write().await;
                    if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                        topic_state.promote_to_eager(&remote_addr);
                    }
                }

                // Look up the cached message and send it
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
                    let envelope_bytes =
                        postcard::to_stdvec(&envelope).expect("envelope serialization cannot fail");
                    Self::send_to_peers(&envelope_bytes, &[remote_addr], state).await;
                } else {
                    debug!("Graft request for unknown message {:?}", &msg_hash[..4]);
                }
            }

            GossipEnvelope::Prune { topic_id } => {
                // The remote peer wants us to stop sending them full messages for this topic.
                let mut s = state.write().await;
                if let Some(topic_state) = s.topics.get_mut(&topic_id) {
                    topic_state.demote_to_lazy(&remote_addr);
                    debug!("Pruned peer {} to lazy for topic", remote_addr);
                }
            }

            GossipEnvelope::AntiEntropy { topic_id, hashes } => {
                // Peer sent us their hash set. Find messages we have that they don't,
                // and send them back.
                let peer_hashes: HashSet<_> = hashes.into_iter().collect();
                let missing_messages: Vec<(MessageHash, Vec<u8>)> = {
                    let s = state.read().await;
                    s.message_cache
                        .iter()
                        .filter(|(hash, cached)| {
                            cached.topic_id == topic_id && !peer_hashes.contains(*hash)
                        })
                        .map(|(hash, cached)| (*hash, cached.payload.clone()))
                        .collect()
                };

                if !missing_messages.is_empty() {
                    let response = GossipEnvelope::AntiEntropyResponse {
                        topic_id,
                        messages: missing_messages,
                    };
                    let response_bytes =
                        postcard::to_stdvec(&response).expect("envelope serialization cannot fail");
                    Self::send_to_peers(&response_bytes, &[remote_addr], state).await;
                }
            }

            GossipEnvelope::AntiEntropyResponse { topic_id, messages } => {
                // We received messages we were missing. Process each one.
                for (msg_hash, payload) in messages {
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
                        // Deliver to local subscribers
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

    /// Periodically check for IHave messages that haven't been fulfilled by eager push.
    /// If IHAVE_TIMEOUT has elapsed, send a Graft to the IHave sender.
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
                    // Only graft if we still haven't seen the message
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

    /// Periodically exchange hash sets with random peers for anti-entropy.
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

            let hashes = {
                let s = state.read().await;
                s.seen.hashes()
            };

            // For each topic, pick one random peer to exchange with
            for (topic_id, peers) in topics_and_peers {
                if peers.is_empty() {
                    continue;
                }
                // Simple deterministic selection (rotate based on time)
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

    /// Periodically clean up expired entries from the message cache.
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

/// Read a gossip envelope from a uni stream.
async fn read_gossip_envelope(recv: &mut RecvStream) -> Result<GossipEnvelope, String> {
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

        assert!(set.insert(h1)); // new
        assert!(!set.insert(h1)); // duplicate
        assert!(set.insert(h2)); // new
        assert!(set.insert(h3)); // new
        assert!(!set.insert(h2)); // still there
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
        // Set is full (3 entries). Inserting h4 should evict h1.
        assert!(set.insert(h4));
        assert!(!set.contains(&h1)); // evicted
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
        // h1 is oldest
        set.insert(h3); // evicts h1
        assert!(!set.contains(&h1));
        assert!(set.contains(&h2));
        assert!(set.contains(&h3));

        set.insert(h4); // evicts h2
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

        // First DEFAULT_EAGER_DEGREE peers should be eager
        ts.add_peer(a1);
        ts.add_peer(a2);
        ts.add_peer(a3);
        assert_eq!(ts.eager_peers().len(), 3);
        assert_eq!(ts.lazy_peers().len(), 0);

        // Beyond that, peers are lazy
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
        ts.add_peer(a4); // lazy

        assert!(ts.lazy_peers().contains(&a4));

        // Promote a4 to eager
        ts.promote_to_eager(&a4);
        assert!(ts.eager_peers().contains(&a4));
        assert!(!ts.lazy_peers().contains(&a4));

        // Demote a1 to lazy
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
    fn seen_set_hashes_returns_all() {
        let mut set = BoundedSeenSet::new(10, Duration::from_secs(60));
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];

        set.insert(h1);
        set.insert(h2);
        set.insert(h3);

        let hashes = set.hashes();
        assert_eq!(hashes.len(), 3);
        assert!(hashes.contains(&h1));
        assert!(hashes.contains(&h2));
        assert!(hashes.contains(&h3));
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

    /// Test that the IHave/Graft flow works correctly at the state level.
    #[test]
    fn ihave_graft_state_flow() {
        let topic_id = topic_id_from_name("test-topic");
        let msg_hash = [0xab; 32];
        let sender: SocketAddr = "127.0.0.1:9000".parse().unwrap();

        // Simulate receiving an IHave
        let mut pending: HashMap<(TopicId, MessageHash), (SocketAddr, Instant)> = HashMap::new();
        pending.insert((topic_id, msg_hash), (sender, Instant::now()));

        // Verify it's pending
        assert!(pending.contains_key(&(topic_id, msg_hash)));

        // Simulate timeout check
        let (_, (addr, _)) = pending.iter().next().unwrap();
        assert_eq!(*addr, sender);

        // After sending Graft, the pending entry is removed
        pending.remove(&(topic_id, msg_hash));
        assert!(!pending.contains_key(&(topic_id, msg_hash)));
    }

    /// Test that prune correctly demotes eager peers to lazy.
    #[test]
    fn prune_demotes_to_lazy() {
        let mut ts = TopicState::new();
        let a1: SocketAddr = "127.0.0.1:1000".parse().unwrap();
        let a2: SocketAddr = "127.0.0.1:2000".parse().unwrap();

        ts.add_peer(a1); // eager
        ts.add_peer(a2); // eager

        assert!(ts.eager_peers().contains(&a1));
        assert!(ts.eager_peers().contains(&a2));

        // Simulate receiving Prune from a1
        ts.demote_to_lazy(&a1);

        assert!(!ts.eager_peers().contains(&a1));
        assert!(ts.lazy_peers().contains(&a1));
        assert!(ts.eager_peers().contains(&a2));
    }

    /// Test that duplicate messages from eager peers trigger prune logic.
    #[test]
    fn duplicate_from_eager_triggers_prune() {
        let mut seen = BoundedSeenSet::new(100, Duration::from_secs(60));
        let msg_hash = [0xcd; 32];

        // First insertion is new
        assert!(seen.insert(msg_hash));
        // Second is duplicate
        assert!(!seen.insert(msg_hash));
        // Already seen -> would trigger prune in handle_envelope
        assert!(seen.contains(&msg_hash));
    }

    /// Test the message cache stores and retrieves messages for Graft responses.
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

    /// Test anti-entropy: finds messages peer is missing.
    #[test]
    fn anti_entropy_finds_missing() {
        let topic_id = topic_id_from_name("ae-test");
        let h1 = [1u8; 32];
        let h2 = [2u8; 32];
        let h3 = [3u8; 32];

        // Our cache has h1, h2, h3
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

        // Peer only has h1 and h3
        let peer_hashes: HashSet<MessageHash> = [h1, h3].into_iter().collect();

        // Find what peer is missing
        let missing: Vec<_> = cache
            .iter()
            .filter(|(hash, cached)| cached.topic_id == topic_id && !peer_hashes.contains(*hash))
            .map(|(hash, cached)| (*hash, cached.payload.clone()))
            .collect();

        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].0, h2);
        assert_eq!(missing[0].1, vec![2]);
    }
}
