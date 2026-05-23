//! Cross-federation bridge nodes.
//!
//! A bridge node participates in TWO (or more) federations' gossip networks
//! simultaneously. It relays relevant messages between them:
//! - Attested roots (so each federation knows the other's state)
//! - Receipts (for EventualRef resolution and BridgeFinalize)
//! - Revocations (so cross-federation token use is protected)
//! - Conditional proof completions (for atomic swaps)
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────┐
//! │ FederationBridge                                           │
//! │                                                            │
//! │  local_state: SharedNodeState (our federation)             │
//! │                                                            │
//! │  remote_federations: fed_id -> RemoteFederation            │
//! │     ├─ fed_A: gossip_handle, latest_root, trusted_keys    │
//! │     └─ fed_B: gossip_handle, latest_root, trusted_keys    │
//! │                                                            │
//! │  relay_config: which message types to relay                │
//! │                                                            │
//! │  run_relay_loop():                                         │
//! │     - receives from remote gossip streams                  │
//! │     - filters & verifies against relay_config              │
//! │     - injects into local_state (roots, receipts, revocs)  │
//! │     - re-publishes local events to remote federations      │
//! └────────────────────────────────────────────────────────────┘
//! ```

use std::collections::{HashMap, HashSet};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use pyana_net::gossip::{GossipEvent, GossipNetwork, MessageStream};
use pyana_net::message::PeerMessage;
use pyana_net::node::{NodeId, PeerNode, PeerNodeConfig};
use tokio::sync::RwLock;
use tracing::{debug, error, info, warn};

use crate::gossip::{GossipHandle, TOPIC_REVOCATIONS, TOPIC_ROOTS, TOPIC_TURNS};
use crate::state::NodeState;

// ─── Configuration ─────────────────────────────────────────────────────────

/// Configuration for which message types to relay between federations.
#[derive(Clone, Debug)]
pub struct RelayConfig {
    /// Relay attested roots between federations.
    pub relay_roots: bool,
    /// Relay revocation announcements between federations.
    pub relay_revocations: bool,
    /// Relay specific receipts (for EventualRef resolution).
    pub relay_receipts: bool,
    /// Relay conditional proof completions (for atomic swaps).
    pub relay_conditionals: bool,
    /// Maximum age (seconds) for accepting remote attested roots.
    pub max_remote_root_age_secs: u64,
    /// Maximum number of remote roots to cache per federation.
    pub max_cached_roots: usize,
}

impl Default for RelayConfig {
    fn default() -> Self {
        Self {
            relay_roots: true,
            relay_revocations: true,
            relay_receipts: true,
            relay_conditionals: true,
            max_remote_root_age_secs: 3600,
            max_cached_roots: 100,
        }
    }
}

// ─── Remote Federation State ───────────────────────────────────────────────

/// A connection to a remote federation's gossip network.
pub struct RemoteFederation {
    /// The remote federation's identity (blake3 hash of their genesis config).
    pub federation_id: [u8; 32],
    /// Peer addresses for connecting to the remote federation.
    pub peer_addresses: Vec<SocketAddr>,
    /// Gossip handle for publishing to the remote federation.
    pub gossip_handle: Option<GossipHandle>,
    /// The latest known attested root from this remote federation.
    pub latest_root: Option<RemoteAttestedRoot>,
    /// Whether this remote federation is trusted (verified keys loaded).
    pub trusted: bool,
    /// Known validator public keys for this remote federation.
    pub trusted_keys: Vec<pyana_types::PublicKey>,
    /// Cache of recent attested roots from this federation (bounded).
    pub root_cache: Vec<RemoteAttestedRoot>,
    /// Time the connection was established.
    pub connected_at: Option<Instant>,
}

/// An attested root from a remote federation, annotated with reception metadata.
#[derive(Clone, Debug)]
pub struct RemoteAttestedRoot {
    /// The raw attested root data.
    pub root: pyana_store::StoredAttestedRoot,
    /// When we received this root.
    pub received_at: Instant,
    /// Whether this root passed QC verification against the remote federation's keys.
    pub verified: bool,
}

// ─── Bridge Node ───────────────────────────────────────────────────────────

/// A bridge node connects to multiple federations and relays messages between them.
///
/// The bridge maintains gossip connections to one or more remote federations and
/// selectively relays messages based on the configured relay policy. This enables:
/// - Cross-federation state awareness (attested root propagation)
/// - Cross-federation token revocation (revocation relay)
/// - EventualRef resolution for cross-federation pending turns
/// - Atomic swap completion across federation boundaries
pub struct FederationBridge {
    /// Our local federation's node state.
    local_state: NodeState,
    /// Remote federation connections (federation_id -> connection info).
    remote_federations: Arc<RwLock<HashMap<[u8; 32], RemoteFederation>>>,
    /// Which message types to relay.
    relay_config: RelayConfig,
    /// Cross-federation revocation cache: federation_id -> set of revoked token hashes.
    /// Tokens revoked in remote federations that we have observed.
    cross_federation_revocations: Arc<RwLock<HashMap<[u8; 32], HashSet<[u8; 32]>>>>,
    /// Pending cross-federation receipt subscriptions: turn_hash -> federation_id.
    /// When a local pending turn awaits a receipt from a remote federation, we track
    /// it here so the relay loop knows which receipts to look for.
    pending_receipt_subscriptions: Arc<RwLock<HashMap<[u8; 32], [u8; 32]>>>,
}

impl FederationBridge {
    /// Create a new bridge with the given local state and relay configuration.
    pub fn new(local_state: NodeState, relay_config: RelayConfig) -> Self {
        Self {
            local_state,
            remote_federations: Arc::new(RwLock::new(HashMap::new())),
            relay_config,
            cross_federation_revocations: Arc::new(RwLock::new(HashMap::new())),
            pending_receipt_subscriptions: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Connect to a remote federation's gossip network.
    ///
    /// This creates a new QUIC endpoint, joins the remote federation's gossip topics,
    /// and returns after the connection is established. Call `run_relay_loop` to start
    /// actually relaying messages.
    ///
    /// # Errors
    ///
    /// Returns an error if `trusted_keys` is empty. Untrusted mode (empty
    /// trusted_keys) is a debug/relay-only configuration that does NOT accept
    /// state-mutating messages (revocations, turn receipts). Since the bridge
    /// cannot safely process mutations without at least one trusted key to verify
    /// against, callers must provide a non-empty set. Use `run_bridge_node` which
    /// already enforces this requirement.
    pub async fn connect_remote(
        &self,
        federation_id: [u8; 32],
        peers: Vec<String>,
        trusted_keys: Vec<pyana_types::PublicKey>,
    ) -> Result<(), String> {
        if trusted_keys.is_empty() {
            return Err(
                "trusted_keys must be non-empty: untrusted mode cannot safely accept \
                 state-mutating messages (revocations, turn receipts)"
                    .to_string(),
            );
        }

        let fed_id_hex: String = federation_id
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();

        // Parse peer addresses.
        let peer_addrs: Vec<SocketAddr> = peers
            .iter()
            .filter_map(|p| match p.parse::<SocketAddr>() {
                Ok(addr) => Some(addr),
                Err(e) => {
                    warn!(peer = %p, error = %e, fed = %fed_id_hex, "invalid remote peer address");
                    None
                }
            })
            .collect();

        if peer_addrs.is_empty() {
            return Err("no valid peer addresses for remote federation".to_string());
        }

        info!(
            federation = %fed_id_hex,
            peer_count = peer_addrs.len(),
            "connecting to remote federation"
        );

        // Create a dedicated PeerNode for this remote federation connection.
        let peer_node = PeerNode::new(PeerNodeConfig {
            bind_addr: "0.0.0.0:0".parse().unwrap(),
            ..PeerNodeConfig::default()
        })
        .await
        .map_err(|e| format!("failed to create PeerNode for remote federation: {e}"))?;

        let node_id: NodeId = peer_node.node_id();
        let endpoint = peer_node.endpoint().clone();

        // Get our signing key for gossip authentication.
        let (signing_key, our_public_key) = {
            let s = self.local_state.read().await;
            let sk = s.wallet.gossip_signing_key();
            let pk = s.wallet.public_key();
            (sk, pk)
        };

        // Build peer key registry from the remote federation's known keys.
        let mut peer_keys: std::collections::HashMap<NodeId, pyana_types::PublicKey> =
            std::collections::HashMap::new();
        for fed_key in &trusted_keys {
            let peer_node_id = *blake3::hash(fed_key.as_bytes()).as_bytes();
            peer_keys.insert(peer_node_id, *fed_key);
        }
        // Register our own key.
        peer_keys.insert(node_id, our_public_key);

        // Create the gossip network for this remote federation.
        let gossip = Arc::new(GossipNetwork::new(
            endpoint,
            node_id,
            signing_key,
            peer_keys,
        ));

        // Join the remote federation's core topics.
        let topic_turns = gossip
            .join_topic(TOPIC_TURNS, &peer_addrs)
            .await
            .map_err(|e| format!("failed to join remote turns topic: {e}"))?;
        let topic_revocations = gossip
            .join_topic(TOPIC_REVOCATIONS, &peer_addrs)
            .await
            .map_err(|e| format!("failed to join remote revocations topic: {e}"))?;
        let topic_roots = gossip
            .join_topic(TOPIC_ROOTS, &peer_addrs)
            .await
            .map_err(|e| format!("failed to join remote roots topic: {e}"))?;

        // Subscribe to each topic.
        let turns_stream = gossip
            .subscribe(&topic_turns)
            .await
            .map_err(|e| format!("failed to subscribe to remote turns: {e}"))?;
        let revocations_stream = gossip
            .subscribe(&topic_revocations)
            .await
            .map_err(|e| format!("failed to subscribe to remote revocations: {e}"))?;
        let roots_stream = gossip
            .subscribe(&topic_roots)
            .await
            .map_err(|e| format!("failed to subscribe to remote roots: {e}"))?;

        // Build a gossip handle for publishing to the remote federation.
        // We reuse the same topic handles for the core topics; checkpoints/budget/etc
        // are not relayed across federations.
        let gossip_handle = GossipHandle {
            network: gossip.clone(),
            topic_turns: topic_turns.clone(),
            topic_revocations: topic_revocations.clone(),
            topic_intents: topic_roots.clone(), // placeholder (intents not relayed)
            topic_roots: topic_roots.clone(),
            topic_checkpoints: topic_roots.clone(), // placeholder
            topic_decryption_shares: topic_roots.clone(), // placeholder
            topic_budget: topic_roots.clone(),      // placeholder
        };

        // Store the remote federation state.
        {
            let mut remotes = self.remote_federations.write().await;
            remotes.insert(
                federation_id,
                RemoteFederation {
                    federation_id,
                    peer_addresses: peer_addrs.clone(),
                    gossip_handle: Some(gossip_handle),
                    latest_root: None,
                    trusted: !trusted_keys.is_empty(),
                    trusted_keys,
                    root_cache: Vec::new(),
                    connected_at: Some(Instant::now()),
                },
            );
        }

        // Spawn relay tasks for this remote federation.
        self.spawn_remote_relay_tasks(
            federation_id,
            turns_stream,
            revocations_stream,
            roots_stream,
        );

        info!(
            federation = %fed_id_hex,
            "connected to remote federation, relay tasks spawned"
        );

        Ok(())
    }

    /// Spawn background tasks that relay messages from a remote federation to local state.
    fn spawn_remote_relay_tasks(
        &self,
        federation_id: [u8; 32],
        mut turns_stream: MessageStream,
        mut revocations_stream: MessageStream,
        mut roots_stream: MessageStream,
    ) {
        let fed_id_hex: String = federation_id
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();

        // Task 1: Relay remote attested roots to local state.
        if self.relay_config.relay_roots {
            let local_state = self.local_state.clone();
            let remotes = self.remote_federations.clone();
            let max_age = self.relay_config.max_remote_root_age_secs;
            let max_cached = self.relay_config.max_cached_roots;
            let fed_hex = fed_id_hex.clone();

            tokio::spawn(async move {
                loop {
                    match roots_stream.recv().await {
                        Some(GossipEvent::Message { from, message }) => {
                            handle_remote_root(
                                &local_state,
                                &remotes,
                                federation_id,
                                from,
                                message,
                                max_age,
                                max_cached,
                            )
                            .await;
                        }
                        Some(GossipEvent::PeerJoined(addr)) => {
                            info!(peer = %addr, fed = %fed_hex, "remote peer joined roots topic");
                        }
                        Some(GossipEvent::PeerLeft(addr)) => {
                            info!(peer = %addr, fed = %fed_hex, "remote peer left roots topic");
                        }
                        None => {
                            warn!(fed = %fed_hex, "remote roots stream closed");
                            break;
                        }
                    }
                }
            });
        }

        // Task 2: Relay remote revocations to local cross-federation revocation cache.
        if self.relay_config.relay_revocations {
            let revocations = self.cross_federation_revocations.clone();
            let remotes = self.remote_federations.clone();
            let fed_hex = fed_id_hex.clone();

            tokio::spawn(async move {
                loop {
                    match revocations_stream.recv().await {
                        Some(GossipEvent::Message { from, message }) => {
                            handle_remote_revocation(
                                &revocations,
                                &remotes,
                                federation_id,
                                from,
                                message,
                            )
                            .await;
                        }
                        Some(GossipEvent::PeerJoined(addr)) => {
                            info!(peer = %addr, fed = %fed_hex, "remote peer joined revocations topic");
                        }
                        Some(GossipEvent::PeerLeft(addr)) => {
                            info!(peer = %addr, fed = %fed_hex, "remote peer left revocations topic");
                        }
                        None => {
                            warn!(fed = %fed_hex, "remote revocations stream closed");
                            break;
                        }
                    }
                }
            });
        }

        // Task 3: Relay remote turn receipts for cross-federation EventualRef resolution.
        if self.relay_config.relay_receipts {
            let local_state = self.local_state.clone();
            let pending_subs = self.pending_receipt_subscriptions.clone();
            let remotes = self.remote_federations.clone();
            let fed_hex = fed_id_hex.clone();

            tokio::spawn(async move {
                loop {
                    match turns_stream.recv().await {
                        Some(GossipEvent::Message { from, message }) => {
                            handle_remote_receipt(
                                &local_state,
                                &pending_subs,
                                &remotes,
                                federation_id,
                                from,
                                message,
                            )
                            .await;
                        }
                        Some(GossipEvent::PeerJoined(addr)) => {
                            debug!(peer = %addr, fed = %fed_hex, "remote peer joined turns topic");
                        }
                        Some(GossipEvent::PeerLeft(addr)) => {
                            debug!(peer = %addr, fed = %fed_hex, "remote peer left turns topic");
                        }
                        None => {
                            warn!(fed = %fed_hex, "remote turns stream closed");
                            break;
                        }
                    }
                }
            });
        }
    }

    /// Subscribe to receipt notifications from a remote federation.
    ///
    /// When a local pending turn has `ResolutionCondition::AwaitReceipt { federation_id: Some(remote_fed) }`,
    /// call this to tell the bridge to watch for that receipt on the remote federation.
    pub async fn subscribe_receipt(&self, turn_hash: [u8; 32], federation_id: [u8; 32]) {
        let mut subs = self.pending_receipt_subscriptions.write().await;
        subs.insert(turn_hash, federation_id);
        let fed_hex: String = federation_id
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();
        let hash_hex: String = turn_hash
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect();
        debug!(
            turn_hash = %hash_hex,
            federation = %fed_hex,
            "subscribed to remote receipt"
        );
    }

    /// Check if a token hash is revoked in a remote federation.
    pub async fn is_revoked_in_remote(
        &self,
        federation_id: &[u8; 32],
        token_hash: &[u8; 32],
    ) -> bool {
        let revocations = self.cross_federation_revocations.read().await;
        revocations
            .get(federation_id)
            .map(|set| set.contains(token_hash))
            .unwrap_or(false)
    }

    /// Get the latest known root for a remote federation.
    pub async fn latest_remote_root(&self, federation_id: &[u8; 32]) -> Option<RemoteAttestedRoot> {
        let remotes = self.remote_federations.read().await;
        remotes
            .get(federation_id)
            .and_then(|rf| rf.latest_root.clone())
    }

    /// Get all connected remote federation IDs.
    pub async fn connected_federations(&self) -> Vec<[u8; 32]> {
        let remotes = self.remote_federations.read().await;
        remotes.keys().copied().collect()
    }

    /// Get the cross-federation revocation set for a specific federation.
    pub async fn revocations_for(&self, federation_id: &[u8; 32]) -> HashSet<[u8; 32]> {
        let revocations = self.cross_federation_revocations.read().await;
        revocations.get(federation_id).cloned().unwrap_or_default()
    }

    /// Run the main bridge relay loop.
    ///
    /// This monitors the local federation for events that should be relayed to
    /// remote federations (outbound relay). Inbound relay is handled by the
    /// per-federation tasks spawned in `connect_remote`.
    ///
    /// Specifically, this:
    /// - Watches for local attested root updates and relays them to remote federations
    /// - Watches for local revocations and relays them to remote federations
    /// - Periodically checks for stale remote connections and logs warnings
    pub async fn run_relay_loop(&self) {
        info!("bridge relay loop started");

        let mut events_rx = self.local_state.subscribe_events();
        let mut stale_check_interval = tokio::time::interval(Duration::from_secs(60));

        loop {
            tokio::select! {
                // Relay local events to remote federations.
                event = events_rx.recv() => {
                    match event {
                        Ok(crate::state::NodeEvent::Root { height, merkle_root, timestamp }) => {
                            if self.relay_config.relay_roots {
                                self.relay_local_root_to_remotes(height, &merkle_root, timestamp).await;
                            }
                        }
                        Ok(crate::state::NodeEvent::Revocation { token_id }) => {
                            if self.relay_config.relay_revocations {
                                self.relay_local_revocation_to_remotes(&token_id).await;
                            }
                        }
                        Ok(crate::state::NodeEvent::Receipt { hash }) => {
                            if self.relay_config.relay_receipts {
                                debug!(receipt = %hash, "local receipt emitted (available for relay if requested)");
                            }
                        }
                        Ok(_) => {}
                        Err(tokio::sync::broadcast::error::RecvError::Lagged(n)) => {
                            warn!(missed = n, "bridge event subscriber lagged");
                        }
                        Err(tokio::sync::broadcast::error::RecvError::Closed) => {
                            info!("local event channel closed, bridge shutting down");
                            break;
                        }
                    }
                }
                // Periodic stale connection check.
                _ = stale_check_interval.tick() => {
                    self.check_stale_connections().await;
                }
            }
        }
    }

    /// Relay a local attested root to all connected remote federations.
    async fn relay_local_root_to_remotes(&self, height: u64, _merkle_root: &str, _timestamp: i64) {
        // Serialize the latest local root for relay.
        let root_data = {
            let s = self.local_state.read().await;
            match s.store.latest_attested_root() {
                Ok(Some(root)) => match postcard::to_stdvec(&root) {
                    Ok(data) => Some(data),
                    Err(e) => {
                        warn!(error = %e, "failed to serialize local root for relay");
                        None
                    }
                },
                _ => None,
            }
        };

        let Some(data) = root_data else { return };

        let remotes = self.remote_federations.read().await;
        for (fed_id, remote) in remotes.iter() {
            if let Some(handle) = &remote.gossip_handle {
                handle.gossip_root(data.clone()).await;
                let fed_hex: String = fed_id.iter().take(4).map(|b| format!("{b:02x}")).collect();
                debug!(federation = %fed_hex, height = height, "relayed local root to remote federation");
            }
        }
    }

    /// Relay a local revocation to all connected remote federations.
    async fn relay_local_revocation_to_remotes(&self, token_id: &str) {
        // Get the revocation signature from local store.
        let signature = {
            let s = self.local_state.read().await;
            let sk = s.wallet.gossip_signing_key();
            let sig = pyana_types::sign(&sk, token_id.as_bytes());
            sig.0.to_vec()
        };

        let remotes = self.remote_federations.read().await;
        for (fed_id, remote) in remotes.iter() {
            if let Some(handle) = &remote.gossip_handle {
                handle
                    .gossip_revocation(token_id.to_string(), signature.clone())
                    .await;
                let fed_hex: String = fed_id.iter().take(4).map(|b| format!("{b:02x}")).collect();
                debug!(federation = %fed_hex, token_id = %token_id, "relayed revocation to remote federation");
            }
        }
    }

    /// Check for stale remote federation connections and log warnings.
    async fn check_stale_connections(&self) {
        let remotes = self.remote_federations.read().await;
        let now = Instant::now();

        for (fed_id, remote) in remotes.iter() {
            let fed_hex: String = fed_id.iter().take(4).map(|b| format!("{b:02x}")).collect();

            // Check if we have a recent root. If the latest root is older than
            // 2x the max_remote_root_age, the connection may be stale.
            if let Some(latest) = &remote.latest_root {
                let age = now.duration_since(latest.received_at);
                if age > Duration::from_secs(self.relay_config.max_remote_root_age_secs * 2) {
                    warn!(
                        federation = %fed_hex,
                        age_secs = age.as_secs(),
                        "remote federation connection may be stale (no recent roots)"
                    );
                }
            } else if let Some(connected_at) = remote.connected_at {
                // Never received a root — if connected for > 5 minutes, something is wrong.
                let age = now.duration_since(connected_at);
                if age > Duration::from_secs(300) {
                    warn!(
                        federation = %fed_hex,
                        connected_secs = age.as_secs(),
                        "remote federation never sent a root after connection"
                    );
                }
            }
        }
    }
}

// ─── Remote Message Handlers ───────────────────────────────────────────────

/// Handle an attested root received from a remote federation.
///
/// Verifies the root's QC against the remote federation's known validator keys,
/// stores it in the remote federation's root cache, and notifies pending turns
/// that may be waiting on this federation's state.
async fn handle_remote_root(
    local_state: &NodeState,
    remotes: &Arc<RwLock<HashMap<[u8; 32], RemoteFederation>>>,
    federation_id: [u8; 32],
    from: SocketAddr,
    message: PeerMessage,
    max_age_secs: u64,
    max_cached: usize,
) {
    let PeerMessage::AttestedRootUpdate { root } = message else {
        return;
    };

    let fed_hex: String = federation_id
        .iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect();

    // Deserialize the remote root.
    let attested_root: pyana_store::StoredAttestedRoot = match postcard::from_bytes(&root) {
        Ok(r) => r,
        Err(e) => {
            warn!(from = %from, fed = %fed_hex, error = %e, "failed to decode remote attested root");
            return;
        }
    };

    let height = attested_root.height;

    // Verify the root's timestamp freshness.
    let now_secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let root_age = (now_secs - attested_root.timestamp).unsigned_abs();
    if root_age > max_age_secs {
        warn!(
            from = %from,
            fed = %fed_hex,
            height = height,
            age_secs = root_age,
            max_age = max_age_secs,
            "rejecting remote root: too old"
        );
        return;
    }

    // Verify QC against known remote federation keys.
    let verified = {
        let remotes_guard = remotes.read().await;
        if let Some(remote) = remotes_guard.get(&federation_id) {
            if remote.trusted && !remote.trusted_keys.is_empty() {
                let typed_root = pyana_types::AttestedRoot {
                    merkle_root: attested_root.merkle_root,
                    note_tree_root: attested_root.note_tree_root,
                    nullifier_set_root: attested_root.nullifier_set_root,
                    height: attested_root.height,
                    timestamp: attested_root.timestamp,
                    quorum_signatures: attested_root.quorum_signatures.clone(),
                    threshold_qc: attested_root.threshold_qc.clone(),
                    threshold: attested_root.threshold,
                };
                typed_root.is_valid(&remote.trusted_keys)
            } else {
                // Untrusted mode: accept but mark as unverified.
                false
            }
        } else {
            warn!(fed = %fed_hex, "received root from unknown remote federation");
            return;
        }
    };

    let remote_root = RemoteAttestedRoot {
        root: attested_root.clone(),
        received_at: Instant::now(),
        verified,
    };

    // Update the remote federation's state.
    {
        let mut remotes_guard = remotes.write().await;
        if let Some(remote) = remotes_guard.get_mut(&federation_id) {
            remote.latest_root = Some(remote_root.clone());

            // Add to cache, evicting oldest if needed.
            if remote.root_cache.len() >= max_cached {
                remote.root_cache.remove(0);
            }
            remote.root_cache.push(remote_root);
        }
    }

    // Store the remote root in local state's trusted federation roots
    // so that BridgeMint and other cross-federation operations can verify against it.
    if verified {
        let s = local_state.read().await;
        // Store as a cross-federation root. The executor's trusted_federation_roots
        // will pick this up when verifying BridgeMint proofs.
        if let Err(e) = s.store.store_attested_root(&attested_root) {
            warn!(error = %e, fed = %fed_hex, "failed to store remote attested root locally");
        }
    }

    info!(
        from = %from,
        fed = %fed_hex,
        height = height,
        verified = verified,
        "received and cached remote federation root"
    );
}

/// Handle a revocation received from a remote federation.
///
/// Verifies the revocation signature against the remote federation's keys and
/// adds it to the cross-federation revocation cache.
async fn handle_remote_revocation(
    revocations: &Arc<RwLock<HashMap<[u8; 32], HashSet<[u8; 32]>>>>,
    remotes: &Arc<RwLock<HashMap<[u8; 32], RemoteFederation>>>,
    federation_id: [u8; 32],
    from: SocketAddr,
    message: PeerMessage,
) {
    let PeerMessage::RevocationGossip {
        token_id,
        signature,
    } = message
    else {
        return;
    };

    let fed_hex: String = federation_id
        .iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect();

    // Verify the revocation signature against the remote federation's keys.
    if signature.len() != 64 {
        warn!(from = %from, fed = %fed_hex, "invalid remote revocation signature length");
        return;
    }

    let sig_bytes: [u8; 64] = signature[..64].try_into().unwrap();
    let sig = pyana_types::Signature(sig_bytes);

    let verified = {
        let remotes_guard = remotes.read().await;
        if let Some(remote) = remotes_guard.get(&federation_id) {
            if remote.trusted_keys.is_empty() {
                // Untrusted mode (no trusted keys): refuse state-mutating messages.
                // Revocations require verified signer identity to prevent spoofed
                // revocations from poisoning the cross-federation cache.
                warn!(
                    from = %from,
                    fed = %fed_hex,
                    "rejecting revocation in untrusted mode (no trusted keys configured)"
                );
                false
            } else {
                remote
                    .trusted_keys
                    .iter()
                    .any(|pk| pk.verify(token_id.as_bytes(), &sig))
            }
        } else {
            false
        }
    };

    if !verified {
        warn!(
            from = %from,
            fed = %fed_hex,
            token_id = %token_id,
            "rejecting remote revocation: signature verification failed"
        );
        return;
    }

    // Add to cross-federation revocation cache.
    let token_hash = *blake3::hash(token_id.as_bytes()).as_bytes();
    {
        let mut revocs = revocations.write().await;
        revocs.entry(federation_id).or_default().insert(token_hash);
    }

    info!(
        from = %from,
        fed = %fed_hex,
        token_id = %token_id,
        "remote revocation cached"
    );
}

/// Handle a turn receipt from a remote federation.
///
/// Checks if any local pending turns are awaiting this receipt for EventualRef
/// resolution. If so, resolves the pending turn.
async fn handle_remote_receipt(
    local_state: &NodeState,
    pending_subs: &Arc<RwLock<HashMap<[u8; 32], [u8; 32]>>>,
    remotes: &Arc<RwLock<HashMap<[u8; 32], RemoteFederation>>>,
    federation_id: [u8; 32],
    from: SocketAddr,
    message: PeerMessage,
) {
    let PeerMessage::PublishTurn {
        turn_hash,
        turn_data,
        ..
    } = message
    else {
        return;
    };

    let fed_hex: String = federation_id
        .iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect();
    let hash_hex: String = turn_hash
        .iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect();

    // Check if any local pending turns are waiting for this specific receipt.
    let is_subscribed = {
        let subs = pending_subs.read().await;
        subs.get(&turn_hash)
            .map(|fid| *fid == federation_id)
            .unwrap_or(false)
    };

    if !is_subscribed {
        // Not a receipt we're waiting for — ignore (normal for most messages).
        return;
    }

    debug!(
        from = %from,
        fed = %fed_hex,
        turn_hash = %hash_hex,
        "received subscribed remote receipt"
    );

    // Deserialize the remote turn to extract a receipt.
    let signed_turn: pyana_sdk::SignedTurn = match postcard::from_bytes(&turn_data) {
        Ok(st) => st,
        Err(e) => {
            warn!(
                from = %from,
                fed = %fed_hex,
                error = %e,
                "failed to deserialize remote turn for receipt extraction"
            );
            return;
        }
    };

    // Verify the remote turn's signature.
    let computed_hash = signed_turn.turn.hash();
    if computed_hash != turn_hash {
        warn!(from = %from, fed = %fed_hex, "remote turn hash mismatch");
        return;
    }

    // Verify signature against remote federation keys.
    let sig_valid = {
        let remotes_guard = remotes.read().await;
        if let Some(remote) = remotes_guard.get(&federation_id) {
            if remote.trusted_keys.is_empty() {
                // Untrusted mode (no trusted keys): refuse state-mutating messages.
                // Turn receipts that resolve pending local turns are state-mutating;
                // without a trusted key set we cannot verify the signer's identity.
                warn!(
                    from = %from,
                    fed = %fed_hex,
                    turn_hash = %hash_hex,
                    "rejecting remote receipt in untrusted mode (no trusted keys configured)"
                );
                false
            } else {
                // Verify the signer is a known key in the remote federation.
                let signer_known = remote.trusted_keys.contains(&signed_turn.signer);
                signer_known
                    && signed_turn
                        .signer
                        .verify(&computed_hash, &signed_turn.signature)
            }
        } else {
            false
        }
    };

    if !sig_valid {
        warn!(
            from = %from,
            fed = %fed_hex,
            turn_hash = %hash_hex,
            "rejecting remote receipt: signature verification failed"
        );
        return;
    }

    // Create a synthetic receipt for the remote turn.
    // In a full implementation, the remote federation would gossip actual receipts;
    // here we construct one from the verified turn data.
    let receipt = pyana_turn::TurnReceipt {
        turn_hash: computed_hash,
        forest_hash: signed_turn.turn.call_forest.compute_hash(),
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: signed_turn.turn.call_forest.roots.len(),
        previous_receipt_hash: None,
        agent: signed_turn.turn.agent,
        federation_id,
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
    };

    // Resolve the pending turn in the local registry.
    {
        let mut s = local_state.write().await;
        let events = s.pending_turns.resolve(
            turn_hash,
            pyana_turn::ResolutionOutcome::Resolved(receipt.clone()),
        );

        if !events.is_empty() {
            info!(
                fed = %fed_hex,
                turn_hash = %hash_hex,
                resolved_count = events.len(),
                "remote receipt resolved local pending turns"
            );

            // Execute any turns that became ready due to cascading resolution.
            for event in &events {
                if let pyana_turn::ResolutionEvent::ReadyToExecute {
                    turn_hash: ready_hash,
                    turn: ready_turn,
                } = event
                {
                    let mut executor =
                        pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
                    let local_fed_id = *blake3::hash(s.wallet.public_key().as_bytes()).as_bytes();
                    executor.set_local_federation_id(local_fed_id);
                    let now = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_secs() as i64)
                        .unwrap_or(0);
                    executor.set_timestamp(now);
                    let current_height = s
                        .store
                        .latest_attested_root()
                        .ok()
                        .flatten()
                        .map(|r| r.height)
                        .unwrap_or(0);
                    executor.set_block_height(current_height);

                    let exec_result = executor.execute(ready_turn, &mut s.ledger);
                    match exec_result {
                        pyana_turn::TurnResult::Committed {
                            receipt: ready_receipt,
                            ..
                        } => {
                            s.pending_turns.resolve(
                                *ready_hash,
                                pyana_turn::ResolutionOutcome::Resolved(ready_receipt.clone()),
                            );
                            s.wallet.append_receipt(ready_receipt);
                        }
                        pyana_turn::TurnResult::Rejected { reason, .. } => {
                            s.pending_turns.resolve(
                                *ready_hash,
                                pyana_turn::ResolutionOutcome::Broken(
                                    pyana_turn::BrokenReason::TurnRejected(reason),
                                ),
                            );
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // Remove the subscription now that it's fulfilled.
    {
        let mut subs = pending_subs.write().await;
        subs.remove(&turn_hash);
    }

    info!(
        fed = %fed_hex,
        turn_hash = %hash_hex,
        "remote receipt successfully processed and pending turn resolved"
    );
}

// ─── Bridge Startup ────────────────────────────────────────────────────────

/// Parse a remote peer specification in the format "federation_id_hex:host:port".
///
/// Returns (federation_id, socket_address) if valid.
pub fn parse_remote_peer(spec: &str) -> Result<([u8; 32], String), String> {
    // Format: <64-char-hex-fed-id>:<host>:<port>
    // Minimum length: 64 + 1 + 1 + 1 + 1 = 68 (x:y:1)
    if spec.len() < 68 {
        return Err(format!("remote peer spec too short: {spec}"));
    }

    let fed_hex = &spec[..64];
    let addr_part = &spec[65..]; // skip the ':' separator

    // Parse federation ID from hex.
    let mut federation_id = [0u8; 32];
    for (i, chunk) in fed_hex.as_bytes().chunks(2).enumerate() {
        let hex_str = std::str::from_utf8(chunk).map_err(|_| "invalid hex in federation ID")?;
        federation_id[i] =
            u8::from_str_radix(hex_str, 16).map_err(|_| "invalid hex digit in federation ID")?;
    }

    Ok((federation_id, addr_part.to_string()))
}

/// Run the bridge node: connect to remote federations and start relay loops.
///
/// This is the main entry point called from the CLI's Bridge subcommand.
pub async fn run_bridge(
    local_state: NodeState,
    remote_peers: Vec<String>,
    relay_config: RelayConfig,
    remote_federation_keys: HashMap<[u8; 32], Vec<pyana_types::PublicKey>>,
) {
    let bridge = FederationBridge::new(local_state.clone(), relay_config);

    // Group remote peers by federation ID.
    let mut peers_by_federation: HashMap<[u8; 32], Vec<String>> = HashMap::new();
    for spec in &remote_peers {
        match parse_remote_peer(spec) {
            Ok((fed_id, addr)) => {
                peers_by_federation.entry(fed_id).or_default().push(addr);
            }
            Err(e) => {
                error!(spec = %spec, error = %e, "invalid remote peer specification, skipping");
            }
        }
    }

    if peers_by_federation.is_empty() {
        error!("no valid remote peers configured, bridge cannot start");
        return;
    }

    // Connect to each remote federation.
    for (fed_id, addrs) in &peers_by_federation {
        let fed_hex: String = fed_id.iter().take(4).map(|b| format!("{b:02x}")).collect();
        info!(
            federation = %fed_hex,
            peer_count = addrs.len(),
            "connecting bridge to remote federation"
        );

        // Load trusted keys from the provided remote keys map, falling back
        // to the node's known federation keys.
        let trusted_keys = if let Some(keys) = remote_federation_keys.get(fed_id) {
            keys.clone()
        } else {
            // Fall back to node's known federation keys.
            let s = local_state.read().await;
            s.known_federation_keys.clone()
        };

        if trusted_keys.is_empty() {
            error!(
                federation = %fed_hex,
                "cannot start bridge without trusted remote keys. \
                 Use --remote-keys or configure known_federation_keys."
            );
            std::process::exit(1);
        }

        if let Err(e) = bridge
            .connect_remote(*fed_id, addrs.clone(), trusted_keys)
            .await
        {
            error!(
                federation = %fed_hex,
                error = %e,
                "failed to connect to remote federation"
            );
        }
    }

    // Scan local pending turns for cross-federation receipt dependencies
    // and subscribe to them on the bridge.
    {
        let s = local_state.read().await;
        // The PendingTurnRegistry doesn't expose iteration, so we check the
        // state at startup. New subscriptions will be added as pending turns
        // are submitted via the API.
        drop(s);
    }

    // Run the outbound relay loop (blocks forever).
    bridge.run_relay_loop().await;
}
