//! Transport abstraction for federation consensus networking.
//!
//! This module defines the [`FederationTransport`] trait that abstracts how
//! consensus messages are sent between federation nodes. Two implementations
//! are provided:
//!
//! - [`LocalTransport`]: In-memory channels for testing and single-process simulations.
//! - [`TcpFederationTransport`]: Real TCP networking using the wire protocol's
//!   length-prefixed postcard framing.

use std::collections::HashMap;
use std::future::Future;
use std::net::SocketAddr;
use std::pin::Pin;
use std::sync::Arc;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::sync::{Mutex, mpsc};

use crate::node::{ConsensusConfig, ConsensusState};
use crate::types::*;

// =============================================================================
// Transport Error
// =============================================================================

/// Errors that can occur during transport operations.
#[derive(Debug)]
pub enum TransportError {
    /// The target node is unreachable.
    Unreachable(usize),
    /// A serialization/deserialization error.
    Codec(String),
    /// An I/O error on the underlying transport.
    Io(std::io::Error),
    /// The connection was closed by the peer.
    ConnectionClosed,
    /// The operation timed out.
    Timeout,
    /// The channel is full (backpressure).
    ChannelFull,
    /// Peer authentication failed during handshake.
    AuthenticationFailed(String),
}

impl std::fmt::Display for TransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unreachable(id) => write!(f, "node {id} unreachable"),
            Self::Codec(msg) => write!(f, "codec error: {msg}"),
            Self::Io(e) => write!(f, "I/O error: {e}"),
            Self::ConnectionClosed => write!(f, "connection closed"),
            Self::Timeout => write!(f, "operation timed out"),
            Self::ChannelFull => write!(f, "channel full (backpressure)"),
            Self::AuthenticationFailed(msg) => write!(f, "authentication failed: {msg}"),
        }
    }
}

impl std::error::Error for TransportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for TransportError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

// =============================================================================
// FederationTransport Trait
// =============================================================================

/// Trait abstracting how consensus messages are delivered between nodes.
///
/// Implementations handle the actual network I/O (or in-memory routing for tests).
/// All methods return boxed futures for dyn-compatibility.
pub trait FederationTransport: Send + Sync {
    /// Send a vote to the leader (proposer) for the current view.
    fn send_vote(
        &self,
        to: usize,
        vote: &Vote,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>>;

    /// Broadcast a proposal to all federation members.
    fn broadcast_proposal(
        &self,
        proposal: &RevocationBlock,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>>;

    /// Broadcast a finalized block with its quorum certificate to all members.
    fn broadcast_finalized(
        &self,
        block: &RevocationBlock,
        qc: &QuorumCertificate,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>>;

    /// Broadcast a view-change message to all federation members.
    fn broadcast_view_change(
        &self,
        vc: &ViewChangeMessage,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>>;

    /// Receive the next consensus message for this node.
    /// Returns None if no message is available within a reasonable timeout.
    fn recv(
        &self,
    ) -> Pin<Box<dyn Future<Output = Result<Option<ConsensusMessage>, TransportError>> + Send + '_>>;
}

// =============================================================================
// LocalTransport (in-memory channels for testing)
// =============================================================================

/// In-memory transport using tokio mpsc channels.
///
/// Messages are delivered synchronously within a single process. Useful for
/// unit tests and single-machine simulations.
pub struct LocalTransport {
    /// This node's ID.
    node_id: usize,
    /// Senders to each node's inbox (indexed by node_id).
    senders: Vec<mpsc::Sender<ConsensusMessage>>,
    /// This node's inbox receiver.
    receiver: Mutex<mpsc::Receiver<ConsensusMessage>>,
}

impl LocalTransport {
    /// Create a set of local transports for n nodes.
    ///
    /// Returns a Vec of transports, one per node, all interconnected.
    pub fn create_network(num_nodes: usize) -> Vec<Arc<Self>> {
        let mut senders = Vec::with_capacity(num_nodes);
        let mut receivers = Vec::with_capacity(num_nodes);

        for _ in 0..num_nodes {
            let (tx, rx) = mpsc::channel(256);
            senders.push(tx);
            receivers.push(rx);
        }

        let shared_senders: Vec<mpsc::Sender<ConsensusMessage>> = senders;

        receivers
            .into_iter()
            .enumerate()
            .map(|(id, rx)| {
                Arc::new(Self {
                    node_id: id,
                    senders: shared_senders.clone(),
                    receiver: Mutex::new(rx),
                })
            })
            .collect()
    }
}

impl FederationTransport for LocalTransport {
    fn send_vote(
        &self,
        to: usize,
        vote: &Vote,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let vote = vote.clone();
        Box::pin(async move {
            self.senders
                .get(to)
                .ok_or(TransportError::Unreachable(to))?
                .try_send(ConsensusMessage::VoteMsg(vote))
                .map_err(|_| TransportError::ChannelFull)
        })
    }

    fn broadcast_proposal(
        &self,
        proposal: &RevocationBlock,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let msg = ConsensusMessage::Propose(proposal.clone());
        Box::pin(async move {
            for (i, sender) in self.senders.iter().enumerate() {
                if i == self.node_id {
                    continue;
                }
                if sender.try_send(msg.clone()).is_err() {
                    tracing::warn!(peer_id = i, "failed to send proposal to peer");
                }
            }
            Ok(())
        })
    }

    fn broadcast_finalized(
        &self,
        block: &RevocationBlock,
        qc: &QuorumCertificate,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let msg = ConsensusMessage::Finalize(qc.clone(), block.clone());
        Box::pin(async move {
            for (i, sender) in self.senders.iter().enumerate() {
                if i == self.node_id {
                    continue;
                }
                if sender.try_send(msg.clone()).is_err() {
                    tracing::warn!(peer_id = i, "failed to send finalized block to peer");
                }
            }
            Ok(())
        })
    }

    fn broadcast_view_change(
        &self,
        vc: &ViewChangeMessage,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let msg = ConsensusMessage::ViewChange(vc.clone());
        Box::pin(async move {
            for (i, sender) in self.senders.iter().enumerate() {
                if i == self.node_id {
                    continue;
                }
                if sender.try_send(msg.clone()).is_err() {
                    tracing::warn!(peer_id = i, "failed to send view-change to peer");
                }
            }
            Ok(())
        })
    }

    fn recv(
        &self,
    ) -> Pin<Box<dyn Future<Output = Result<Option<ConsensusMessage>, TransportError>> + Send + '_>>
    {
        Box::pin(async move {
            let mut rx = self.receiver.lock().await;
            match rx.try_recv() {
                Ok(msg) => Ok(Some(msg)),
                Err(mpsc::error::TryRecvError::Empty) => Ok(None),
                Err(mpsc::error::TryRecvError::Disconnected) => {
                    Err(TransportError::ConnectionClosed)
                }
            }
        })
    }
}

// =============================================================================
// TcpFederationTransport
// =============================================================================

/// Wire-level federation message envelope for TCP transport.
///
/// This wraps a ConsensusMessage with sender metadata for the length-prefixed
/// postcard framing used on the wire.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct FederationEnvelope {
    /// The sender's node ID.
    pub from: usize,
    /// The consensus message payload.
    pub message: ConsensusMessage,
}

/// TCP-based federation transport.
///
/// Maintains persistent connections to all federation peers. Messages are
/// serialized with postcard and framed with a 4-byte LE length prefix,
/// matching the wire crate's framing convention.
///
/// Includes peer authentication: on each incoming connection, the transport
/// sends a 32-byte random challenge. The connecting peer must respond with
/// its node_id and an Ed25519 signature over (challenge || node_id). The
/// signature is verified against the known member public keys.
pub struct TcpFederationTransport {
    /// This node's ID.
    node_id: usize,
    /// Map of node_id -> socket address for all federation peers.
    peers: HashMap<usize, SocketAddr>,
    /// Outgoing connections to peers (lazily established, reconnecting).
    connections: Mutex<HashMap<usize, TcpStream>>,
    /// Inbox for messages received from peers.
    inbox: Mutex<mpsc::Receiver<ConsensusMessage>>,
    /// Sender half of the inbox (held to keep the channel alive for listeners).
    #[allow(dead_code)]
    inbox_tx: mpsc::Sender<ConsensusMessage>,
    /// Known member public keys for peer authentication (indexed by node_id).
    /// When non-empty, incoming connections must complete a challenge-response
    /// handshake proving they hold the private key for a known member.
    member_keys: Arc<Vec<PublicKey>>,
    /// This node's signing key for authenticating outgoing connections.
    signing_key: SigningKey,
}

impl TcpFederationTransport {
    /// Create a new TCP transport for a federation node.
    ///
    /// - `node_id`: This node's index in the federation.
    /// - `peers`: Map of peer node_id -> socket address.
    /// - `listen_addr`: The address to listen on for incoming connections.
    pub async fn new(
        node_id: usize,
        peers: HashMap<usize, SocketAddr>,
        listen_addr: SocketAddr,
    ) -> Result<Arc<Self>, TransportError> {
        let (sk, _pk) = generate_keypair();
        Self::new_with_auth(node_id, peers, listen_addr, Vec::new(), sk).await
    }

    /// Create a new TCP transport with peer authentication.
    ///
    /// - `node_id`: This node's index in the federation.
    /// - `peers`: Map of peer node_id -> socket address.
    /// - `listen_addr`: The address to listen on for incoming connections.
    /// - `member_keys`: Public keys of federation members (indexed by node_id).
    /// - `signing_key`: This node's signing key for authenticating to peers.
    pub async fn new_with_auth(
        node_id: usize,
        peers: HashMap<usize, SocketAddr>,
        listen_addr: SocketAddr,
        member_keys: Vec<PublicKey>,
        signing_key: SigningKey,
    ) -> Result<Arc<Self>, TransportError> {
        let (inbox_tx, inbox_rx) = mpsc::channel(1024);
        let member_keys = Arc::new(member_keys);

        let transport = Arc::new(Self {
            node_id,
            peers,
            connections: Mutex::new(HashMap::new()),
            inbox: Mutex::new(inbox_rx),
            inbox_tx: inbox_tx.clone(),
            member_keys: member_keys.clone(),
            signing_key,
        });

        // Start the listener task.
        let listener_tx = inbox_tx;
        let listener = tokio::net::TcpListener::bind(listen_addr).await?;
        let keys_for_listener = member_keys;
        tokio::spawn(async move {
            loop {
                match listener.accept().await {
                    Ok((stream, _addr)) => {
                        let tx = listener_tx.clone();
                        let keys = keys_for_listener.clone();
                        tokio::spawn(Self::handle_incoming(stream, tx, keys));
                    }
                    Err(_) => break,
                }
            }
        });

        Ok(transport)
    }

    /// Create and return the actual bound address (useful for port 0).
    pub async fn new_with_addr(
        node_id: usize,
        peers: HashMap<usize, SocketAddr>,
        listen_addr: SocketAddr,
    ) -> Result<(Arc<Self>, SocketAddr), TransportError> {
        let (sk, _pk) = generate_keypair();
        Self::new_with_addr_auth(node_id, peers, listen_addr, Vec::new(), sk).await
    }

    /// Create and return the actual bound address with peer authentication.
    pub async fn new_with_addr_auth(
        node_id: usize,
        peers: HashMap<usize, SocketAddr>,
        listen_addr: SocketAddr,
        member_keys: Vec<PublicKey>,
        signing_key: SigningKey,
    ) -> Result<(Arc<Self>, SocketAddr), TransportError> {
        let (inbox_tx, inbox_rx) = mpsc::channel(1024);
        let member_keys = Arc::new(member_keys);

        let listener = tokio::net::TcpListener::bind(listen_addr).await?;
        let actual_addr = listener.local_addr()?;

        let transport = Arc::new(Self {
            node_id,
            peers,
            connections: Mutex::new(HashMap::new()),
            inbox: Mutex::new(inbox_rx),
            inbox_tx: inbox_tx.clone(),
            member_keys: member_keys.clone(),
            signing_key,
        });

        // Start the listener task.
        let listener_tx = inbox_tx;
        let keys_for_listener = member_keys;
        tokio::spawn(async move {
            loop {
                match listener.accept().await {
                    Ok((stream, _addr)) => {
                        let tx = listener_tx.clone();
                        let keys = keys_for_listener.clone();
                        tokio::spawn(Self::handle_incoming(stream, tx, keys));
                    }
                    Err(_) => break,
                }
            }
        });

        Ok((transport, actual_addr))
    }

    /// Handle an incoming TCP connection with challenge-response authentication.
    ///
    /// Protocol:
    /// 1. Server sends 32 random bytes as a challenge.
    /// 2. Peer responds with: [node_id as u32 LE][64-byte Ed25519 signature over (challenge || node_id_bytes)].
    /// 3. Server verifies the signature against the member's public key.
    /// 4. If valid, the connection is accepted and message processing begins.
    async fn handle_incoming(
        mut stream: TcpStream,
        tx: mpsc::Sender<ConsensusMessage>,
        member_keys: Arc<Vec<PublicKey>>,
    ) {
        // If member keys are configured, perform challenge-response authentication.
        if !member_keys.is_empty() {
            // Step 1: Send a 32-byte random challenge.
            let mut challenge = [0u8; 32];
            getrandom::fill(&mut challenge).expect("getrandom failed");
            if stream.write_all(&challenge).await.is_err() {
                return;
            }
            if stream.flush().await.is_err() {
                return;
            }

            // Step 2: Read the peer's response: [4-byte node_id LE][64-byte signature].
            let mut response = [0u8; 68]; // 4 + 64
            if stream.read_exact(&mut response).await.is_err() {
                return;
            }

            let peer_node_id =
                u32::from_le_bytes([response[0], response[1], response[2], response[3]]) as usize;
            let mut sig_bytes = [0u8; 64];
            sig_bytes.copy_from_slice(&response[4..68]);
            let sig = Signature(sig_bytes);

            // Step 3: Verify signature against known member key.
            let peer_key = match member_keys.get(peer_node_id) {
                Some(k) => k,
                None => {
                    tracing::warn!(peer_node_id, "rejecting connection: unknown node_id");
                    return;
                }
            };

            // The signed message is: challenge || node_id_bytes
            let mut signed_msg = Vec::with_capacity(36);
            signed_msg.extend_from_slice(&challenge);
            signed_msg.extend_from_slice(&(peer_node_id as u32).to_le_bytes());

            if !peer_key.verify(&signed_msg, &sig) {
                tracing::warn!(
                    peer_node_id,
                    "rejecting connection: invalid handshake signature"
                );
                return;
            }

            tracing::debug!(peer_node_id, "peer authenticated successfully");
        }

        // Authenticated (or no auth configured) — process messages.
        loop {
            match Self::read_envelope(&mut stream).await {
                Ok(envelope) => {
                    if tx.send(envelope.message).await.is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    }

    /// Perform the client side of the challenge-response handshake.
    ///
    /// Called when establishing an outgoing connection to a peer that requires auth.
    async fn authenticate_outgoing(
        stream: &mut TcpStream,
        node_id: usize,
        signing_key: &SigningKey,
    ) -> Result<(), TransportError> {
        // Step 1: Read the 32-byte challenge from the server.
        let mut challenge = [0u8; 32];
        stream.read_exact(&mut challenge).await?;

        // Step 2: Sign (challenge || our_node_id) and send [node_id LE][signature].
        let mut signed_msg = Vec::with_capacity(36);
        signed_msg.extend_from_slice(&challenge);
        signed_msg.extend_from_slice(&(node_id as u32).to_le_bytes());

        let sig = sign(signing_key, &signed_msg);

        let mut response = [0u8; 68];
        response[0..4].copy_from_slice(&(node_id as u32).to_le_bytes());
        response[4..68].copy_from_slice(&sig.0);
        stream.write_all(&response).await?;
        stream.flush().await?;

        Ok(())
    }

    /// Get or establish a TCP connection to a peer.
    ///
    /// If member keys are configured, the outgoing connection performs the
    /// client side of the challenge-response handshake before being stored.
    async fn get_connection(&self, peer_id: usize) -> Result<(), TransportError> {
        let mut conns = self.connections.lock().await;
        if conns.contains_key(&peer_id) {
            return Ok(());
        }
        let addr = self
            .peers
            .get(&peer_id)
            .ok_or(TransportError::Unreachable(peer_id))?;
        let mut stream = TcpStream::connect(addr).await?;
        stream.set_nodelay(true).ok();

        // Authenticate if member keys are configured.
        if !self.member_keys.is_empty() {
            Self::authenticate_outgoing(&mut stream, self.node_id, &self.signing_key).await?;
        }

        conns.insert(peer_id, stream);
        Ok(())
    }

    /// Send an envelope to a specific peer, reconnecting on failure.
    async fn send_to(
        &self,
        peer_id: usize,
        envelope: &FederationEnvelope,
    ) -> Result<(), TransportError> {
        // Try to connect if not already connected.
        if let Err(_) = self.get_connection(peer_id).await {
            // Retry once after a short delay.
            tokio::time::sleep(std::time::Duration::from_millis(50)).await;
            self.get_connection(peer_id).await?;
        }

        let mut conns = self.connections.lock().await;
        let stream = conns
            .get_mut(&peer_id)
            .ok_or(TransportError::Unreachable(peer_id))?;

        match Self::write_envelope(stream, envelope).await {
            Ok(()) => Ok(()),
            Err(_) => {
                // Connection broken — remove it and try once more.
                conns.remove(&peer_id);
                drop(conns);

                self.get_connection(peer_id).await?;
                let mut conns = self.connections.lock().await;
                let stream = conns
                    .get_mut(&peer_id)
                    .ok_or(TransportError::Unreachable(peer_id))?;
                Self::write_envelope(stream, envelope).await
            }
        }
    }

    /// Write a framed envelope to a TCP stream.
    /// Frame format: [4-byte LE length][postcard payload]
    async fn write_envelope(
        stream: &mut TcpStream,
        envelope: &FederationEnvelope,
    ) -> Result<(), TransportError> {
        let payload =
            postcard::to_stdvec(envelope).map_err(|e| TransportError::Codec(e.to_string()))?;
        let len = payload.len() as u32;
        stream.write_all(&len.to_le_bytes()).await?;
        stream.write_all(&payload).await?;
        stream.flush().await?;
        Ok(())
    }

    /// Read a framed envelope from a TCP stream.
    async fn read_envelope(stream: &mut TcpStream) -> Result<FederationEnvelope, TransportError> {
        let mut header = [0u8; 4];
        stream.read_exact(&mut header).await?;
        let len = u32::from_le_bytes(header) as usize;

        if len > 16 * 1024 * 1024 {
            return Err(TransportError::Codec("message too large".to_string()));
        }

        let mut payload = vec![0u8; len];
        stream.read_exact(&mut payload).await?;

        postcard::from_bytes(&payload).map_err(|e| TransportError::Codec(e.to_string()))
    }
}

impl FederationTransport for TcpFederationTransport {
    fn send_vote(
        &self,
        to: usize,
        vote: &Vote,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let vote = vote.clone();
        Box::pin(async move {
            let envelope = FederationEnvelope {
                from: self.node_id,
                message: ConsensusMessage::VoteMsg(vote),
            };
            self.send_to(to, &envelope).await
        })
    }

    fn broadcast_proposal(
        &self,
        proposal: &RevocationBlock,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let envelope = FederationEnvelope {
            from: self.node_id,
            message: ConsensusMessage::Propose(proposal.clone()),
        };
        Box::pin(async move {
            for &peer_id in self.peers.keys() {
                if peer_id == self.node_id {
                    continue;
                }
                let mut sent = false;
                for delay in [
                    std::time::Duration::from_millis(0),
                    std::time::Duration::from_millis(100),
                    std::time::Duration::from_millis(500),
                ] {
                    if delay.as_millis() > 0 {
                        tokio::time::sleep(delay).await;
                    }
                    if self.send_to(peer_id, &envelope).await.is_ok() {
                        sent = true;
                        break;
                    }
                }
                if !sent {
                    tracing::warn!(peer_id, "failed to send proposal to peer after retries");
                }
            }
            Ok(())
        })
    }

    fn broadcast_finalized(
        &self,
        block: &RevocationBlock,
        qc: &QuorumCertificate,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let envelope = FederationEnvelope {
            from: self.node_id,
            message: ConsensusMessage::Finalize(qc.clone(), block.clone()),
        };
        Box::pin(async move {
            for &peer_id in self.peers.keys() {
                if peer_id == self.node_id {
                    continue;
                }
                let mut sent = false;
                for delay in [
                    std::time::Duration::from_millis(0),
                    std::time::Duration::from_millis(100),
                    std::time::Duration::from_millis(500),
                ] {
                    if delay.as_millis() > 0 {
                        tokio::time::sleep(delay).await;
                    }
                    if self.send_to(peer_id, &envelope).await.is_ok() {
                        sent = true;
                        break;
                    }
                }
                if !sent {
                    tracing::warn!(
                        peer_id,
                        "failed to send finalized block to peer after retries"
                    );
                }
            }
            Ok(())
        })
    }

    fn broadcast_view_change(
        &self,
        vc: &ViewChangeMessage,
    ) -> Pin<Box<dyn Future<Output = Result<(), TransportError>> + Send + '_>> {
        let envelope = FederationEnvelope {
            from: self.node_id,
            message: ConsensusMessage::ViewChange(vc.clone()),
        };
        Box::pin(async move {
            for &peer_id in self.peers.keys() {
                if peer_id == self.node_id {
                    continue;
                }
                if self.send_to(peer_id, &envelope).await.is_err() {
                    tracing::warn!(peer_id, "failed to send view-change to peer");
                }
            }
            Ok(())
        })
    }

    fn recv(
        &self,
    ) -> Pin<Box<dyn Future<Output = Result<Option<ConsensusMessage>, TransportError>> + Send + '_>>
    {
        Box::pin(async move {
            let mut rx = self.inbox.lock().await;
            match rx.try_recv() {
                Ok(msg) => Ok(Some(msg)),
                Err(mpsc::error::TryRecvError::Empty) => Ok(None),
                Err(mpsc::error::TryRecvError::Disconnected) => {
                    Err(TransportError::ConnectionClosed)
                }
            }
        })
    }
}

// =============================================================================
// NetworkConsensusNode: drives consensus over a transport
// =============================================================================

/// Timeout for proposals: if no proposal is seen within this duration,
/// the node initiates a view change.
pub const PROPOSAL_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(30);

/// An async consensus node that drives the Morpheus-shaped protocol over a
/// [`FederationTransport`].
///
/// Each `NetworkConsensusNode` runs the propose/vote/finalize loop for one
/// federation member using real (or simulated) network I/O.
///
/// Includes a pacemaker that detects leader failures: if no proposal is seen
/// within [`PROPOSAL_TIMEOUT`], this node broadcasts a signed view-change
/// message. Once n-f view-change messages for the same view are collected,
/// the view advances and the next leader takes over.
pub struct NetworkConsensusNode {
    /// The consensus state for this node.
    pub state: ConsensusState,
    /// The transport used to communicate with peers.
    pub transport: Arc<dyn FederationTransport>,
    /// The consensus configuration.
    pub config: ConsensusConfig,
    /// Timestamp of the last proposal seen (for timeout/pacemaker).
    pub last_proposal_seen: std::time::Instant,
    /// Whether we have already broadcast a view-change for the current view.
    pub view_change_sent: bool,
    /// Collected view-change messages for the next view, keyed by voter node ID.
    pub view_change_votes: std::collections::HashMap<usize, ViewChangeMessage>,
}

impl NetworkConsensusNode {
    /// Create a new network consensus node.
    pub fn new(
        state: ConsensusState,
        transport: Arc<dyn FederationTransport>,
        config: ConsensusConfig,
    ) -> Self {
        Self {
            state,
            transport,
            config,
            last_proposal_seen: std::time::Instant::now(),
            view_change_sent: false,
            view_change_votes: std::collections::HashMap::new(),
        }
    }

    /// If this node is the leader, create and broadcast a proposal.
    /// Returns the proposal if one was created.
    pub async fn try_propose(&mut self) -> Result<Option<RevocationBlock>, TransportError> {
        if !self.state.is_leader() || self.state.pending_events.is_empty() {
            return Ok(None);
        }

        let proposal = match self.state.create_proposal() {
            Some(p) => p,
            None => return Ok(None),
        };

        // Broadcast the proposal to all peers.
        self.transport.broadcast_proposal(&proposal).await?;

        // Vote for our own proposal.
        if let Some(vote) = self.state.vote_on_proposal(&proposal) {
            self.state.collect_vote(vote);
        }

        // Reset pacemaker since we just proposed.
        self.last_proposal_seen = std::time::Instant::now();

        Ok(Some(proposal))
    }

    /// Check if the proposal timeout has expired and initiate a view change.
    ///
    /// If no proposal has been seen within [`PROPOSAL_TIMEOUT`], this node
    /// broadcasts a signed view-change message requesting the next view.
    /// Returns `true` if a view-change message was sent.
    pub async fn check_timeout(&mut self) -> Result<bool, TransportError> {
        if self.view_change_sent {
            return Ok(false);
        }

        let elapsed = std::time::Instant::now().duration_since(self.last_proposal_seen);
        if elapsed < PROPOSAL_TIMEOUT {
            return Ok(false);
        }

        // Timeout expired -- broadcast a view-change.
        let new_view = self.state.current_view + 1;
        let height = self.state.current_height;
        let msg_bytes = ViewChangeMessage::signing_message(new_view, height);
        let signature = sign(&self.state.signing_key, &msg_bytes);

        let vc_msg = ViewChangeMessage {
            new_view,
            height,
            voter: self.state.node_id,
            signature,
        };

        // Record our own view-change vote.
        self.view_change_votes
            .insert(self.state.node_id, vc_msg.clone());

        // Broadcast the view-change to all peers via the transport.
        self.transport.broadcast_view_change(&vc_msg).await?;

        self.view_change_sent = true;

        // Check if we already have enough view-change votes to advance.
        self.try_advance_view();

        Ok(true)
    }

    /// Try to advance the view if we have collected n-f view-change votes
    /// for the same new_view.
    fn try_advance_view(&mut self) {
        let new_view = self.state.current_view + 1;
        let vc_count = self
            .view_change_votes
            .values()
            .filter(|vc| vc.new_view == new_view)
            .count();

        // Need n - f (threshold) view-change messages to advance.
        if vc_count >= self.config.threshold {
            self.state.advance_view();
            self.last_proposal_seen = std::time::Instant::now();
            self.view_change_sent = false;
            self.view_change_votes.clear();
            tracing::info!(
                new_view = new_view,
                "view change completed -- advanced to new view"
            );
        }
    }

    /// Process incoming messages. Returns a QC if finalization is reached.
    pub async fn process_messages(
        &mut self,
    ) -> Result<Option<(RevocationBlock, QuorumCertificate)>, TransportError> {
        // Drain all available messages.
        loop {
            let msg = self.transport.recv().await?;
            match msg {
                None => break,
                Some(ConsensusMessage::Propose(block)) => {
                    // Reset pacemaker -- we received a proposal.
                    self.last_proposal_seen = std::time::Instant::now();
                    self.view_change_sent = false;
                    self.view_change_votes.clear();

                    // Validate and vote.
                    if let Some(vote) = self.state.vote_on_proposal(&block) {
                        let leader_id = self.config.leader_for_view(block.view);
                        self.transport.send_vote(leader_id, &vote).await?;
                    }
                }
                Some(ConsensusMessage::VoteMsg(vote)) => {
                    // Collect vote (only meaningful if we're the leader).
                    if let Some(qc) = self.state.collect_vote(vote) {
                        // We've reached quorum! Finalize.
                        let block = self.state.current_proposal.clone().unwrap();
                        self.transport.broadcast_finalized(&block, &qc).await?;
                        self.state.finalize_block(block.clone(), qc.clone());
                        return Ok(Some((block, qc)));
                    }
                }
                Some(ConsensusMessage::Finalize(qc, block)) => {
                    // Validate the QC signatures before accepting finalization.
                    if !self.config.members.is_empty() {
                        if qc.votes.len() < self.config.threshold {
                            tracing::warn!("Rejected Finalize: insufficient votes in QC");
                            continue;
                        }
                        let vote_message =
                            QuorumCertificate::vote_message(&qc.block_hash, qc.height, qc.view);
                        let mut sigs_valid = true;
                        for (voter_id, sig) in &qc.votes {
                            match self.config.members.get(*voter_id) {
                                Some(pk) => {
                                    if !pk.verify(&vote_message, sig) {
                                        sigs_valid = false;
                                        break;
                                    }
                                }
                                None => {
                                    sigs_valid = false;
                                    break;
                                }
                            }
                        }
                        if !sigs_valid {
                            tracing::warn!("Rejected Finalize: invalid QC signatures");
                            continue;
                        }
                    } else if self.config.require_authentication {
                        tracing::warn!(
                            "INSECURE: accepting Finalize without QC signature verification \
                             (legacy mode — no members configured)"
                        );
                    }

                    // Verify QC block_hash matches the block.
                    if qc.block_hash != block.block_hash {
                        tracing::warn!("Rejected Finalize: QC/block hash mismatch");
                        continue;
                    }

                    // Verify height alignment with current state.
                    if block.height != self.state.current_height {
                        tracing::warn!(
                            expected = self.state.current_height,
                            got = block.height,
                            "Rejected Finalize: wrong height"
                        );
                        continue;
                    }

                    // Reset pacemaker -- finalization received and validated.
                    self.last_proposal_seen = std::time::Instant::now();
                    self.view_change_sent = false;
                    self.view_change_votes.clear();

                    self.state.finalize_block(block.clone(), qc.clone());
                    return Ok(Some((block, qc)));
                }
                Some(ConsensusMessage::RevokeRequest(event)) => {
                    self.state.submit_revocation(event);
                }
                Some(ConsensusMessage::ViewChange(vc_msg)) => {
                    // Verify the view-change signature if members are configured.
                    let valid = if !self.config.members.is_empty() {
                        if let Some(voter_pk) = self.config.members.get(vc_msg.voter) {
                            let msg_bytes =
                                ViewChangeMessage::signing_message(vc_msg.new_view, vc_msg.height);
                            voter_pk.verify(&msg_bytes, &vc_msg.signature)
                        } else {
                            false
                        }
                    } else {
                        // Legacy mode: accept view-change without signature check.
                        true
                    };

                    if valid
                        && vc_msg.new_view == self.state.current_view + 1
                        && vc_msg.height == self.state.current_height
                    {
                        self.view_change_votes.insert(vc_msg.voter, vc_msg);
                        self.try_advance_view();
                    }
                }
                Some(_) => {
                    // Ignore other message types.
                }
            }
        }
        Ok(None)
    }

    /// Submit a revocation event to be included in the next block.
    pub fn submit_revocation(&mut self, event: RevocationEvent) {
        self.state.submit_revocation(event);
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::ConsensusConfig;
    use crate::types::generate_keypair;

    #[tokio::test]
    async fn local_transport_basic_send_recv() {
        let transports = LocalTransport::create_network(3);

        // Node 0 sends a vote to node 1.
        let vote = Vote {
            block_hash: [0xAA; 32],
            height: 1,
            view: 1,
            voter: 0,
            signature: Signature([0xBB; 64]),
        };
        transports[0].send_vote(1, &vote).await.unwrap();

        // Node 1 should receive it.
        let msg = transports[1].recv().await.unwrap();
        assert!(msg.is_some());
        match msg.unwrap() {
            ConsensusMessage::VoteMsg(v) => {
                assert_eq!(v.voter, 0);
                assert_eq!(v.block_hash, [0xAA; 32]);
            }
            other => panic!("expected VoteMsg, got {other:?}"),
        }

        // Node 2 should have nothing.
        let msg = transports[2].recv().await.unwrap();
        assert!(msg.is_none());
    }

    #[tokio::test]
    async fn local_transport_broadcast() {
        let transports = LocalTransport::create_network(4);

        let block = RevocationBlock {
            height: 1,
            view: 1,
            proposer: 0,
            events: vec![],
            prev_hash: [0; 32],
            block_hash: [0xFF; 32],
            proposer_signature: None,
            pre_state_root: [0; 32],
            post_state_root: [0; 32],
            note_tree_root: [0; 32],
            nullifier_set_root: [0; 32],
            transition_proof: None,
        };

        transports[0].broadcast_proposal(&block).await.unwrap();

        // All nodes except 0 should receive.
        let msg0 = transports[0].recv().await.unwrap();
        assert!(msg0.is_none());

        for i in 1..4 {
            let msg = transports[i].recv().await.unwrap();
            assert!(msg.is_some(), "node {i} should have received proposal");
        }
    }

    #[tokio::test]
    async fn network_consensus_node_full_round() {
        let config = ConsensusConfig::new(4);
        let transports = LocalTransport::create_network(4);

        let mut nodes: Vec<NetworkConsensusNode> = (0..4)
            .map(|i| {
                let (sk, _pk) = generate_keypair();
                let state = ConsensusState::new(i, sk, config.clone());
                NetworkConsensusNode::new(state, transports[i].clone(), config.clone())
            })
            .collect();

        // Submit a revocation event to node 0.
        let event = RevocationEvent {
            token_id: "tok-net-1".to_string(),
            authority_id: 0,
            signature: Signature([0x42; 64]),
        };
        nodes[0].submit_revocation(event.clone());

        // Determine leader for view 1.
        let leader_id = config.leader_for_view(1);

        // Move pending events to the leader if needed.
        if leader_id != 0 {
            nodes[leader_id].submit_revocation(event);
            nodes[0].state.pending_events.clear();
        }

        // Leader proposes.
        let proposal = nodes[leader_id].try_propose().await.unwrap();
        assert!(proposal.is_some());

        // Other nodes process the proposal and vote.
        for i in 0..4 {
            if i == leader_id {
                continue;
            }
            nodes[i].process_messages().await.unwrap();
        }

        // Leader collects votes and finalizes.
        let result = nodes[leader_id].process_messages().await.unwrap();
        assert!(result.is_some(), "leader should have reached quorum");

        let (_block, qc) = result.unwrap();
        assert!(qc.is_valid());

        // Other nodes receive the finalization.
        for i in 0..4 {
            if i == leader_id {
                continue;
            }
            let fin = nodes[i].process_messages().await.unwrap();
            assert!(fin.is_some(), "node {i} should have received finalization");
        }
    }
}
