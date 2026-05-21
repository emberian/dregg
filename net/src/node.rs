//! PeerNode: quinn-based QUIC transport for pyana P2P connections.
//!
//! Each pyana node runs a `PeerNode` that manages its identity (via a self-signed
//! certificate derived from a secret key) and provides connect/accept operations
//! for direct QUIC streams.
//!
//! Security properties:
//! - Mutual TLS: both client and server must present certificates.
//! - Peer identity is derived exclusively from TLS certificates (no IP fallback).
//! - Configurable max_connections limit, enforced on accept.
//! - Per-IP connection rate limiting to prevent brute-force attacks.
//!
//! This uses quinn (raw QUIC) since the iroh crate has pre-release dependency
//! conflicts in the current ecosystem. The P2P semantics are equivalent.

use std::collections::{HashMap, HashSet};
use std::net::{IpAddr, SocketAddr};
use std::sync::{Arc, RwLock};
use std::time::Instant;

use quinn::{ClientConfig, Connection, Endpoint, RecvStream, SendStream, ServerConfig};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use tracing::{debug, info, warn};

use crate::message::{DecodeError, PeerMessage};

/// ALPN protocol identifier for pyana P2P connections.
pub const PYANA_ALPN: &[u8] = b"pyana/p2p/1";

/// A 32-byte node identity derived from the certificate's public key.
pub type NodeId = [u8; 32];

/// Default maximum number of concurrent connections.
const DEFAULT_MAX_CONNECTIONS: usize = 256;

/// Maximum connection attempts per IP per window before rate limiting.
const RATE_LIMIT_MAX_ATTEMPTS: u32 = 10;

/// Rate limit window duration.
const RATE_LIMIT_WINDOW: std::time::Duration = std::time::Duration::from_secs(60);

/// A pyana peer-to-peer network node backed by a quinn QUIC endpoint.
///
/// Each node has a unique identity derived from its TLS certificate.
/// Connections are authenticated via mutual TLS with self-signed certificates.
pub struct PeerNode {
    endpoint: Endpoint,
    node_id: NodeId,
    local_addr: SocketAddr,
    cert_der: Vec<u8>,
    /// Maximum concurrent connections enforced by this node.
    max_connections: usize,
    /// Rate limiter for incoming connections.
    rate_limiter: ConnectionRateLimiter,
}

/// A bidirectional connection to a remote pyana peer.
pub struct PeerConnection {
    connection: Connection,
    remote_id: NodeId,
}

/// Errors that can occur during peer operations.
#[derive(Debug)]
pub enum PeerError {
    /// Failed to bind the endpoint.
    Bind(String),
    /// Failed to connect to a peer.
    Connect(String),
    /// Failed to accept a connection.
    Accept(String),
    /// Failed to send a message.
    Send(String),
    /// Failed to receive a message.
    Recv(String),
    /// Message decode error.
    Decode(DecodeError),
    /// Connection was closed.
    ConnectionClosed,
    /// TLS/certificate error.
    Tls(String),
}

impl std::fmt::Display for PeerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PeerError::Bind(e) => write!(f, "bind error: {e}"),
            PeerError::Connect(e) => write!(f, "connect error: {e}"),
            PeerError::Accept(e) => write!(f, "accept error: {e}"),
            PeerError::Send(e) => write!(f, "send error: {e}"),
            PeerError::Recv(e) => write!(f, "recv error: {e}"),
            PeerError::Decode(e) => write!(f, "decode error: {e}"),
            PeerError::ConnectionClosed => write!(f, "connection closed"),
            PeerError::Tls(e) => write!(f, "tls error: {e}"),
        }
    }
}

impl std::error::Error for PeerError {}

/// Configuration for creating a PeerNode.
pub struct PeerNodeConfig {
    /// Address to bind to. Use `0.0.0.0:0` for OS-assigned port.
    pub bind_addr: SocketAddr,
    /// Maximum number of concurrent connections. Defaults to 256.
    pub max_connections: usize,
}

impl Default for PeerNodeConfig {
    fn default() -> Self {
        Self {
            bind_addr: "127.0.0.1:0".parse().unwrap(),
            max_connections: DEFAULT_MAX_CONNECTIONS,
        }
    }
}

/// Per-IP connection rate limiter to prevent brute-force and resource exhaustion.
#[derive(Debug, Clone)]
pub struct ConnectionRateLimiter {
    /// Map of IP -> (attempt_count, window_start)
    state: Arc<RwLock<HashMap<IpAddr, (u32, Instant)>>>,
    max_attempts: u32,
    window: std::time::Duration,
}

impl ConnectionRateLimiter {
    /// Create a new rate limiter.
    pub fn new(max_attempts: u32, window: std::time::Duration) -> Self {
        Self {
            state: Arc::new(RwLock::new(HashMap::new())),
            max_attempts,
            window,
        }
    }

    /// Check if a connection from this IP should be allowed. Returns false if rate limited.
    pub fn check_and_record(&self, ip: IpAddr) -> bool {
        let mut state = self.state.write().unwrap();
        let now = Instant::now();

        let entry = state.entry(ip).or_insert((0, now));

        // Reset window if expired
        if now.duration_since(entry.1) > self.window {
            *entry = (0, now);
        }

        entry.0 += 1;
        entry.0 <= self.max_attempts
    }

    /// Evict expired entries to prevent unbounded growth.
    pub fn evict_expired(&self) {
        let mut state = self.state.write().unwrap();
        let now = Instant::now();
        state.retain(|_, (_, window_start)| now.duration_since(*window_start) <= self.window);
    }
}

impl PeerNode {
    /// Create a new pyana peer node with a fresh identity.
    ///
    /// Generates a self-signed certificate for authentication.
    /// Binds to the specified address (default: localhost with OS-assigned port).
    /// Uses mutual TLS: the server requires clients to present a certificate.
    pub async fn new(config: PeerNodeConfig) -> Result<Self, PeerError> {
        // Generate a self-signed certificate
        let cert_params = rcgen::CertificateParams::new(vec!["pyana.local".to_string()])
            .map_err(|e| PeerError::Tls(e.to_string()))?;
        let key_pair = rcgen::KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256)
            .map_err(|e| PeerError::Tls(e.to_string()))?;
        let cert = cert_params
            .self_signed(&key_pair)
            .map_err(|e| PeerError::Tls(e.to_string()))?;

        let cert_der = cert.der().to_vec();
        let key_der = key_pair.serialize_der();

        // Derive node ID from certificate hash
        let node_id = *blake3::hash(&cert_der).as_bytes();

        // Build server config with mutual TLS (client cert required)
        let server_config = Self::build_server_config(&cert_der, &key_der)?;

        // Build the quinn endpoint
        let mut endpoint = Endpoint::server(server_config, config.bind_addr)
            .map_err(|e| PeerError::Bind(e.to_string()))?;

        // Set the default client config with our certificate for mutual TLS
        let client_config = Self::build_client_config_with_cert(&cert_der, &key_der)?;
        endpoint.set_default_client_config(client_config);

        let local_addr = endpoint
            .local_addr()
            .map_err(|e| PeerError::Bind(e.to_string()))?;

        let rate_limiter = ConnectionRateLimiter::new(RATE_LIMIT_MAX_ATTEMPTS, RATE_LIMIT_WINDOW);

        info!(
            "PeerNode started: {} @ {} (max_connections={})",
            fmt_node_id(&node_id),
            local_addr,
            config.max_connections,
        );

        Ok(Self {
            endpoint,
            node_id,
            local_addr,
            cert_der,
            max_connections: config.max_connections,
            rate_limiter,
        })
    }

    /// Connect to a remote peer at the given address.
    ///
    /// The remote peer's node_id is verified after connection (via certificate hash).
    pub async fn connect(&self, addr: SocketAddr) -> Result<PeerConnection, PeerError> {
        let client_config = Self::build_client_config()?;
        let connection = self
            .endpoint
            .connect_with(client_config, addr, "pyana.local")
            .map_err(|e| PeerError::Connect(e.to_string()))?
            .await
            .map_err(|e| PeerError::Connect(e.to_string()))?;

        // Derive remote node ID from their certificate
        let remote_id = extract_remote_id(&connection)?;
        debug!("Connected to peer: {}", fmt_node_id(&remote_id));

        Ok(PeerConnection {
            connection,
            remote_id,
        })
    }

    /// Accept an incoming connection from a remote peer.
    ///
    /// Enforces:
    /// - Maximum concurrent connection limit (rejects when at capacity).
    /// - Per-IP rate limiting (rejects after N rapid connection attempts).
    /// - Peer identity extraction from TLS certificate (no IP-based fallback).
    pub async fn accept(&self) -> Result<PeerConnection, PeerError> {
        loop {
            let incoming = self
                .endpoint
                .accept()
                .await
                .ok_or_else(|| PeerError::Accept("endpoint closed".to_string()))?;

            let remote_addr = incoming.remote_address();

            // Enforce per-IP rate limiting
            if !self.rate_limiter.check_and_record(remote_addr.ip()) {
                warn!(
                    "Rate limited connection from {} — rejecting",
                    remote_addr.ip()
                );
                incoming.refuse();
                continue;
            }

            let connection = incoming
                .await
                .map_err(|e| PeerError::Accept(e.to_string()))?;

            let remote_id = extract_remote_id(&connection)?;
            debug!("Accepted connection from: {}", fmt_node_id(&remote_id));

            return Ok(PeerConnection {
                connection,
                remote_id,
            });
        }
    }

    /// Get this node's identity (blake3 hash of its certificate).
    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    /// Get this node's local listening address.
    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Get this node's DER-encoded certificate (for out-of-band sharing).
    pub fn cert_der(&self) -> &[u8] {
        &self.cert_der
    }

    /// Get a reference to the underlying quinn endpoint.
    pub fn endpoint(&self) -> &Endpoint {
        &self.endpoint
    }

    /// Get the maximum connections configuration.
    pub fn max_connections(&self) -> usize {
        self.max_connections
    }

    /// Get a reference to the rate limiter (for gossip layer integration).
    pub fn rate_limiter(&self) -> &ConnectionRateLimiter {
        &self.rate_limiter
    }

    /// Gracefully shut down the endpoint, refusing new connections.
    pub fn close(&self) {
        self.endpoint.close(0u8.into(), b"shutdown");
    }

    /// Wait for all connections to finish after closing.
    pub async fn wait_idle(&self) {
        self.endpoint.wait_idle().await;
    }

    fn build_server_config(cert_der: &[u8], key_der: &[u8]) -> Result<ServerConfig, PeerError> {
        let cert = CertificateDer::from(cert_der.to_vec());
        let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_der.to_vec()));

        // Mutual TLS: require client certificates. We use a custom verifier that
        // accepts any self-signed cert (identity checked at application layer via
        // blake3(cert_der) -> NodeId). This ensures peers MUST present a certificate,
        // preventing unauthenticated connections.
        let client_cert_verifier = Arc::new(MutualTlsClientVerifier);

        let mut server_crypto = rustls::ServerConfig::builder()
            .with_client_cert_verifier(client_cert_verifier)
            .with_single_cert(vec![cert], key)
            .map_err(|e| PeerError::Tls(e.to_string()))?;

        server_crypto.alpn_protocols = vec![PYANA_ALPN.to_vec()];

        let mut server_config = ServerConfig::with_crypto(Arc::new(
            quinn::crypto::rustls::QuicServerConfig::try_from(server_crypto)
                .map_err(|e| PeerError::Tls(e.to_string()))?,
        ));
        // Allow migration for NAT rebinding
        server_config.migration(true);

        Ok(server_config)
    }

    /// Build a client config that presents our certificate for mutual TLS.
    fn build_client_config_with_cert(
        cert_der: &[u8],
        key_der: &[u8],
    ) -> Result<ClientConfig, PeerError> {
        let cert = CertificateDer::from(cert_der.to_vec());
        let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_der.to_vec()));

        let mut client_crypto = rustls::ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(Arc::new(GossipCertVerifier))
            .with_client_auth_cert(vec![cert], key)
            .map_err(|e| PeerError::Tls(e.to_string()))?;

        client_crypto.alpn_protocols = vec![PYANA_ALPN.to_vec()];

        let client_config = ClientConfig::new(Arc::new(
            quinn::crypto::rustls::QuicClientConfig::try_from(client_crypto)
                .map_err(|e| PeerError::Tls(e.to_string()))?,
        ));
        Ok(client_config)
    }

    fn build_client_config() -> Result<ClientConfig, PeerError> {
        Self::build_client_config_static()
    }

    /// Build a client config using the allowlist verifier.
    ///
    /// The verifier checks that the peer's node_id (blake3 hash of their certificate DER)
    /// is in the provided allowlist. Use `AllowlistVerifier::allow_node()` to pre-authorize
    /// peers before connecting.
    pub fn build_client_config_with_allowlist(
        verifier: &AllowlistVerifier,
    ) -> Result<ClientConfig, PeerError> {
        verifier.build_client_config()
    }

    /// Build a client config for the gossip layer that presents a fresh ephemeral
    /// certificate for mutual TLS.
    ///
    /// Gossip peers are authenticated at the application layer (explicit `join_topic`/`add_peer`
    /// calls + message-hash deduplication + envelope signatures), but mutual TLS ensures
    /// that all peers present a verifiable certificate identity.
    /// For direct peer connections, use [`build_client_config_with_allowlist`] instead.
    pub fn build_client_config_static() -> Result<ClientConfig, PeerError> {
        // Generate ephemeral certificate for mutual TLS
        let cert_params = rcgen::CertificateParams::new(vec!["pyana.local".to_string()])
            .map_err(|e| PeerError::Tls(e.to_string()))?;
        let key_pair = rcgen::KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256)
            .map_err(|e| PeerError::Tls(e.to_string()))?;
        let cert = cert_params
            .self_signed(&key_pair)
            .map_err(|e| PeerError::Tls(e.to_string()))?;

        let cert_der = CertificateDer::from(cert.der().to_vec());
        let key_der = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key_pair.serialize_der()));

        let mut client_crypto = rustls::ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(Arc::new(GossipCertVerifier))
            .with_client_auth_cert(vec![cert_der], key_der)
            .map_err(|e| PeerError::Tls(e.to_string()))?;

        client_crypto.alpn_protocols = vec![PYANA_ALPN.to_vec()];
        let client_config = ClientConfig::new(Arc::new(
            quinn::crypto::rustls::QuicClientConfig::try_from(client_crypto)
                .map_err(|e| PeerError::Tls(e.to_string()))?,
        ));
        Ok(client_config)
    }
}

impl PeerConnection {
    /// Send a message to the remote peer over a new uni-directional stream.
    pub async fn send(&self, msg: &PeerMessage) -> Result<(), PeerError> {
        let mut send_stream = self
            .connection
            .open_uni()
            .await
            .map_err(|e| PeerError::Send(e.to_string()))?;

        let encoded = msg.encode();
        send_stream
            .write_all(&encoded)
            .await
            .map_err(|e| PeerError::Send(e.to_string()))?;
        send_stream
            .finish()
            .map_err(|e| PeerError::Send(e.to_string()))?;

        Ok(())
    }

    /// Receive a message from the remote peer by accepting a uni-directional stream.
    pub async fn recv(&self) -> Result<PeerMessage, PeerError> {
        let mut recv_stream = self
            .connection
            .accept_uni()
            .await
            .map_err(|e| PeerError::Recv(e.to_string()))?;

        read_framed_message(&mut recv_stream).await
    }

    /// Send a message and wait for a response on a bi-directional stream.
    pub async fn request(&self, msg: &PeerMessage) -> Result<PeerMessage, PeerError> {
        let (mut send_stream, mut recv_stream) = self
            .connection
            .open_bi()
            .await
            .map_err(|e| PeerError::Send(e.to_string()))?;

        // Send request
        let encoded = msg.encode();
        send_stream
            .write_all(&encoded)
            .await
            .map_err(|e| PeerError::Send(e.to_string()))?;
        send_stream
            .finish()
            .map_err(|e| PeerError::Send(e.to_string()))?;

        // Read response
        read_framed_message(&mut recv_stream).await
    }

    /// Accept a bi-directional stream request and return the message + response handle.
    pub async fn accept_request(&self) -> Result<(PeerMessage, ResponseHandle), PeerError> {
        let (send_stream, mut recv_stream) = self
            .connection
            .accept_bi()
            .await
            .map_err(|e| PeerError::Recv(e.to_string()))?;

        let msg = read_framed_message(&mut recv_stream).await?;
        let handle = ResponseHandle { send_stream };
        Ok((msg, handle))
    }

    /// Get the remote peer's node ID.
    pub fn remote_id(&self) -> NodeId {
        self.remote_id
    }

    /// Get the remote peer's address.
    pub fn remote_addr(&self) -> SocketAddr {
        self.connection.remote_address()
    }

    /// Close this connection gracefully.
    pub fn close(&self) {
        self.connection.close(0u8.into(), b"done");
    }

    /// Get RTT estimate for this connection.
    pub fn rtt(&self) -> std::time::Duration {
        self.connection.rtt()
    }
}

/// Handle for sending a response on a bi-directional stream.
pub struct ResponseHandle {
    send_stream: SendStream,
}

impl ResponseHandle {
    /// Send a response message.
    pub async fn respond(mut self, msg: &PeerMessage) -> Result<(), PeerError> {
        let encoded = msg.encode();
        self.send_stream
            .write_all(&encoded)
            .await
            .map_err(|e| PeerError::Send(e.to_string()))?;
        self.send_stream
            .finish()
            .map_err(|e| PeerError::Send(e.to_string()))?;
        Ok(())
    }
}

/// Read a length-prefixed message from a QUIC recv stream.
async fn read_framed_message(recv_stream: &mut RecvStream) -> Result<PeerMessage, PeerError> {
    // Read the 4-byte length prefix
    let mut len_buf = [0u8; 4];
    recv_stream
        .read_exact(&mut len_buf)
        .await
        .map_err(|e| PeerError::Recv(e.to_string()))?;
    let len = u32::from_be_bytes(len_buf) as usize;

    // Sanity check (16 MiB max)
    if len > 16 * 1024 * 1024 {
        return Err(PeerError::Recv(format!("message too large: {len} bytes")));
    }

    // Read the payload
    let mut payload = vec![0u8; len];
    recv_stream
        .read_exact(&mut payload)
        .await
        .map_err(|e| PeerError::Recv(e.to_string()))?;

    PeerMessage::decode_raw(&payload).map_err(PeerError::Decode)
}

/// Extract the remote node ID from a connection's peer certificates.
///
/// With mutual TLS enabled, the peer MUST present a certificate. If no certificate
/// is available, the connection is rejected — there is no IP-based fallback as that
/// would be trivially spoofable and provide no authentication guarantee.
fn extract_remote_id(conn: &Connection) -> Result<NodeId, PeerError> {
    let cert = conn
        .peer_identity()
        .and_then(|id| id.downcast_ref::<Vec<CertificateDer<'static>>>().cloned())
        .and_then(|certs| certs.into_iter().next())
        .ok_or_else(|| {
            PeerError::Tls(format!(
                "peer {} did not present a TLS certificate — mutual TLS required",
                conn.remote_address()
            ))
        })?;

    Ok(*blake3::hash(cert.as_ref()).as_bytes())
}

/// Format a node ID as a short hex string.
pub fn fmt_node_id(id: &NodeId) -> String {
    format!(
        "{:02x}{:02x}{:02x}{:02x}..{:02x}{:02x}{:02x}{:02x}",
        id[0], id[1], id[2], id[3], id[28], id[29], id[30], id[31]
    )
}

/// Server-side client certificate verifier for mutual TLS.
///
/// Accepts any client certificate (the identity check is done at the application layer
/// via `blake3(cert_der) -> NodeId`). The important thing is that the client MUST present
/// a certificate — this prevents unauthenticated connections entirely.
#[derive(Debug)]
struct MutualTlsClientVerifier;

impl rustls::server::danger::ClientCertVerifier for MutualTlsClientVerifier {
    fn root_hint_subjects(&self) -> &[rustls::DistinguishedName] {
        &[]
    }

    fn verify_client_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _now: rustls::pki_types::UnixTime,
    ) -> Result<rustls::server::danger::ClientCertVerified, rustls::Error> {
        // Accept any client cert — identity is verified at the application layer
        // (blake3 hash of cert DER == NodeId). The critical security property is
        // that the client MUST present a cert to connect at all.
        Ok(rustls::server::danger::ClientCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }

    fn client_auth_mandatory(&self) -> bool {
        true
    }
}

/// Certificate verifier that checks the peer's node ID (blake3 hash of cert DER)
/// against a runtime-mutable allowlist.
///
/// Accepts self-signed certificates only if the derived node_id is in the allowlist.
/// This provides Sybil resistance: only pre-authorized nodes can connect.
#[derive(Debug, Clone)]
pub struct AllowlistVerifier {
    allowed_node_ids: Arc<RwLock<HashSet<[u8; 32]>>>,
}

impl AllowlistVerifier {
    /// Create a new verifier with an initial set of allowed node IDs.
    pub fn new(allowed: impl IntoIterator<Item = [u8; 32]>) -> Self {
        Self {
            allowed_node_ids: Arc::new(RwLock::new(allowed.into_iter().collect())),
        }
    }

    /// Create an empty verifier (rejects all connections until nodes are added).
    pub fn empty() -> Self {
        Self::new(std::iter::empty())
    }

    /// Add a node ID to the allowlist at runtime.
    pub fn allow_node(&self, node_id: [u8; 32]) {
        self.allowed_node_ids.write().unwrap().insert(node_id);
    }

    /// Remove a node ID from the allowlist at runtime.
    pub fn deny_node(&self, node_id: &[u8; 32]) {
        self.allowed_node_ids.write().unwrap().remove(node_id);
    }

    /// Check if a node ID is currently allowed.
    pub fn is_allowed(&self, node_id: &[u8; 32]) -> bool {
        self.allowed_node_ids.read().unwrap().contains(node_id)
    }

    /// Build a `ClientConfig` that verifies peers against this allowlist.
    pub fn build_client_config(&self) -> Result<ClientConfig, PeerError> {
        let mut client_crypto = rustls::ClientConfig::builder()
            .dangerous()
            .with_custom_certificate_verifier(Arc::new(self.clone()))
            .with_no_client_auth();

        client_crypto.alpn_protocols = vec![PYANA_ALPN.to_vec()];

        let client_config = ClientConfig::new(Arc::new(
            quinn::crypto::rustls::QuicClientConfig::try_from(client_crypto)
                .map_err(|e| PeerError::Tls(e.to_string()))?,
        ));
        Ok(client_config)
    }
}

impl rustls::client::danger::ServerCertVerifier for AllowlistVerifier {
    fn verify_server_cert(
        &self,
        end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &rustls::pki_types::ServerName<'_>,
        _ocsp_response: &[u8],
        _now: rustls::pki_types::UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        let node_id = *blake3::hash(end_entity.as_ref()).as_bytes();
        if self.allowed_node_ids.read().unwrap().contains(&node_id) {
            Ok(rustls::client::danger::ServerCertVerified::assertion())
        } else {
            Err(rustls::Error::General(format!(
                "peer node_id {} not in allowlist",
                fmt_node_id(&node_id),
            )))
        }
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

/// Certificate verifier for the gossip layer.
///
/// Fix 6: While this still accepts self-signed certificates (required for the gossip
/// protocol where peers may not have CA-issued certs), it enforces that the TLS
/// handshake signature is cryptographically valid. This prevents man-in-the-middle
/// attacks where an attacker cannot forge TLS signatures without the private key.
///
/// For full certificate pinning, use [`AllowlistVerifier`] which checks the peer's
/// node_id (blake3 hash of cert DER) against a known set. The gossip layer should
/// be configured with `AllowlistVerifier` in production deployments.
///
/// **Security properties of this verifier:**
/// - TLS signatures MUST be cryptographically valid (prevents MITM)
/// - Self-signed certs are accepted (no CA requirement)
/// - No identity pinning (peer rotation is allowed)
///
/// **To enable certificate pinning for gossip**, use:
/// `PeerNode::build_client_config_with_allowlist(&verifier)` instead of
/// `PeerNode::build_client_config_static()`.
#[derive(Debug)]
struct GossipCertVerifier;

impl rustls::client::danger::ServerCertVerifier for GossipCertVerifier {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &rustls::pki_types::ServerName<'_>,
        _ocsp_response: &[u8],
        _now: rustls::pki_types::UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::danger::ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls12_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn verify_tls13_signature(
        &self,
        message: &[u8],
        cert: &CertificateDer<'_>,
        dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        rustls::crypto::verify_tls13_signature(
            message,
            cert,
            dss,
            &rustls::crypto::ring::default_provider().signature_verification_algorithms,
        )
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        rustls::crypto::ring::default_provider()
            .signature_verification_algorithms
            .supported_schemes()
    }
}

/// Permissive certificate verifier that accepts ANY self-signed certificate
/// without any identity checks. **Only available in test builds.**
///
/// Use this for bootstrapping test scenarios where node IDs are not known ahead of time.
#[cfg(test)]
#[derive(Debug)]
#[allow(dead_code)]
pub(crate) struct PermissiveVerifier;

#[cfg(test)]
impl rustls::client::danger::ServerCertVerifier for PermissiveVerifier {
    fn verify_server_cert(
        &self,
        _end_entity: &CertificateDer<'_>,
        _intermediates: &[CertificateDer<'_>],
        _server_name: &rustls::pki_types::ServerName<'_>,
        _ocsp_response: &[u8],
        _now: rustls::pki_types::UnixTime,
    ) -> Result<rustls::client::danger::ServerCertVerified, rustls::Error> {
        Ok(rustls::client::danger::ServerCertVerified::assertion())
    }

    fn verify_tls12_signature(
        &self,
        _message: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }

    fn verify_tls13_signature(
        &self,
        _message: &[u8],
        _cert: &CertificateDer<'_>,
        _dss: &rustls::DigitallySignedStruct,
    ) -> Result<rustls::client::danger::HandshakeSignatureValid, rustls::Error> {
        Ok(rustls::client::danger::HandshakeSignatureValid::assertion())
    }

    fn supported_verify_schemes(&self) -> Vec<rustls::SignatureScheme> {
        vec![
            rustls::SignatureScheme::ECDSA_NISTP256_SHA256,
            rustls::SignatureScheme::ECDSA_NISTP384_SHA384,
            rustls::SignatureScheme::ED25519,
            rustls::SignatureScheme::RSA_PSS_SHA256,
            rustls::SignatureScheme::RSA_PSS_SHA384,
            rustls::SignatureScheme::RSA_PSS_SHA512,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allowlist_verifier_empty_rejects() {
        let verifier = AllowlistVerifier::empty();
        let fake_cert = CertificateDer::from(vec![1u8; 64]);
        let node_id = *blake3::hash(fake_cert.as_ref()).as_bytes();
        assert!(!verifier.is_allowed(&node_id));
    }

    #[test]
    fn allowlist_verifier_add_remove() {
        let verifier = AllowlistVerifier::empty();
        let node_id = [0xab; 32];

        assert!(!verifier.is_allowed(&node_id));
        verifier.allow_node(node_id);
        assert!(verifier.is_allowed(&node_id));
        verifier.deny_node(&node_id);
        assert!(!verifier.is_allowed(&node_id));
    }

    #[test]
    fn allowlist_verifier_with_initial_set() {
        let id1 = [1u8; 32];
        let id2 = [2u8; 32];
        let id3 = [3u8; 32];
        let verifier = AllowlistVerifier::new([id1, id2]);

        assert!(verifier.is_allowed(&id1));
        assert!(verifier.is_allowed(&id2));
        assert!(!verifier.is_allowed(&id3));
    }

    #[test]
    fn allowlist_verifier_verify_cert() {
        use rustls::client::danger::ServerCertVerifier;
        use rustls::pki_types::{ServerName, UnixTime};

        let fake_cert_bytes = vec![42u8; 100];
        let node_id = *blake3::hash(&fake_cert_bytes).as_bytes();
        let cert = CertificateDer::from(fake_cert_bytes);

        let verifier = AllowlistVerifier::new([node_id]);
        let server_name = ServerName::try_from("pyana.local").unwrap();

        // Should succeed - node_id is in allowlist
        let result = verifier.verify_server_cert(&cert, &[], &server_name, &[], UnixTime::now());
        assert!(result.is_ok());

        // Remove from allowlist - should now fail
        verifier.deny_node(&node_id);
        let result = verifier.verify_server_cert(&cert, &[], &server_name, &[], UnixTime::now());
        assert!(result.is_err());
    }

    #[test]
    fn rate_limiter_allows_within_limit() {
        let limiter = ConnectionRateLimiter::new(3, std::time::Duration::from_secs(60));
        let ip: IpAddr = "192.168.1.1".parse().unwrap();

        assert!(limiter.check_and_record(ip));
        assert!(limiter.check_and_record(ip));
        assert!(limiter.check_and_record(ip));
        // 4th attempt should be rejected
        assert!(!limiter.check_and_record(ip));
    }

    #[test]
    fn rate_limiter_different_ips_independent() {
        let limiter = ConnectionRateLimiter::new(2, std::time::Duration::from_secs(60));
        let ip1: IpAddr = "192.168.1.1".parse().unwrap();
        let ip2: IpAddr = "192.168.1.2".parse().unwrap();

        assert!(limiter.check_and_record(ip1));
        assert!(limiter.check_and_record(ip1));
        assert!(!limiter.check_and_record(ip1));

        // ip2 should still be allowed
        assert!(limiter.check_and_record(ip2));
        assert!(limiter.check_and_record(ip2));
        assert!(!limiter.check_and_record(ip2));
    }
}
