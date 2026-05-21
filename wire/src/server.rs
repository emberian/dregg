//! Silo server: a TCP server that handles incoming wire protocol connections.
//!
//! Each silo server represents one organizational silo in the federation. It can:
//! - Accept incoming connections from peer silos
//! - Handle token presentations (verify proofs against the federation root)
//! - Process revocation submissions
//! - Serve the current attested root and non-membership proofs
//! - Initiate outgoing connections for cross-silo token presentation

use crate::connection::{ConnectionError, PeerConnection};
use crate::message::{AuthorizationRequest, PROTOCOL_VERSION, PublicKey, Signature, WireMessage};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::net::TcpListener;
use tokio::sync::{Mutex, RwLock};

// =============================================================================
// Proof Verifier Trait
// =============================================================================

/// Trait for verifying presentation proofs.
///
/// Callers must inject a verifier implementation into `SiloConfig`. This ensures
/// no code path silently accepts invalid proofs -- either real verification is
/// performed, or the caller explicitly opts into a test-only noop verifier.
pub trait ProofVerifier: Send + Sync + std::fmt::Debug {
    /// Verify a serialized STARK presentation proof bound to a specific request.
    ///
    /// The `request_digest` is the BLAKE3 hash of the authorization request.
    /// Implementations MUST check that the proof is cryptographically bound to
    /// this specific request, preventing replay attacks where a valid proof for
    /// one request is presented against a different request.
    ///
    /// Returns `Ok(true)` if the proof is cryptographically valid and bound to
    /// the request, `Ok(false)` if verification ran but the proof is invalid,
    /// `Err(reason)` if the proof could not be parsed or checked.
    fn verify(&self, proof_bytes: &[u8], request_digest: &[u8; 32]) -> Result<bool, String>;
}

/// Real STARK proof verifier using pyana-circuit.
///
/// Deserializes the proof bytes and runs full STARK verification
/// (Merkle commitments, FRI low-degree test, Fiat-Shamir checks).
///
/// Tries `MerklePoseidon2StarkAir` first (production path, collision-resistant),
/// then falls back to `MerkleStarkAir` (legacy linear binding) for backward
/// compatibility with older proofs.
#[derive(Clone, Debug)]
pub struct StarkVerifier;

impl ProofVerifier for StarkVerifier {
    fn verify(&self, proof_bytes: &[u8], request_digest: &[u8; 32]) -> Result<bool, String> {
        let proof = pyana_circuit::stark::proof_from_bytes(proof_bytes)?;
        let public_inputs: Vec<pyana_circuit::field::BabyBear> = proof
            .public_inputs
            .iter()
            .map(|&v| pyana_circuit::field::BabyBear(v))
            .collect();

        // Verify action binding: the proof's last public input must be a commitment
        // to the request being authorized. This prevents replay attacks where a
        // valid proof for one request is presented against a different request.
        let action_commitment = pyana_circuit::poseidon2::hash_many(
            &pyana_circuit::field::BabyBear::encode_hash(request_digest),
        );
        match public_inputs.last() {
            Some(&last_pi) if last_pi == action_commitment => {}
            _ => return Ok(false), // Proof not bound to this request
        }

        // Try Poseidon2 AIR first (production path).
        let poseidon2_air = pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir;
        match pyana_circuit::stark::verify(&poseidon2_air, &proof, &public_inputs) {
            Ok(()) => return Ok(true),
            Err(_) => {}
        }

        // Fall back to legacy linear AIR for backward compatibility.
        let linear_air = pyana_circuit::stark::MerkleStarkAir;
        match pyana_circuit::stark::verify(&linear_air, &proof, &public_inputs) {
            Ok(()) => Ok(true),
            Err(_reason) => Ok(false),
        }
    }
}

/// A no-op verifier that always accepts proofs without cryptographic checks.
///
/// Only available when the `dev` feature is enabled or in test builds.
/// Production code should use [`StarkVerifier`] which performs full STARK verification.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct NoopVerifier;

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for NoopVerifier {
    fn verify(&self, _proof_bytes: &[u8], _request_digest: &[u8; 32]) -> Result<bool, String> {
        Ok(true)
    }
}

/// A verifier that always rejects. Available only for testing.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct RejectAllVerifier;

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for RejectAllVerifier {
    fn verify(&self, _proof_bytes: &[u8], _request_digest: &[u8; 32]) -> Result<bool, String> {
        Ok(false)
    }
}

/// A verifier that requires a minimum proof size. Available only for testing
/// transport framing without real crypto.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub struct MinSizeVerifier {
    pub min_bytes: usize,
}

#[cfg(any(test, feature = "dev"))]
impl ProofVerifier for MinSizeVerifier {
    fn verify(&self, proof_bytes: &[u8], _request_digest: &[u8; 32]) -> Result<bool, String> {
        Ok(proof_bytes.len() >= self.min_bytes)
    }
}

// =============================================================================
// Silo Configuration
// =============================================================================

/// Configuration for a silo server.
#[derive(Clone, Debug)]
pub struct SiloConfig {
    /// Human-readable name for this silo (e.g., "acme.corp").
    pub name: String,
    /// This node's identity key.
    pub node_id: [u8; 32],
    /// Capabilities this silo advertises.
    pub capabilities: Vec<String>,
    /// Maximum concurrent connections.
    pub max_connections: usize,
    /// Connection timeout for incoming handshakes.
    pub handshake_timeout: Duration,
    /// The proof verifier used to check incoming presentation proofs.
    pub verifier: Arc<dyn ProofVerifier>,
}

impl SiloConfig {
    /// Create a new silo config with real STARK verification as the default.
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        let node_id = *blake3::hash(name.as_bytes()).as_bytes();
        Self {
            name,
            node_id,
            capabilities: vec![
                "present".to_string(),
                "revoke".to_string(),
                "sync".to_string(),
            ],
            max_connections: 64,
            handshake_timeout: Duration::from_secs(10),
            verifier: Arc::new(StarkVerifier),
        }
    }

    /// Set a custom proof verifier.
    pub fn with_verifier(mut self, verifier: Arc<dyn ProofVerifier>) -> Self {
        self.verifier = verifier;
        self
    }
}

/// Legacy type alias retained for source compatibility in tests.
/// New code should use `SiloConfig::with_verifier()` directly.
#[cfg(any(test, feature = "dev"))]
#[derive(Clone, Debug)]
pub enum VerificationMode {
    /// Always accept. Equivalent to `NoopVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(NoopVerifier)) instead")]
    SimulatedAccept,
    /// Always reject. Equivalent to `RejectAllVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(RejectAllVerifier)) instead")]
    SimulatedReject,
    /// Size gate. Equivalent to `MinSizeVerifier`.
    #[deprecated(note = "Use SiloConfig::with_verifier(Arc::new(MinSizeVerifier { .. })) instead")]
    MinProofSize(usize),
}

#[cfg(any(test, feature = "dev"))]
impl SiloConfig {
    /// Convenience: set verifier from a legacy VerificationMode.
    #[allow(deprecated)]
    pub fn with_verification(self, mode: VerificationMode) -> Self {
        let verifier: Arc<dyn ProofVerifier> = match mode {
            VerificationMode::SimulatedAccept => Arc::new(NoopVerifier),
            VerificationMode::SimulatedReject => Arc::new(RejectAllVerifier),
            VerificationMode::MinProofSize(n) => Arc::new(MinSizeVerifier { min_bytes: n }),
        };
        self.with_verifier(verifier)
    }
}

// =============================================================================
// Revocation Handler Trait
// =============================================================================

/// Trait for delegating revocation logic to an external handler.
///
/// This allows the silo server to delegate revocation submission, status checks,
/// and root computation to an external system (e.g., a `pyana-federation` backed
/// handler) while maintaining backward compatibility with the standalone logic.
pub trait RevocationHandler: Send + Sync {
    /// Submit a revocation for a token, returning true if accepted.
    fn submit_revocation(&self, token_id: &str, sig: &[u8; 64]) -> bool;
    /// Check whether a token has been revoked.
    fn is_revoked(&self, token_id: &str) -> bool;
    /// Get the current revocation root hash.
    fn current_root(&self) -> [u8; 32];
}

/// Default revocation handler that wraps the existing standalone logic
/// (Vec<String> + BLAKE3 hash chain). This preserves backward compatibility
/// for existing tests and deployments.
///
/// # Deprecation Notice
///
/// This handler uses a BLAKE3 hash chain for root computation, which is **not
/// consistent** with the 4-ary Merkle tree used by `pyana-federation`'s
/// `RevocationTree`. For federation-connected deployments, use
/// [`FederationBridge`](crate::federation_bridge::FederationBridge) as the
/// `RevocationHandler` instead.
#[derive(Clone, Debug)]
pub struct DefaultRevocationHandler {
    /// Revoked token IDs.
    revoked_tokens: std::sync::Arc<std::sync::RwLock<Vec<String>>>,
    /// Current root hash.
    root: std::sync::Arc<std::sync::RwLock<[u8; 32]>>,
    /// Current height (for hash chain).
    height: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

impl DefaultRevocationHandler {
    /// Create a new default handler with the given genesis root.
    pub fn new(genesis_root: [u8; 32]) -> Self {
        Self {
            revoked_tokens: std::sync::Arc::new(std::sync::RwLock::new(Vec::new())),
            root: std::sync::Arc::new(std::sync::RwLock::new(genesis_root)),
            height: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }
}

impl RevocationHandler for DefaultRevocationHandler {
    fn submit_revocation(&self, token_id: &str, sig: &[u8; 64]) -> bool {
        let mut tokens = self.revoked_tokens.write().unwrap();
        let new_height = self
            .height
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            + 1;
        tokens.push(token_id.to_string());

        let mut root = self.root.write().unwrap();
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-root v1");
        hasher.update(&*root);
        hasher.update(token_id.as_bytes());
        hasher.update(sig);
        hasher.update(&new_height.to_le_bytes());
        *root = *hasher.finalize().as_bytes();

        true
    }

    fn is_revoked(&self, token_id: &str) -> bool {
        let tokens = self.revoked_tokens.read().unwrap();
        tokens.iter().any(|t| t == token_id)
    }

    fn current_root(&self) -> [u8; 32] {
        *self.root.read().unwrap()
    }
}

// =============================================================================
// Silo State
// =============================================================================

/// Mutable state for the silo server.
#[derive(Clone, Debug)]
pub struct SiloState {
    /// The current federation root.
    ///
    /// **Canonical source**: When a [`RevocationHandler`] is configured on the
    /// [`SiloServer`], this field is updated from the handler's `current_root()`
    /// after each revocation. The handler (typically backed by a
    /// `pyana-federation` `RevocationTree`) is the single source of truth.
    ///
    /// When no handler is configured, the standalone BLAKE3 hash-chain
    /// computation in [`SiloState::apply_revocation_standalone`] is used as a
    /// fallback (e.g., in tests or single-node deployments).
    pub federation_root: [u8; 32],
    /// Current block height.
    pub height: u64,
    /// Number of members in the federation.
    pub member_count: u32,
    /// Revoked token IDs (simplified; in production this is a Merkle tree).
    pub revoked_tokens: Vec<String>,
    /// Signatures on the current root: (public_key, signature) pairs.
    /// Signatures are full 64-byte Ed25519.
    pub root_signatures: Vec<(PublicKey, Signature)>,
}

impl SiloState {
    /// Create initial state with a genesis root.
    pub fn genesis(member_count: u32) -> Self {
        let root = *blake3::hash(b"pyana-federation-genesis").as_bytes();
        Self {
            federation_root: root,
            height: 0,
            member_count,
            revoked_tokens: Vec::new(),
            root_signatures: Vec::new(),
        }
    }

    /// Apply a revocation event using the federation's `RevocationHandler` as the
    /// canonical root source.
    ///
    /// This updates the local revocation index and height, then sets
    /// `federation_root` to the handler's `current_root()`. The handler
    /// (backed by `pyana-federation`'s `RevocationTree`) is the single source
    /// of truth for the Merkle root.
    ///
    /// If no handler is available, use [`apply_revocation_standalone`] instead.
    pub fn apply_revocation_delegated(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
        handler: &dyn RevocationHandler,
    ) {
        self.revoked_tokens.push(token_id.to_string());
        self.height += 1;

        // The handler already processed the revocation; just adopt its root.
        self.federation_root = handler.current_root();

        // Add the authority's signature to the root attestation.
        self.root_signatures.push((*authority, *authority_sig));
    }

    /// Apply a revocation event using the standalone BLAKE3 hash-chain.
    ///
    /// # Deprecation Notice
    ///
    /// This method computes a root via a sequential BLAKE3 hash chain, which is
    /// **not consistent** with the 4-ary Merkle tree used by `pyana-federation`'s
    /// `RevocationTree`. It exists for backward compatibility in tests and
    /// single-node deployments where no `RevocationHandler` is configured.
    ///
    /// New code should use [`apply_revocation_delegated`] with a handler backed
    /// by `pyana-federation::RevocationTree` to ensure root consistency across
    /// the federation.
    #[deprecated(
        note = "Use apply_revocation_delegated() with a RevocationHandler for consistent roots"
    )]
    pub fn apply_revocation_standalone(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) {
        self.revoked_tokens.push(token_id.to_string());
        self.height += 1;

        // Standalone BLAKE3 hash-chain root (NOT consistent with federation Merkle tree).
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wire revocation-root v1");
        hasher.update(&self.federation_root);
        hasher.update(token_id.as_bytes());
        hasher.update(&authority_sig.0);
        hasher.update(&self.height.to_le_bytes());
        self.federation_root = *hasher.finalize().as_bytes();

        // Add the authority's signature to the root attestation.
        self.root_signatures.push((*authority, *authority_sig));
    }

    /// Apply a revocation event and update the root.
    ///
    /// **Deprecated**: This is an alias for [`apply_revocation_standalone`] kept
    /// for source compatibility. Prefer [`apply_revocation_delegated`] when a
    /// `RevocationHandler` is available.
    pub fn apply_revocation(
        &mut self,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) {
        #[allow(deprecated)]
        self.apply_revocation_standalone(token_id, authority, authority_sig);
    }

    /// Check if a token is revoked.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked_tokens.iter().any(|t| t == token_id)
    }
}

// =============================================================================
// Silo Server
// =============================================================================

/// A TCP server representing one silo in the federation.
///
/// Handles incoming connections, processes wire protocol messages, and
/// maintains federation state.
pub struct SiloServer {
    /// The address this server listens on.
    addr: SocketAddr,
    /// Server configuration.
    config: Arc<SiloConfig>,
    /// Shared mutable state.
    state: Arc<RwLock<SiloState>>,
    /// Event log for diagnostics.
    event_log: Arc<Mutex<Vec<ServerEvent>>>,
    /// Revocation handler for delegating revocation logic.
    /// Defaults to `DefaultRevocationHandler` which wraps the standalone logic.
    revocation_handler: Option<Arc<dyn RevocationHandler>>,
}

/// Events logged by the server for diagnostics.
#[derive(Clone, Debug)]
pub enum ServerEvent {
    /// A new connection was accepted.
    ConnectionAccepted { remote: SocketAddr },
    /// A Hello message was received.
    HelloReceived {
        node_name: String,
        remote: SocketAddr,
    },
    /// A token was presented.
    TokenPresented {
        proof_size: usize,
        accepted: bool,
        remote: SocketAddr,
    },
    /// A revocation was submitted.
    RevocationSubmitted {
        token_id: String,
        new_height: u64,
        remote: SocketAddr,
    },
    /// A non-membership proof was requested.
    NonMembershipRequested {
        token_id: String,
        found: bool,
        remote: SocketAddr,
    },
    /// An error occurred while handling a connection.
    ConnectionError { error: String, remote: SocketAddr },
}

impl SiloServer {
    /// Create a new silo server.
    pub fn new(addr: SocketAddr, config: SiloConfig) -> Self {
        let member_count = config.capabilities.len() as u32 + 2; // arbitrary for demo
        Self {
            addr,
            config: Arc::new(config),
            state: Arc::new(RwLock::new(SiloState::genesis(member_count))),
            event_log: Arc::new(Mutex::new(Vec::new())),
            revocation_handler: None,
        }
    }

    /// Create a silo server with pre-initialized state.
    pub fn with_state(addr: SocketAddr, config: SiloConfig, state: SiloState) -> Self {
        Self {
            addr,
            config: Arc::new(config),
            state: Arc::new(RwLock::new(state)),
            event_log: Arc::new(Mutex::new(Vec::new())),
            revocation_handler: None,
        }
    }

    /// Set a custom revocation handler for delegating revocation logic.
    ///
    /// When set, `SubmitRevocation` messages will be routed through this handler
    /// instead of the built-in `SiloState::apply_revocation()` logic.
    pub fn with_revocation_handler(mut self, handler: Arc<dyn RevocationHandler>) -> Self {
        self.revocation_handler = Some(handler);
        self
    }

    /// Get the listening address.
    pub fn addr(&self) -> SocketAddr {
        self.addr
    }

    /// Get the silo name.
    pub fn name(&self) -> &str {
        &self.config.name
    }

    /// Get a snapshot of the current state.
    pub async fn state(&self) -> SiloState {
        self.state.read().await.clone()
    }

    /// Get the event log.
    pub async fn events(&self) -> Vec<ServerEvent> {
        self.event_log.lock().await.clone()
    }

    /// Run the server, accepting and handling connections.
    ///
    /// This runs indefinitely until the task is cancelled.
    pub async fn run(&self) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(self.addr).await?;
        // Update addr to reflect the actual bound address (useful for port 0)
        let _actual_addr = listener.local_addr()?;

        loop {
            let (stream, remote_addr) = listener.accept().await?;
            let config = Arc::clone(&self.config);
            let state = Arc::clone(&self.state);
            let event_log = Arc::clone(&self.event_log);
            let revocation_handler = self.revocation_handler.clone();

            tokio::spawn(async move {
                Self::handle_connection(
                    stream,
                    remote_addr,
                    config,
                    state,
                    event_log,
                    revocation_handler,
                )
                .await;
            });
        }
    }

    /// Run the server and return the actual bound address.
    ///
    /// Useful when binding to port 0 (OS-assigned port). The returned oneshot
    /// fires with the actual address once the server is listening.
    pub async fn run_with_addr(
        &self,
        addr_tx: tokio::sync::oneshot::Sender<SocketAddr>,
    ) -> Result<(), std::io::Error> {
        let listener = TcpListener::bind(self.addr).await?;
        let actual_addr = listener.local_addr()?;
        let _ = addr_tx.send(actual_addr);

        loop {
            let (stream, remote_addr) = listener.accept().await?;
            let config = Arc::clone(&self.config);
            let state = Arc::clone(&self.state);
            let event_log = Arc::clone(&self.event_log);
            let revocation_handler = self.revocation_handler.clone();

            tokio::spawn(async move {
                Self::handle_connection(
                    stream,
                    remote_addr,
                    config,
                    state,
                    event_log,
                    revocation_handler,
                )
                .await;
            });
        }
    }

    /// Handle a single connection.
    async fn handle_connection(
        stream: tokio::net::TcpStream,
        remote_addr: SocketAddr,
        config: Arc<SiloConfig>,
        state: Arc<RwLock<SiloState>>,
        event_log: Arc<Mutex<Vec<ServerEvent>>>,
        revocation_handler: Option<Arc<dyn RevocationHandler>>,
    ) {
        event_log
            .lock()
            .await
            .push(ServerEvent::ConnectionAccepted {
                remote: remote_addr,
            });

        let mut conn = PeerConnection::from_stream(stream);

        // Process messages until the connection closes
        loop {
            let msg = match conn.recv_timeout(Duration::from_secs(60)).await {
                Ok(msg) => msg,
                Err(ConnectionError::Closed) => break,
                Err(ConnectionError::Timeout) => {
                    // Send a ping to check liveness
                    let ping = WireMessage::Ping {
                        seq: 0,
                        timestamp: current_timestamp(),
                    };
                    if conn.send(ping).await.is_err() {
                        break;
                    }
                    continue;
                }
                Err(e) => {
                    event_log.lock().await.push(ServerEvent::ConnectionError {
                        error: e.to_string(),
                        remote: remote_addr,
                    });
                    break;
                }
            };

            let response = Self::process_message(
                msg,
                remote_addr,
                &config,
                &state,
                &event_log,
                revocation_handler.as_deref(),
            )
            .await;

            if let Some(response) = response {
                if conn.send(response).await.is_err() {
                    break;
                }
            }
        }
    }

    /// Process a single message and return an optional response.
    async fn process_message(
        msg: WireMessage,
        remote_addr: SocketAddr,
        config: &SiloConfig,
        state: &RwLock<SiloState>,
        event_log: &Mutex<Vec<ServerEvent>>,
        revocation_handler: Option<&dyn RevocationHandler>,
    ) -> Option<WireMessage> {
        match msg {
            WireMessage::Hello {
                node_id: _,
                node_name,
                protocol_version,
                capabilities: _,
            } => {
                event_log.lock().await.push(ServerEvent::HelloReceived {
                    node_name: node_name.clone(),
                    remote: remote_addr,
                });

                if protocol_version != PROTOCOL_VERSION {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::UNSUPPORTED_VERSION,
                        message: format!(
                            "unsupported protocol version {protocol_version}, expected {PROTOCOL_VERSION}"
                        ),
                    });
                }

                let st = state.read().await;
                Some(WireMessage::Welcome {
                    federation_root: st.federation_root,
                    member_count: st.member_count,
                    node_id: config.node_id,
                    node_name: config.name.clone(),
                })
            }

            WireMessage::PresentToken {
                proof,
                request,
                federation_root,
            } => {
                let st = state.read().await;

                // Check federation root freshness
                if federation_root != st.federation_root {
                    event_log.lock().await.push(ServerEvent::TokenPresented {
                        proof_size: proof.len(),
                        accepted: false,
                        remote: remote_addr,
                    });
                    return Some(WireMessage::PresentationResult {
                        accepted: false,
                        reason: Some("stale federation root".to_string()),
                        request_digest: request.digest(),
                    });
                }

                // Verify the proof using the injected verifier, binding to the request.
                // The proof must be cryptographically bound to this specific request
                // to prevent replay attacks across different authorization requests.
                let req_digest = request.digest();
                let accepted = match config.verifier.verify(&proof, &req_digest) {
                    Ok(result) => result,
                    Err(_reason) => false, // parse/verification error -> reject
                };

                event_log.lock().await.push(ServerEvent::TokenPresented {
                    proof_size: proof.len(),
                    accepted,
                    remote: remote_addr,
                });

                Some(WireMessage::PresentationResult {
                    accepted,
                    reason: if accepted {
                        None
                    } else {
                        Some("proof verification failed".to_string())
                    },
                    request_digest: request.digest(),
                })
            }

            WireMessage::RequestAttestedRoot => {
                let st = state.read().await;
                Some(WireMessage::AttestedRoot {
                    root: st.federation_root,
                    height: st.height,
                    timestamp: current_timestamp(),
                    signatures: st.root_signatures.clone(),
                    threshold_qc: None,
                })
            }

            WireMessage::SubmitRevocation {
                token_id,
                authority,
                authority_sig,
            } => {
                // Verify the authority's signature over the token_id before
                // accepting the revocation. Without this, any peer could forge
                // a revocation for an arbitrary token.
                if !authority.verify(token_id.as_bytes(), &authority_sig) {
                    return Some(WireMessage::Error {
                        code: crate::message::error_codes::INVALID_SIGNATURE,
                        message: "authority signature verification failed".to_string(),
                    });
                }

                // If a revocation handler is configured, delegate to it and use
                // its root as the canonical source of truth.
                if let Some(handler) = revocation_handler {
                    let _accepted = handler.submit_revocation(&token_id, &authority_sig.0);

                    // Update local state using the handler's root (no independent
                    // hash-chain computation — the handler IS the authority).
                    let mut st = state.write().await;
                    st.apply_revocation_delegated(
                        &token_id,
                        &authority,
                        &authority_sig,
                        handler,
                    );

                    event_log
                        .lock()
                        .await
                        .push(ServerEvent::RevocationSubmitted {
                            token_id,
                            new_height: st.height,
                            remote: remote_addr,
                        });

                    Some(WireMessage::RevocationAck {
                        new_root: st.federation_root,
                        height: st.height,
                    })
                } else {
                    // Fallback: use the standalone BLAKE3 hash-chain logic.
                    // This is NOT consistent with the federation's Merkle tree
                    // but preserved for single-node/test deployments.
                    let mut st = state.write().await;
                    #[allow(deprecated)]
                    st.apply_revocation_standalone(&token_id, &authority, &authority_sig);

                    event_log
                        .lock()
                        .await
                        .push(ServerEvent::RevocationSubmitted {
                            token_id,
                            new_height: st.height,
                            remote: remote_addr,
                        });

                    Some(WireMessage::RevocationAck {
                        new_root: st.federation_root,
                        height: st.height,
                    })
                }
            }

            WireMessage::RequestNonMembership { token_id } => {
                let st = state.read().await;
                let is_revoked = st.is_revoked(&token_id);

                event_log
                    .lock()
                    .await
                    .push(ServerEvent::NonMembershipRequested {
                        token_id: token_id.clone(),
                        found: !is_revoked,
                        remote: remote_addr,
                    });

                if is_revoked {
                    Some(WireMessage::NonMembershipResponse {
                        token_id,
                        proof: None,
                        root: st.federation_root,
                        height: st.height,
                    })
                } else {
                    // Attempt to produce a non-membership proof.
                    // Returns None if this node lacks a real revocation tree.
                    let proof = generate_non_membership_proof(&token_id, &st.federation_root);
                    Some(WireMessage::NonMembershipResponse {
                        token_id,
                        proof,
                        root: st.federation_root,
                        height: st.height,
                    })
                }
            }

            WireMessage::Ping { seq, .. } => Some(WireMessage::Pong {
                seq,
                timestamp: current_timestamp(),
            }),

            WireMessage::Pong { .. } => None, // No response needed

            WireMessage::Welcome { .. } | WireMessage::PresentationResult { .. } => {
                // These are responses, not requests; no action needed
                None
            }

            WireMessage::AttestedRoot { .. } | WireMessage::RevocationAck { .. } => None,

            WireMessage::NonMembershipResponse { .. } => None,

            WireMessage::Error { .. } => None,
        }
    }

    /// Verify a proof using the provided verifier. Exposed for testing.
    ///
    /// Uses an all-zeros request digest (suitable for testing verifiers that
    /// don't check action binding, like `NoopVerifier` or `MinSizeVerifier`).
    pub fn verify_proof_with(proof: &[u8], verifier: &dyn ProofVerifier) -> bool {
        let dummy_digest = [0u8; 32];
        match verifier.verify(proof, &dummy_digest) {
            Ok(result) => result,
            Err(_) => false,
        }
    }

    /// Present a token to a remote peer.
    ///
    /// This is the client-side operation: connect to a peer silo, perform
    /// the handshake, and present a token for authorization.
    pub async fn present_token(
        &self,
        peer_addr: &str,
        proof: &[u8],
        request: &AuthorizationRequest,
    ) -> Result<bool, ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        // Perform handshake
        let hello = WireMessage::Hello {
            node_id: self.config.node_id,
            node_name: self.config.name.clone(),
            protocol_version: PROTOCOL_VERSION,
            capabilities: self.config.capabilities.clone(),
        };
        conn.send(hello).await?;
        let _welcome = conn.recv().await?;

        // Get the current federation root from state
        let federation_root = self.state.read().await.federation_root;

        // Present the token
        let present = WireMessage::PresentToken {
            proof: proof.to_vec(),
            request: request.clone(),
            federation_root,
        };
        conn.send(present).await?;

        // Wait for result
        match conn.recv().await? {
            WireMessage::PresentationResult { accepted, .. } => Ok(accepted),
            WireMessage::Error { message, .. } => {
                Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                    std::io::Error::new(std::io::ErrorKind::Other, message),
                )))
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Submit a revocation to a remote peer.
    pub async fn submit_revocation(
        &self,
        peer_addr: &str,
        token_id: &str,
        authority: &PublicKey,
        authority_sig: &Signature,
    ) -> Result<([u8; 32], u64), ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: *authority,
            authority_sig: *authority_sig,
        };
        conn.send(msg).await?;

        match conn.recv().await? {
            WireMessage::RevocationAck { new_root, height } => Ok((new_root, height)),
            WireMessage::Error { message, .. } => {
                Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                    std::io::Error::new(std::io::ErrorKind::Other, message),
                )))
            }
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Request the attested root from a remote peer.
    pub async fn request_attested_root(
        &self,
        peer_addr: &str,
    ) -> Result<([u8; 32], u64, i64), ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        conn.send(WireMessage::RequestAttestedRoot).await?;

        match conn.recv().await? {
            WireMessage::AttestedRoot {
                root,
                height,
                timestamp,
                ..
            } => Ok((root, height, timestamp)),
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Request a non-membership proof from a remote peer.
    pub async fn request_non_membership(
        &self,
        peer_addr: &str,
        token_id: &str,
    ) -> Result<Option<Vec<u8>>, ConnectionError> {
        let mut conn = PeerConnection::connect(peer_addr).await?;

        conn.send(WireMessage::RequestNonMembership {
            token_id: token_id.to_string(),
        })
        .await?;

        match conn.recv().await? {
            WireMessage::NonMembershipResponse { proof, .. } => Ok(proof),
            _ => Err(ConnectionError::Codec(crate::codec::CodecError::Io(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "unexpected response"),
            ))),
        }
    }

    /// Update the silo's federation root (e.g., after syncing with peers).
    pub async fn set_federation_root(&self, root: [u8; 32], height: u64) {
        let mut st = self.state.write().await;
        st.federation_root = root;
        st.height = height;
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Get the current Unix timestamp.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Attempt to generate a non-membership proof for the given token.
///
/// Returns `None` because the wire crate does not maintain a real revocation
/// Merkle tree. Callers that need real non-membership proofs must integrate
/// with the `pyana-commit` crate's revocation tree and provide proof data
/// via an injected `NonMembershipProofProvider` or similar mechanism.
///
/// Returning `None` signals to the requester: "this node cannot produce
/// cryptographic proof of non-membership; consult another source."
fn generate_non_membership_proof(_token_id: &str, _root: &[u8; 32]) -> Option<Vec<u8>> {
    // We explicitly do NOT fabricate fake Merkle proofs. A real implementation
    // would query the revocation tree (from pyana-commit) and produce a genuine
    // Merkle non-membership path. Until that integration exists, we honestly
    // report that no proof is available.
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn server_accepts_hello() {
        let config = SiloConfig::new("test-silo").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        client
            .send(WireMessage::Hello {
                node_id: [0x11; 32],
                node_name: "client".to_string(),
                protocol_version: PROTOCOL_VERSION,
                capabilities: vec![],
            })
            .await
            .unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::Welcome {
                member_count,
                node_name,
                ..
            } => {
                assert!(member_count > 0);
                assert_eq!(node_name, "test-silo");
            }
            other => panic!("expected Welcome, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn server_handles_presentation() {
        let config =
            SiloConfig::new("verifier").with_verifier(Arc::new(MinSizeVerifier { min_bytes: 100 }));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let state = Arc::clone(&server.state);

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let federation_root = state.read().await.federation_root;

        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Present with a proof that's large enough
        let request = AuthorizationRequest::new("resource", "read", "alice");
        let msg = WireMessage::PresentToken {
            proof: vec![0xab; 200],
            request: request.clone(),
            federation_root,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::PresentationResult { accepted, .. } => {
                assert!(accepted, "proof of 200 bytes should pass min-100 check");
            }
            other => panic!("expected PresentationResult, got {other:?}"),
        }

        // Present with a proof that's too small
        let msg = WireMessage::PresentToken {
            proof: vec![0xab; 50],
            request,
            federation_root,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::PresentationResult {
                accepted, reason, ..
            } => {
                assert!(!accepted);
                assert!(reason.is_some());
            }
            other => panic!("expected PresentationResult, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn server_handles_revocation() {
        let config = SiloConfig::new("revoker").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();
        let state = Arc::clone(&server.state);

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Generate a real keypair so the signature verifies.
        let (sk, pk) = pyana_types::generate_keypair();
        let token_id = "tok-revoke-me";
        let sig = pyana_types::sign(&sk, token_id.as_bytes());

        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: pk,
            authority_sig: sig,
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::RevocationAck { height, .. } => {
                assert_eq!(height, 1);
            }
            other => panic!("expected RevocationAck, got {other:?}"),
        }

        // Verify the token is now revoked in state
        let st = state.read().await;
        assert!(st.is_revoked("tok-revoke-me"));
        assert!(!st.is_revoked("tok-other"));
    }

    #[tokio::test]
    async fn server_rejects_revocation_with_invalid_signature() {
        let config = SiloConfig::new("revoker").with_verifier(Arc::new(NoopVerifier));
        let server = SiloServer::new("127.0.0.1:0".parse().unwrap(), config);

        let (addr_tx, addr_rx) = tokio::sync::oneshot::channel();

        tokio::spawn(async move {
            server.run_with_addr(addr_tx).await.unwrap();
        });

        let addr = addr_rx.await.unwrap();
        let mut client = PeerConnection::connect(&addr.to_string()).await.unwrap();

        // Use a forged signature (random bytes) with a random public key.
        let msg = WireMessage::SubmitRevocation {
            token_id: "tok-forged".to_string(),
            authority: PublicKey([0xdd; 32]),
            authority_sig: Signature([0xcc; 64]),
        };
        client.send(msg).await.unwrap();

        let response = client.recv().await.unwrap();
        match response {
            WireMessage::Error { code, message } => {
                assert_eq!(code, crate::message::error_codes::INVALID_SIGNATURE);
                assert!(message.contains("signature"));
            }
            other => panic!("expected Error, got {other:?}"),
        }
    }

    #[test]
    fn silo_state_genesis() {
        let state = SiloState::genesis(5);
        assert_eq!(state.height, 0);
        assert_eq!(state.member_count, 5);
        assert!(state.revoked_tokens.is_empty());
    }

    #[test]
    fn silo_state_revocation() {
        let mut state = SiloState::genesis(5);
        let original_root = state.federation_root;

        state.apply_revocation("tok-1", &PublicKey([0xaa; 32]), &Signature([0xaa; 64]));
        assert_eq!(state.height, 1);
        assert!(state.is_revoked("tok-1"));
        assert!(!state.is_revoked("tok-2"));
        assert_ne!(state.federation_root, original_root);

        let root_after_first = state.federation_root;
        state.apply_revocation("tok-2", &PublicKey([0xbb; 32]), &Signature([0xbb; 64]));
        assert_eq!(state.height, 2);
        assert!(state.is_revoked("tok-2"));
        assert_ne!(state.federation_root, root_after_first);
    }

    #[test]
    fn verification_modes() {
        let proof_small = vec![0u8; 50];
        let proof_big = vec![0u8; 200];

        assert!(SiloServer::verify_proof_with(&proof_small, &NoopVerifier));
        assert!(!SiloServer::verify_proof_with(
            &proof_small,
            &RejectAllVerifier
        ));
        assert!(!SiloServer::verify_proof_with(
            &proof_small,
            &MinSizeVerifier { min_bytes: 100 }
        ));
        assert!(SiloServer::verify_proof_with(
            &proof_big,
            &MinSizeVerifier { min_bytes: 100 }
        ));
    }

    #[test]
    fn stark_verifier_rejects_garbage() {
        let garbage = vec![0u8; 100];
        let verifier = StarkVerifier;
        // Random bytes should not pass STARK verification
        assert!(!SiloServer::verify_proof_with(&garbage, &verifier));
    }
}
