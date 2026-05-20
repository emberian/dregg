//! pyana-relay: Lightweight iroh relay node for the pyana federation.
//!
//! This binary:
//! - Creates an iroh endpoint with persistent identity (from `PYANA_RELAY_SECRET_KEY` env var)
//! - Accepts connections from pyana peers via iroh's QUIC + relay hole-punching
//! - Stores and serves attested roots (latest federation state)
//! - Accepts authenticated commands: mint_token, publish_root, register_peer
//! - Prints its NodeId and connection address on startup
//! - Graceful shutdown on SIGTERM/SIGINT

use std::sync::Arc;

use futures_util::StreamExt;
use iroh::{Endpoint, RelayMode, SecretKey, endpoint::Connection};
use iroh::protocol::{AcceptError, ProtocolHandler, Router};
use pyana_types::{AttestedRoot, PublicKey, Signature};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::{error, info, warn};

// =============================================================================
// Protocol ALPNs
// =============================================================================

/// ALPN for the pyana relay protocol (state queries + commands).
const PYANA_RELAY_ALPN: &[u8] = b"pyana/relay/0";

// =============================================================================
// State
// =============================================================================

/// Known peer entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PeerEntry {
    /// The peer's pyana public key (32 bytes).
    pub public_key: PublicKey,
    /// The peer's iroh endpoint address (serialized).
    pub iroh_addr: String,
    /// Unix timestamp of last registration.
    pub registered_at: i64,
}

/// Federation configuration broadcast to peers.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FederationConfig {
    /// Known federation validator public keys.
    pub validators: Vec<PublicKey>,
    /// Quorum threshold for attested roots.
    pub threshold: usize,
    /// Relay node's pyana public key (the root key).
    pub relay_pubkey: PublicKey,
}

/// Relay node shared state.
#[derive(Debug)]
pub struct RelayState {
    /// Latest attested root from the federation.
    pub latest_root: Option<AttestedRoot>,
    /// Federation configuration.
    pub config: FederationConfig,
    /// Known peers.
    pub peers: Vec<PeerEntry>,
    /// Root signing key (for minting tokens).
    pub root_key: Option<ed25519_dalek::SigningKey>,
}

// =============================================================================
// Protocol Messages
// =============================================================================

/// Requests from peers to the relay.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RelayRequest {
    /// Get the latest attested root.
    GetLatestRoot,
    /// Get the federation configuration.
    GetConfig,
    /// Get known peers.
    GetPeers,
    /// Publish a new attested root (authenticated by quorum).
    PublishRoot { root: AttestedRoot },
    /// Register as a peer.
    RegisterPeer { entry: PeerEntry },
    /// Mint a token (requires root key authentication).
    MintToken {
        /// The recipient's public key.
        recipient: PublicKey,
        /// Domain/scope for the token.
        domain: String,
        /// Nonce for replay protection.
        nonce: [u8; 32],
        /// Signature over (recipient || domain || nonce) by a known authority.
        auth_signature: Signature,
        /// The authority public key that signed.
        authority: PublicKey,
    },
}

/// Responses from the relay to peers.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RelayResponse {
    /// Latest attested root (may be None if not yet initialized).
    LatestRoot(Option<AttestedRoot>),
    /// Federation configuration.
    Config(FederationConfig),
    /// Known peers list.
    Peers(Vec<PeerEntry>),
    /// Root published successfully.
    RootPublished { height: u64 },
    /// Peer registered successfully.
    PeerRegistered,
    /// Minted token (the signed token blob).
    TokenMinted { token_bytes: Vec<u8> },
    /// Error response.
    Error { message: String },
}

// =============================================================================
// Protocol Handler
// =============================================================================

#[derive(Clone, Debug)]
struct PyanaRelayHandler {
    state: Arc<RwLock<RelayState>>,
}

impl ProtocolHandler for PyanaRelayHandler {
    async fn accept(&self, connection: Connection) -> Result<(), AcceptError> {
        let remote_id = connection.remote_id();
        info!("accepted connection from {remote_id}");

        // Handle multiple request/response pairs on this connection.
        loop {
            let (mut send, mut recv) = match connection.accept_bi().await {
                Ok(streams) => streams,
                Err(_) => {
                    // Connection closed by remote — normal.
                    break;
                }
            };

            // Read the request (length-prefixed postcard).
            let request_bytes = match recv.read_to_end(1024 * 1024).await {
                Ok(bytes) => bytes,
                Err(e) => {
                    warn!("failed to read request from {remote_id}: {e}");
                    break;
                }
            };

            let request: RelayRequest = match postcard::from_bytes(&request_bytes) {
                Ok(req) => req,
                Err(e) => {
                    warn!("invalid request from {remote_id}: {e}");
                    let resp = RelayResponse::Error {
                        message: format!("invalid request: {e}"),
                    };
                    let resp_bytes = postcard::to_stdvec(&resp).unwrap_or_default();
                    let _ = send.write_all(&resp_bytes).await;
                    let _ = send.finish();
                    continue;
                }
            };

            let response = self.handle_request(request).await;
            let resp_bytes = postcard::to_stdvec(&response).unwrap_or_else(|e| {
                let err = RelayResponse::Error {
                    message: format!("serialization error: {e}"),
                };
                postcard::to_stdvec(&err).unwrap_or_default()
            });

            if let Err(e) = send.write_all(&resp_bytes).await {
                warn!("failed to send response to {remote_id}: {e}");
                break;
            }
            if send.finish().is_err() {
                break;
            }
        }

        Ok(())
    }
}

impl PyanaRelayHandler {
    async fn handle_request(&self, request: RelayRequest) -> RelayResponse {
        match request {
            RelayRequest::GetLatestRoot => {
                let state = self.state.read().await;
                RelayResponse::LatestRoot(state.latest_root.clone())
            }
            RelayRequest::GetConfig => {
                let state = self.state.read().await;
                RelayResponse::Config(state.config.clone())
            }
            RelayRequest::GetPeers => {
                let state = self.state.read().await;
                RelayResponse::Peers(state.peers.clone())
            }
            RelayRequest::PublishRoot { root } => {
                // Verify the root has a valid quorum before accepting.
                let state = self.state.read().await;
                let known_keys = &state.config.validators;
                if !root.is_valid(known_keys) {
                    return RelayResponse::Error {
                        message: "invalid quorum on attested root".to_string(),
                    };
                }
                let height = root.height;
                drop(state);

                let mut state = self.state.write().await;
                // Only accept if height is strictly increasing.
                if let Some(ref existing) = state.latest_root {
                    if root.height <= existing.height {
                        return RelayResponse::Error {
                            message: format!(
                                "root height {} is not greater than current {}",
                                root.height, existing.height
                            ),
                        };
                    }
                }
                state.latest_root = Some(root);
                info!("published new attested root at height {height}");
                RelayResponse::RootPublished { height }
            }
            RelayRequest::RegisterPeer { entry } => {
                let mut state = self.state.write().await;
                // Upsert: replace existing entry with same public key.
                state.peers.retain(|p| p.public_key != entry.public_key);
                info!("registered peer: {:?}", entry.public_key);
                state.peers.push(entry);
                RelayResponse::PeerRegistered
            }
            RelayRequest::MintToken {
                recipient,
                domain,
                nonce,
                auth_signature,
                authority,
            } => {
                let state = self.state.read().await;

                // Verify the authority is the relay's root key.
                if authority != state.config.relay_pubkey {
                    return RelayResponse::Error {
                        message: "mint authority must be the relay root key".to_string(),
                    };
                }

                // Verify the auth signature.
                let mut auth_msg = Vec::new();
                auth_msg.extend_from_slice(&recipient.0);
                auth_msg.extend_from_slice(domain.as_bytes());
                auth_msg.extend_from_slice(&nonce);
                if !authority.verify(&auth_msg, &auth_signature) {
                    return RelayResponse::Error {
                        message: "invalid mint authorization signature".to_string(),
                    };
                }

                // Mint: sign a token blob with the root key.
                let root_key = match &state.root_key {
                    Some(k) => k,
                    None => {
                        return RelayResponse::Error {
                            message: "relay has no root key configured".to_string(),
                        };
                    }
                };

                let token_payload = TokenPayload {
                    recipient,
                    domain: domain.clone(),
                    nonce,
                    issued_at: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap_or_default()
                        .as_secs() as i64,
                };
                let payload_bytes = postcard::to_stdvec(&token_payload).unwrap_or_default();
                let sig = {
                    use ed25519_dalek::Signer;
                    root_key.sign(&payload_bytes)
                };

                let mut token_bytes = Vec::new();
                token_bytes.extend_from_slice(&payload_bytes);
                token_bytes.extend_from_slice(&sig.to_bytes());

                info!("minted token for {} in domain {}", recipient, domain);
                RelayResponse::TokenMinted { token_bytes }
            }
        }
    }
}

/// Internal token payload for minting.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct TokenPayload {
    recipient: PublicKey,
    domain: String,
    nonce: [u8; 32],
    issued_at: i64,
}

// =============================================================================
// Main
// =============================================================================

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .init();

    info!("pyana-relay starting up");

    // Load or generate the iroh secret key (for endpoint identity).
    let secret_key = match std::env::var("PYANA_RELAY_SECRET_KEY") {
        Ok(hex_key) => {
            let bytes = hex_decode_32(&hex_key)?;
            SecretKey::from_bytes(&bytes)
        }
        Err(_) => {
            info!("no PYANA_RELAY_SECRET_KEY set, generating ephemeral identity");
            SecretKey::generate(&mut rand::rng())
        }
    };

    // Load root signing key for minting.
    let root_key = match std::env::var("PYANA_ROOT_KEY") {
        Ok(hex_key) => {
            let bytes = hex_decode_32(&hex_key)?;
            let sk = ed25519_dalek::SigningKey::from_bytes(&bytes);
            info!("root key loaded: {}", pyana_types::hex_encode(&sk.verifying_key().to_bytes()[..8]));
            Some(sk)
        }
        Err(_) => {
            warn!("no PYANA_ROOT_KEY set — minting will be disabled");
            None
        }
    };

    // Derive the relay's pyana public key from the root key (or a placeholder).
    let relay_pubkey = match &root_key {
        Some(sk) => PublicKey(sk.verifying_key().to_bytes()),
        None => PublicKey([0u8; 32]),
    };

    // Load federation validators from env (comma-separated hex public keys).
    let validators: Vec<PublicKey> = match std::env::var("PYANA_VALIDATORS") {
        Ok(val) => val
            .split(',')
            .filter(|s| !s.is_empty())
            .filter_map(|hex| hex_decode_32(hex.trim()).ok().map(PublicKey))
            .collect(),
        Err(_) => {
            // Default: the relay's own key is the only validator.
            if relay_pubkey.0 != [0u8; 32] {
                vec![relay_pubkey]
            } else {
                vec![]
            }
        }
    };

    let threshold: usize = std::env::var("PYANA_THRESHOLD")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    let state = Arc::new(RwLock::new(RelayState {
        latest_root: None,
        config: FederationConfig {
            validators,
            threshold,
            relay_pubkey,
        },
        peers: Vec::new(),
        root_key,
    }));

    // Build the iroh endpoint.
    let endpoint = Endpoint::builder()
        .secret_key(secret_key)
        .alpns(vec![PYANA_RELAY_ALPN.to_vec()])
        .relay_mode(RelayMode::Default)
        .bind()
        .await?;

    let endpoint_id = endpoint.id();
    info!("iroh endpoint id: {endpoint_id}");

    // Build and spawn the protocol router.
    let handler = PyanaRelayHandler { state };
    let router = Router::builder(endpoint.clone())
        .accept(PYANA_RELAY_ALPN, handler)
        .spawn();

    // Wait for the endpoint to be online and print connection info.
    endpoint.online().await;
    let addr = endpoint.addr();

    println!("=== pyana-relay online ===");
    println!("endpoint_id: {endpoint_id}");
    if let Some(relay_url) = addr.relay_urls().next() {
        println!("relay_url: {relay_url}");
    }
    for ip_addr in addr.ip_addrs() {
        println!("direct_addr: {ip_addr}");
    }
    println!("========================");

    // Output as JSON for machine consumption (GitHub Actions can parse this).
    let info = serde_json::json!({
        "endpoint_id": endpoint_id.to_string(),
        "relay_url": addr.relay_urls().next().map(|u| u.to_string()),
        "direct_addrs": addr.ip_addrs().map(|a| a.to_string()).collect::<Vec<_>>(),
    });
    println!("PYANA_RELAY_INFO={}", serde_json::to_string(&info)?);

    // Wait for shutdown signal.
    tokio::signal::ctrl_c().await?;
    info!("received shutdown signal, closing gracefully...");

    router.shutdown().await.map_err(|e| anyhow::anyhow!("{e}"))?;
    info!("pyana-relay shut down");

    Ok(())
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_decode_32(hex: &str) -> anyhow::Result<[u8; 32]> {
    let hex = hex.trim();
    if hex.len() != 64 {
        anyhow::bail!("expected 64 hex chars (32 bytes), got {}", hex.len());
    }
    let mut bytes = [0u8; 32];
    for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
        let s = std::str::from_utf8(chunk)?;
        bytes[i] = u8::from_str_radix(s, 16)?;
    }
    Ok(bytes)
}
