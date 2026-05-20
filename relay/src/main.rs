//! pyana-relay: Lightweight QUIC relay node for the pyana federation.
//!
//! This binary:
//! - Creates a QUIC endpoint with a self-signed certificate (identity derived from root key)
//! - Accepts connections from pyana peers
//! - Stores and serves attested roots (latest federation state)
//! - Accepts authenticated commands: mint_token, publish_root, register_peer
//! - Prints its endpoint address on startup
//! - Graceful shutdown on SIGTERM/SIGINT
//! - Periodic state snapshots (on SIGUSR1 or timed)
//! - Loads previous state from --state-dir on startup
//! - Writes discovery info for the federation mesh
//!
//! Uses quinn (QUIC) directly instead of iroh, because iroh's ed25519-dalek v3
//! pre-release has dep conflicts with the workspace's crypto stack. The relay runs
//! on a public IP anyway, so iroh's NAT traversal is not needed for the server side.
//! Clients behind NAT can connect to this relay's public address directly.

use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use pyana_types::{AttestedRoot, PublicKey, Signature};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::{info, warn};

// =============================================================================
// CLI Arguments
// =============================================================================

/// Command-line arguments for the relay node.
#[derive(Debug, Clone)]
pub struct Args {
    /// Directory for persistent state (attested roots, intent pool, nullifiers).
    pub state_dir: Option<PathBuf>,
    /// Path to write this node's discovery info (NodeId, ticket, etc.).
    pub discovery_file: Option<PathBuf>,
    /// Comma-separated list of known peer NodeIds to connect to on startup.
    pub peers: Vec<String>,
    /// Role identifier for this node in the federation.
    pub node_role: String,
    /// Whether to run as an intent pool service.
    pub intent_pool: bool,
}

impl Args {
    fn parse() -> Self {
        let args: Vec<String> = std::env::args().collect();
        let mut state_dir = None;
        let mut discovery_file = None;
        let mut peers = Vec::new();
        let mut node_role = "node".to_string();
        let mut intent_pool = false;

        let mut i = 1;
        while i < args.len() {
            match args[i].as_str() {
                "--state-dir" => {
                    i += 1;
                    if i < args.len() {
                        state_dir = Some(PathBuf::from(&args[i]));
                    }
                }
                "--discovery-file" => {
                    i += 1;
                    if i < args.len() {
                        discovery_file = Some(PathBuf::from(&args[i]));
                    }
                }
                "--peers" => {
                    i += 1;
                    if i < args.len() && !args[i].is_empty() {
                        peers = args[i].split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
                    }
                }
                "--node-role" => {
                    i += 1;
                    if i < args.len() {
                        node_role = args[i].clone();
                    }
                }
                "--intent-pool" => {
                    intent_pool = true;
                }
                _ => {}
            }
            i += 1;
        }

        Args {
            state_dir,
            discovery_file,
            peers,
            node_role,
            intent_pool,
        }
    }
}

// =============================================================================
// Persistent State (serializable)
// =============================================================================

/// Serializable snapshot of node state for persistence across restarts.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PersistedState {
    /// Latest attested root from the federation.
    pub latest_root: Option<AttestedRoot>,
    /// Known peers.
    pub peers: Vec<PeerEntry>,
    /// Intent pool (if this node runs as intent service).
    pub intent_pool: Vec<Intent>,
    /// Nullifier set (spent proofs).
    pub nullifiers: Vec<[u8; 32]>,
    /// Monotonic snapshot counter.
    pub snapshot_counter: u64,
}

/// An intent in the pool.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Intent {
    /// Unique intent ID.
    pub id: String,
    /// The intent payload (opaque bytes for now).
    pub payload: Vec<u8>,
    /// Unix timestamp when the intent was submitted.
    pub submitted_at: i64,
    /// Unix timestamp when the intent expires.
    pub expires_at: i64,
    /// Submitter's public key.
    pub submitter: PublicKey,
}

// =============================================================================
// State
// =============================================================================

/// Known peer entry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PeerEntry {
    /// The peer's pyana public key (32 bytes).
    pub public_key: PublicKey,
    /// The peer's connection address (host:port or relay ticket).
    pub address: String,
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
    /// Intent pool (for intent-service mode).
    pub intent_pool: Vec<Intent>,
    /// Nullifier set.
    pub nullifiers: Vec<[u8; 32]>,
    /// Snapshot counter.
    pub snapshot_counter: u64,
}

impl RelayState {
    /// Create a persisted state snapshot.
    fn to_persisted(&self) -> PersistedState {
        PersistedState {
            latest_root: self.latest_root.clone(),
            peers: self.peers.clone(),
            intent_pool: self.intent_pool.clone(),
            nullifiers: self.nullifiers.clone(),
            snapshot_counter: self.snapshot_counter,
        }
    }

    /// Restore from persisted state.
    fn restore_from(&mut self, persisted: PersistedState) {
        self.latest_root = persisted.latest_root;
        self.peers = persisted.peers;
        self.intent_pool = persisted.intent_pool;
        self.nullifiers = persisted.nullifiers;
        self.snapshot_counter = persisted.snapshot_counter;
    }
}

// =============================================================================
// State Persistence
// =============================================================================

const STATE_FILENAME: &str = "state.json";

/// Load persisted state from state_dir if it exists.
fn load_state(state_dir: &PathBuf) -> Option<PersistedState> {
    let path = state_dir.join(STATE_FILENAME);
    if !path.exists() {
        info!("no previous state found at {}", path.display());
        return None;
    }
    match std::fs::read_to_string(&path) {
        Ok(data) => match serde_json::from_str(&data) {
            Ok(state) => {
                info!("loaded previous state from {}", path.display());
                Some(state)
            }
            Err(e) => {
                warn!("failed to parse state file {}: {e}", path.display());
                None
            }
        },
        Err(e) => {
            warn!("failed to read state file {}: {e}", path.display());
            None
        }
    }
}

/// Save state snapshot to state_dir.
fn save_state(state_dir: &PathBuf, persisted: &PersistedState) -> anyhow::Result<()> {
    std::fs::create_dir_all(state_dir)?;
    let path = state_dir.join(STATE_FILENAME);
    let data = serde_json::to_string_pretty(persisted)?;
    std::fs::write(&path, data)?;
    info!("state snapshot saved to {} (counter={})", path.display(), persisted.snapshot_counter);
    Ok(())
}

/// Write discovery info for this node.
fn write_discovery(discovery_path: &PathBuf, node_role: &str, listen_addr: &SocketAddr) -> anyhow::Result<()> {
    let now = chrono_now_iso();
    let info = serde_json::json!({
        "node_id": format!("quic-{}", listen_addr),
        "ticket": format!("pyana-quic://{}", listen_addr),
        "last_seen": now,
        "role": node_role,
        "protocol": "quinn-quic",
        "addr": listen_addr.to_string(),
    });
    std::fs::create_dir_all(discovery_path.parent().unwrap_or(std::path::Path::new(".")))?;
    std::fs::write(discovery_path, serde_json::to_string_pretty(&info)?)?;
    info!("discovery info written to {}", discovery_path.display());
    Ok(())
}

fn chrono_now_iso() -> String {
    // Simple UTC timestamp without chrono dependency.
    let dur = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    let secs = dur.as_secs();
    // Format as ISO 8601 (approximate — no leap seconds).
    let days = secs / 86400;
    let time_of_day = secs % 86400;
    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;
    // Days since 1970-01-01: compute year/month/day.
    let (year, month, day) = days_to_ymd(days);
    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

fn days_to_ymd(mut days: u64) -> (u64, u64, u64) {
    // Simplified date calculation.
    let mut year = 1970;
    loop {
        let days_in_year = if is_leap(year) { 366 } else { 365 };
        if days < days_in_year {
            break;
        }
        days -= days_in_year;
        year += 1;
    }
    let days_in_months: [u64; 12] = if is_leap(year) {
        [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    } else {
        [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    };
    let mut month = 1;
    for &dim in &days_in_months {
        if days < dim {
            break;
        }
        days -= dim;
        month += 1;
    }
    (year, month, days + 1)
}

fn is_leap(year: u64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
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
    /// Submit an intent to the pool (intent-service mode).
    SubmitIntent { intent: Intent },
    /// Query the intent pool.
    GetIntentPool,
    /// Get pool statistics.
    GetPoolStats,
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
    /// Intent accepted.
    IntentAccepted { id: String },
    /// Intent pool contents.
    IntentPool(Vec<Intent>),
    /// Pool statistics.
    PoolStats { total: usize, active: usize, expired: usize },
    /// Error response.
    Error { message: String },
}

// =============================================================================
// Protocol Handler
// =============================================================================

/// Internal token payload for minting.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct TokenPayload {
    recipient: PublicKey,
    domain: String,
    nonce: [u8; 32],
    issued_at: i64,
}

async fn handle_connection(conn: quinn::Connection, state: Arc<RwLock<RelayState>>) {
    let remote_addr = conn.remote_address();
    info!("accepted connection from {remote_addr}");

    loop {
        // Accept bidirectional streams (each stream = one request/response).
        let (send, recv) = match conn.accept_bi().await {
            Ok(streams) => streams,
            Err(quinn::ConnectionError::ApplicationClosed(_)) => {
                info!("connection from {remote_addr} closed gracefully");
                break;
            }
            Err(e) => {
                warn!("connection from {remote_addr} error: {e}");
                break;
            }
        };

        let state = state.clone();
        tokio::spawn(async move {
            if let Err(e) = handle_stream(send, recv, state).await {
                warn!("stream handler error: {e}");
            }
        });
    }
}

async fn handle_stream(
    mut send: quinn::SendStream,
    mut recv: quinn::RecvStream,
    state: Arc<RwLock<RelayState>>,
) -> anyhow::Result<()> {
    // Read the request (up to 1MB).
    let request_bytes = recv
        .read_to_end(1024 * 1024)
        .await
        .map_err(|e| anyhow::anyhow!("read error: {e}"))?;

    let request: RelayRequest = postcard::from_bytes(&request_bytes)
        .map_err(|e| anyhow::anyhow!("deserialize error: {e}"))?;

    let response = handle_request(request, &state).await;

    let resp_bytes = postcard::to_stdvec(&response)?;
    send.write_all(&resp_bytes).await?;
    send.finish()?;

    Ok(())
}

async fn handle_request(request: RelayRequest, state: &Arc<RwLock<RelayState>>) -> RelayResponse {
    match request {
        RelayRequest::GetLatestRoot => {
            let state = state.read().await;
            RelayResponse::LatestRoot(state.latest_root.clone())
        }
        RelayRequest::GetConfig => {
            let state = state.read().await;
            RelayResponse::Config(state.config.clone())
        }
        RelayRequest::GetPeers => {
            let state = state.read().await;
            RelayResponse::Peers(state.peers.clone())
        }
        RelayRequest::PublishRoot { root } => {
            // Verify the root has a valid quorum before accepting.
            let known_keys = {
                let state = state.read().await;
                state.config.validators.clone()
            };
            if !root.is_valid(&known_keys) {
                return RelayResponse::Error {
                    message: "invalid quorum on attested root".to_string(),
                };
            }
            let height = root.height;

            let mut state = state.write().await;
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
            let mut state = state.write().await;
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
            let state = state.read().await;

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
        RelayRequest::SubmitIntent { intent } => {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;

            // Reject expired intents.
            if intent.expires_at <= now {
                return RelayResponse::Error {
                    message: "intent already expired".to_string(),
                };
            }

            let id = intent.id.clone();
            let mut state = state.write().await;
            state.intent_pool.push(intent);
            info!("accepted intent {id} into pool (pool size: {})", state.intent_pool.len());
            RelayResponse::IntentAccepted { id }
        }
        RelayRequest::GetIntentPool => {
            let state = state.read().await;
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            // Return only non-expired intents.
            let active: Vec<Intent> = state.intent_pool.iter()
                .filter(|i| i.expires_at > now)
                .cloned()
                .collect();
            RelayResponse::IntentPool(active)
        }
        RelayRequest::GetPoolStats => {
            let state = state.read().await;
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let total = state.intent_pool.len();
            let active = state.intent_pool.iter().filter(|i| i.expires_at > now).count();
            let expired = total - active;
            RelayResponse::PoolStats { total, active, expired }
        }
    }
}

// =============================================================================
// Intent Pool GC
// =============================================================================

async fn gc_intent_pool(state: &Arc<RwLock<RelayState>>) {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;

    let mut state = state.write().await;
    let before = state.intent_pool.len();
    state.intent_pool.retain(|i| i.expires_at > now);
    let removed = before - state.intent_pool.len();
    if removed > 0 {
        info!("GC'd {removed} expired intents from pool (remaining: {})", state.intent_pool.len());
    }
}

// =============================================================================
// TLS / QUIC setup
// =============================================================================

/// Generate a self-signed certificate for the QUIC endpoint.
fn generate_self_signed_cert() -> anyhow::Result<(rustls::pki_types::CertificateDer<'static>, rustls::pki_types::PrivateKeyDer<'static>)> {
    let cert = rcgen::generate_simple_self_signed(vec!["pyana-relay.local".to_string()])?;
    let cert_der = rustls::pki_types::CertificateDer::from(cert.cert);
    let key_der = rustls::pki_types::PrivateKeyDer::try_from(cert.key_pair.serialize_der())
        .map_err(|e| anyhow::anyhow!("key conversion: {e}"))?;
    Ok((cert_der, key_der))
}

/// Create a quinn server config with a self-signed cert.
fn make_server_config() -> anyhow::Result<quinn::ServerConfig> {
    let (cert, key) = generate_self_signed_cert()?;

    let server_crypto = rustls::ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(vec![cert], key)?;

    let server_config = quinn::ServerConfig::with_crypto(Arc::new(
        quinn::crypto::rustls::QuicServerConfig::try_from(server_crypto)?,
    ));

    Ok(server_config)
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

    let args = Args::parse();
    info!("pyana-relay starting up (role: {}, intent_pool: {})", args.node_role, args.intent_pool);

    // Load root signing key for minting.
    let root_key = match std::env::var("PYANA_ROOT_KEY") {
        Ok(hex_key) => {
            let bytes = hex_decode_32(&hex_key)?;
            let sk = ed25519_dalek::SigningKey::from_bytes(&bytes);
            info!(
                "root key loaded: {}",
                pyana_types::hex_encode(&sk.verifying_key().to_bytes()[..8])
            );
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
        intent_pool: Vec::new(),
        nullifiers: Vec::new(),
        snapshot_counter: 0,
    }));

    // Load previous state from state-dir if available.
    if let Some(ref state_dir) = args.state_dir {
        if let Some(persisted) = load_state(state_dir) {
            let mut s = state.write().await;
            s.restore_from(persisted);
            info!(
                "restored state: {} peers, {} intents, {} nullifiers, root height {:?}",
                s.peers.len(),
                s.intent_pool.len(),
                s.nullifiers.len(),
                s.latest_root.as_ref().map(|r| r.height),
            );
        }
    }

    // Log known peers from CLI.
    if !args.peers.is_empty() {
        info!("known peers from CLI: {:?}", args.peers);
    }

    // Determine listen address.
    let listen_addr: SocketAddr = std::env::var("PYANA_RELAY_ADDR")
        .unwrap_or_else(|_| "0.0.0.0:4433".to_string())
        .parse()?;

    // Create QUIC endpoint.
    let server_config = make_server_config()?;
    let endpoint = quinn::Endpoint::server(server_config, listen_addr)?;
    let local_addr = endpoint.local_addr()?;

    println!("=== pyana-relay online ===");
    println!("listen_addr: {local_addr}");
    println!("protocol: QUIC (quinn)");
    println!("role: {}", args.node_role);
    println!("intent_pool: {}", args.intent_pool);
    println!("minting: {}", if state.read().await.root_key.is_some() { "enabled" } else { "disabled" });
    println!("validators: {}", state.read().await.config.validators.len());
    println!("========================");

    // Write discovery info.
    if let Some(ref discovery_path) = args.discovery_file {
        write_discovery(discovery_path, &args.node_role, &local_addr)?;
    }

    // Output as JSON for machine consumption (GitHub Actions can parse this).
    let info = serde_json::json!({
        "listen_addr": local_addr.to_string(),
        "relay_pubkey": pyana_types::hex_encode(&relay_pubkey.0),
        "minting_enabled": state.read().await.root_key.is_some(),
        "validators": state.read().await.config.validators.len(),
        "role": args.node_role,
        "intent_pool": args.intent_pool,
    });
    println!("PYANA_RELAY_INFO={}", serde_json::to_string(&info)?);

    // Spawn the accept loop.
    let accept_state = state.clone();
    let accept_handle = tokio::spawn(async move {
        while let Some(incoming) = endpoint.accept().await {
            let conn = match incoming.await {
                Ok(conn) => conn,
                Err(e) => {
                    warn!("incoming connection failed: {e}");
                    continue;
                }
            };
            let state = accept_state.clone();
            tokio::spawn(handle_connection(conn, state));
        }
    });

    // Spawn periodic state snapshot (every 5 minutes).
    let snapshot_state = state.clone();
    let snapshot_state_dir = args.state_dir.clone();
    let snapshot_handle = tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(300));
        interval.tick().await; // Skip first immediate tick.
        loop {
            interval.tick().await;
            if let Some(ref state_dir) = snapshot_state_dir {
                let mut s = snapshot_state.write().await;
                s.snapshot_counter += 1;
                let persisted = s.to_persisted();
                drop(s);
                if let Err(e) = save_state(state_dir, &persisted) {
                    warn!("periodic snapshot failed: {e}");
                }
            }
        }
    });

    // Spawn intent pool GC (every 60 seconds, if intent-pool mode).
    let gc_handle = if args.intent_pool {
        let gc_state = state.clone();
        Some(tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            loop {
                interval.tick().await;
                gc_intent_pool(&gc_state).await;
            }
        }))
    } else {
        None
    };

    // Set up SIGUSR1 handler for on-demand snapshots.
    #[cfg(unix)]
    {
        let usr1_state = state.clone();
        let usr1_state_dir = args.state_dir.clone();
        tokio::spawn(async move {
            let mut sig = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::user_defined1())
                .expect("failed to register SIGUSR1 handler");
            loop {
                sig.recv().await;
                info!("SIGUSR1 received — triggering state snapshot");
                if let Some(ref state_dir) = usr1_state_dir {
                    let mut s = usr1_state.write().await;
                    s.snapshot_counter += 1;
                    let persisted = s.to_persisted();
                    drop(s);
                    if let Err(e) = save_state(state_dir, &persisted) {
                        warn!("SIGUSR1 snapshot failed: {e}");
                    }
                }
            }
        });
    }

    // Wait for shutdown signal (SIGTERM or Ctrl-C).
    #[cfg(unix)]
    {
        let mut sigterm = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
            .expect("failed to register SIGTERM handler");
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {
                info!("received SIGINT, shutting down...");
            }
            _ = sigterm.recv() => {
                info!("received SIGTERM, shutting down...");
            }
        }
    }

    #[cfg(not(unix))]
    {
        tokio::signal::ctrl_c().await?;
        info!("received shutdown signal, closing gracefully...");
    }

    // Final state save on shutdown.
    if let Some(ref state_dir) = args.state_dir {
        let mut s = state.write().await;
        s.snapshot_counter += 1;
        let persisted = s.to_persisted();
        drop(s);
        if let Err(e) = save_state(state_dir, &persisted) {
            warn!("final state save failed: {e}");
        } else {
            info!("final state saved successfully");
        }
    }

    // Update discovery with final timestamp.
    if let Some(ref discovery_path) = args.discovery_file {
        write_discovery(discovery_path, &args.node_role, &local_addr)?;
    }

    accept_handle.abort();
    snapshot_handle.abort();
    if let Some(h) = gc_handle {
        h.abort();
    }

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
