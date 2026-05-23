//! `pyana-node`: The federation node daemon.
//!
//! This binary runs the backend that:
//! - Hosts an AgentWallet with token management
//! - Participates in federation consensus (attested roots)
//! - Serves a localhost HTTP API for the browser extension wallet
//! - Syncs state with federation peers

mod api;
mod bridge;
mod federation_sync;
mod genesis;
mod mcp;
mod routing_table;
mod state;
mod ws;

use std::collections::HashMap;
use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing::{error, info};

#[derive(Parser)]
#[command(name = "pyana-node", about = "Pyana federation node daemon")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run the node daemon (HTTP API + federation sync).
    Run {
        /// Port for the localhost HTTP API.
        #[arg(long, default_value = "8420")]
        port: u16,

        /// Bind address for the HTTP API. Defaults to 127.0.0.1 (localhost only).
        /// Use --bind 0.0.0.0 to expose to the network.
        #[arg(long, default_value = "127.0.0.1")]
        bind: String,

        /// Federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,

        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,

        /// Path to the node key file (relative to data-dir or absolute).
        /// Default: "node.key" in the data directory.
        #[arg(long, default_value = "node.key")]
        key_file: String,

        /// Port for the gossip/federation sync protocol.
        #[arg(long, default_value = "9420")]
        gossip_port: u16,

        /// Use the full Morpheus DAG-based BFT consensus instead of simplified consensus.
        /// Requires the `morpheus` feature on pyana-federation.
        #[arg(long)]
        morpheus: bool,

        /// This node's index in the federation (0-based). Required when --morpheus is set.
        #[arg(long, default_value = "0")]
        node_index: usize,

        /// Total number of federation nodes. Required when --morpheus is set.
        #[arg(long, default_value = "4")]
        federation_size: usize,

        /// Enable automatic pruning of old blocks/roots below the latest checkpoint.
        /// Off by default (archival mode). Turn on to bound storage growth.
        #[arg(long)]
        enable_pruning: bool,

        /// Checkpoint interval in blocks (default: 1000).
        #[arg(long, default_value = "1000")]
        checkpoint_interval: u64,

        /// Enable the faucet endpoint (POST /api/faucet).
        /// Only suitable for devnets. Allows anyone to request computrons from the
        /// genesis faucet cell.
        #[arg(long)]
        enable_faucet: bool,
    },

    /// Initialize the data directory and generate a node keypair.
    Init {
        /// Data directory to initialize.
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,
    },

    /// Check if the node is running and show sync state.
    Status {
        /// Port to check (default: 8420).
        #[arg(long, default_value = "8420")]
        port: u16,
    },

    /// Run as an MCP (Model Context Protocol) server over stdio.
    ///
    /// Reads JSON-RPC from stdin and writes responses to stdout.
    /// Used by AI assistants (Claude, GPT, etc.) to interact with the node.
    Mcp {
        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,

        /// Federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,
    },

    /// Generate devnet genesis configuration (keys, genesis.json, env files).
    Genesis {
        /// Number of validator nodes to generate keys for.
        #[arg(long, default_value = "4")]
        validators: usize,

        /// Epoch length in blocks.
        #[arg(long, default_value = "1000")]
        epoch_length: u64,

        /// Checkpoint interval in blocks.
        #[arg(long, default_value = "100")]
        checkpoint_interval: u64,

        /// Output directory for the generated configuration.
        #[arg(long, default_value = "./devnet-config")]
        output: PathBuf,
    },

    /// Run as a cross-federation bridge node.
    ///
    /// Connects to multiple federations' gossip networks and relays messages
    /// between them: attested roots, revocations, receipts, and conditional
    /// proof completions. Enables cross-federation token operations.
    Bridge {
        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,

        /// Local federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,

        /// Remote federation peer addresses (federation_id_hex:host:port), comma-separated.
        /// The federation_id is a 64-character hex string identifying the remote federation.
        #[arg(long, value_delimiter = ',')]
        remote_peers: Vec<String>,

        /// Port for the bridge's local HTTP API (status/admin).
        #[arg(long, default_value = "8421")]
        port: u16,

        /// Disable relay of attested roots between federations.
        #[arg(long)]
        no_relay_roots: bool,

        /// Disable relay of revocations between federations.
        #[arg(long)]
        no_relay_revocations: bool,

        /// Disable relay of receipts between federations.
        #[arg(long)]
        no_relay_receipts: bool,

        /// Disable relay of conditional proof completions.
        #[arg(long)]
        no_relay_conditionals: bool,

        /// Maximum age (seconds) for accepting remote attested roots. Default: 3600.
        #[arg(long, default_value = "3600")]
        max_remote_root_age: u64,

        /// Path to a JSON file containing trusted public keys for remote federations.
        /// Format: `{"<federation_id_hex>": ["<pubkey_hex>", ...], ...}`.
        /// If not provided, the node's known federation keys are used as a fallback.
        /// The bridge refuses to start in relay mode if no trusted keys are available.
        #[arg(long)]
        remote_keys: Option<PathBuf>,
    },
}

#[tokio::main]
async fn main() {
    // Install the ring CryptoProvider for rustls (required by quinn/QUIC).
    rustls::crypto::ring::default_provider()
        .install_default()
        .expect("failed to install rustls CryptoProvider");

    // Initialize tracing.
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "pyana_node=info".into()),
        )
        .init();

    let cli = Cli::parse();

    match cli.command {
        Command::Run {
            port,
            bind,
            federation_peers,
            data_dir,
            key_file,
            gossip_port,
            morpheus,
            node_index,
            federation_size,
            enable_pruning,
            checkpoint_interval,
            enable_faucet,
        } => {
            run_node(
                port,
                &bind,
                federation_peers,
                &data_dir,
                &key_file,
                gossip_port,
                morpheus,
                node_index,
                federation_size,
                enable_pruning,
                checkpoint_interval,
                enable_faucet,
            )
            .await
        }
        Command::Init { data_dir } => init_node(&data_dir),
        Command::Status { port } => check_status(port).await,
        Command::Mcp {
            data_dir,
            federation_peers,
        } => run_mcp(&data_dir, federation_peers).await,
        Command::Genesis {
            validators,
            epoch_length,
            checkpoint_interval,
            output,
        } => genesis::run_genesis(validators, epoch_length, checkpoint_interval, &output),
        Command::Bridge {
            data_dir,
            federation_peers,
            remote_peers,
            port: _port,
            no_relay_roots,
            no_relay_revocations,
            no_relay_receipts,
            no_relay_conditionals,
            max_remote_root_age,
            remote_keys,
        } => {
            run_bridge(
                &data_dir,
                federation_peers,
                remote_peers,
                no_relay_roots,
                no_relay_revocations,
                no_relay_receipts,
                no_relay_conditionals,
                max_remote_root_age,
                remote_keys,
            )
            .await
        }
    }
}

/// Run the node: start HTTP API server and federation sync.
async fn run_node(
    port: u16,
    bind: &str,
    peers: Vec<String>,
    data_dir: &str,
    key_file: &str,
    gossip_port: u16,
    morpheus: bool,
    node_index: usize,
    federation_size: usize,
    enable_pruning: bool,
    checkpoint_interval: u64,
    enable_faucet: bool,
) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!(
            "data directory does not exist: {}. Run `pyana-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    // Check for `.devnet` marker and warn prominently.
    if data_path.join(".devnet").exists() {
        tracing::warn!("Running in DEVNET mode \u{2014} keys are not production-grade");
    }

    // Initialize node state with configurable key file.
    let node_state = match state::NodeState::new_with_key_file(&data_path, peers, key_file) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

    // Load genesis.json if present in the data directory.
    let genesis_path = data_path.join("genesis.json");
    if genesis_path.exists() {
        match std::fs::read_to_string(&genesis_path) {
            Ok(json_str) => {
                match serde_json::from_str::<serde_json::Value>(&json_str) {
                    Ok(genesis) => {
                        let mut s = node_state.write().await;
                        // Extract validator public keys from genesis.
                        if let Some(validators) = genesis["validators"].as_array() {
                            let mut fed_keys = Vec::new();
                            for v in validators {
                                if let Some(pk_hex) = v["public_key"].as_str() {
                                    if let Some(pk_bytes) = hex_decode_32(pk_hex) {
                                        fed_keys.push(pyana_types::PublicKey(pk_bytes));
                                    }
                                }
                            }
                            if !fed_keys.is_empty() {
                                info!(
                                    key_count = fed_keys.len(),
                                    "loaded federation keys from genesis.json"
                                );
                                s.set_federation_keys(fed_keys);
                            }
                        }
                        // Extract threshold from genesis.
                        if let Some(threshold) = genesis["threshold"].as_u64() {
                            s.decryption_threshold = threshold as usize;
                        }
                        // Extract checkpoint interval from genesis.
                        if let Some(ci) = genesis["checkpoint_interval"].as_u64() {
                            s.checkpoint_interval = ci;
                        }
                        info!(genesis = %genesis_path.display(), "genesis configuration loaded");
                    }
                    Err(e) => {
                        error!(error = %e, "failed to parse genesis.json");
                    }
                }
            }
            Err(e) => {
                error!(error = %e, "failed to read genesis.json");
            }
        }
    }

    // Configure pruning.
    {
        let mut s = node_state.write().await;
        s.pruning_enabled = enable_pruning;
        s.checkpoint_interval = checkpoint_interval;
    }

    info!(
        port = port,
        data_dir = %data_path.display(),
        pruning = enable_pruning,
        checkpoint_interval = checkpoint_interval,
        faucet = enable_faucet,
        "starting pyana-node"
    );

    // Spawn federation sync background task.
    let sync_state = node_state.clone();
    let morpheus_config = if morpheus {
        Some(federation_sync::MorpheusConfig {
            node_index,
            federation_size,
        })
    } else {
        None
    };
    let gossip_port_copy = gossip_port;
    tokio::spawn(async move {
        federation_sync::run_federation_sync(sync_state, morpheus_config, gossip_port_copy).await;
    });

    // Build and serve the HTTP API.
    let app = api::router(node_state.clone(), enable_faucet)
        .into_make_service_with_connect_info::<SocketAddr>();
    let bind_addr: std::net::IpAddr = bind.parse().unwrap_or_else(|_| {
        error!("invalid --bind address: {bind}, falling back to 127.0.0.1");
        Ipv4Addr::LOCALHOST.into()
    });
    let addr = SocketAddr::new(bind_addr, port);

    if bind_addr == std::net::IpAddr::V4(Ipv4Addr::UNSPECIFIED)
        || bind_addr == std::net::IpAddr::V6(std::net::Ipv6Addr::UNSPECIFIED)
    {
        tracing::warn!(
            %addr,
            "binding to all interfaces — faucet, wallet, bridge endpoints are exposed to the network"
        );
    }

    info!(%addr, "HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind HTTP listener");

    // P2 Fix 8: Graceful shutdown on Ctrl-C.
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
        .expect("HTTP server error");

    // Persist critical state before exiting.
    node_state.persist_on_shutdown().await;

    info!("HTTP server shut down gracefully");
}

/// Initialize the data directory: create it and generate a keypair.
fn init_node(data_dir: &str) {
    let data_path = expand_path(data_dir);

    if data_path.exists() {
        println!("Data directory already exists: {}", data_path.display());
        println!("Skipping initialization.");
        return;
    }

    std::fs::create_dir_all(&data_path).expect("failed to create data directory");

    // Generate a node keypair and store the public key for display.
    let mut key_bytes = [0u8; 32];
    getrandom::fill(&mut key_bytes).expect("getrandom failed");

    // Write the secret key to the data dir (in production, use a keyring).
    let key_path = data_path.join("node.key");
    std::fs::write(&key_path, key_bytes).expect("failed to write node key");

    // Restrict file permissions to owner read/write only (0600).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600))
            .expect("failed to set node.key permissions");
    }

    // Derive public key for display.
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
    let public_key = signing_key.verifying_key();
    let pk_hex: String = public_key
        .to_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();

    println!(
        "Initialized pyana-node data directory: {}",
        data_path.display()
    );
    println!("Node public key: {pk_hex}");
    println!();
    println!("Start the node with:");
    println!("  pyana-node run --data-dir {}", data_dir);
}

/// Check if the node is running by hitting the status endpoint.
async fn check_status(port: u16) {
    let url = format!("http://127.0.0.1:{port}/status");

    // Use a raw TCP connection to check — avoids adding reqwest as a dep.
    let addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), port);
    match tokio::net::TcpStream::connect(addr).await {
        Ok(_) => {
            println!("pyana-node is running on port {port}");
            println!("  Status endpoint: {url}");
        }
        Err(_) => {
            println!("pyana-node is NOT running on port {port}");
            std::process::exit(1);
        }
    }
}

/// Expand `~` in a path string.
fn expand_path(path: &str) -> PathBuf {
    if path.starts_with("~/") {
        if let Some(home) = dirs_home() {
            return home.join(&path[2..]);
        }
    }
    PathBuf::from(path)
}

/// Get the home directory.
fn dirs_home() -> Option<PathBuf> {
    std::env::var_os("HOME").map(PathBuf::from)
}

/// Run the MCP server: initialize node state and serve over stdio.
async fn run_mcp(data_dir: &str, peers: Vec<String>) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!(
            "data directory does not exist: {}. Run `pyana-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    let node_state = match state::NodeState::new(&data_path, peers) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

    mcp::run_stdio(node_state).await;
}

/// Run the cross-federation bridge node.
async fn run_bridge(
    data_dir: &str,
    federation_peers: Vec<String>,
    remote_peers: Vec<String>,
    no_relay_roots: bool,
    no_relay_revocations: bool,
    no_relay_receipts: bool,
    no_relay_conditionals: bool,
    max_remote_root_age: u64,
    remote_keys: Option<PathBuf>,
) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!(
            "data directory does not exist: {}. Run `pyana-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    }

    // Initialize node state (bridge uses the same local state as a regular node).
    let node_state = match state::NodeState::new(&data_path, federation_peers.clone()) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

    // Start local federation sync if peers are configured.
    if !federation_peers.is_empty() {
        let sync_state = node_state.clone();
        tokio::spawn(async move {
            // Bridge mode uses default gossip port.
            federation_sync::run_federation_sync(sync_state, None, 9420).await;
        });
    }

    // Load trusted remote federation keys from file or node state.
    let remote_federation_keys: HashMap<[u8; 32], Vec<pyana_types::PublicKey>> = if let Some(
        keys_path,
    ) = remote_keys
    {
        match std::fs::read_to_string(&keys_path) {
            Ok(json_str) => {
                // Parse JSON: { "federation_id_hex": ["pubkey_hex", ...], ... }
                match serde_json::from_str::<HashMap<String, Vec<String>>>(&json_str) {
                    Ok(raw) => {
                        let mut result = HashMap::new();
                        for (fed_hex, key_hexes) in raw {
                            if fed_hex.len() != 64 {
                                error!(
                                    federation = %fed_hex,
                                    "invalid federation ID (expected 64 hex chars), skipping"
                                );
                                continue;
                            }
                            let fed_id = match hex_decode_32(&fed_hex) {
                                Some(id) => id,
                                None => {
                                    error!(federation = %fed_hex, "invalid hex for federation ID");
                                    continue;
                                }
                            };
                            let keys: Vec<pyana_types::PublicKey> = key_hexes
                                .iter()
                                .filter_map(|kh| hex_decode_32(kh).map(pyana_types::PublicKey))
                                .collect();
                            if !keys.is_empty() {
                                result.insert(fed_id, keys);
                            }
                        }
                        result
                    }
                    Err(e) => {
                        error!(error = %e, "failed to parse remote keys JSON");
                        std::process::exit(1);
                    }
                }
            }
            Err(e) => {
                error!(path = %keys_path.display(), error = %e, "failed to read remote keys file");
                std::process::exit(1);
            }
        }
    } else {
        HashMap::new()
    };

    // Build relay configuration from CLI flags.
    let relay_config = bridge::RelayConfig {
        relay_roots: !no_relay_roots,
        relay_revocations: !no_relay_revocations,
        relay_receipts: !no_relay_receipts,
        relay_conditionals: !no_relay_conditionals,
        max_remote_root_age_secs: max_remote_root_age,
        max_cached_roots: 100,
    };

    info!(
        data_dir = %data_path.display(),
        local_peers = federation_peers.len(),
        remote_peers = remote_peers.len(),
        relay_roots = relay_config.relay_roots,
        relay_revocations = relay_config.relay_revocations,
        relay_receipts = relay_config.relay_receipts,
        relay_conditionals = relay_config.relay_conditionals,
        "starting cross-federation bridge node"
    );

    // Run the bridge (blocks forever).
    bridge::run_bridge(
        node_state,
        remote_peers,
        relay_config,
        remote_federation_keys,
    )
    .await;
}

/// Decode a 64-char hex string into a [u8; 32].
fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

/// P2 Fix 8: Wait for Ctrl-C (SIGINT) to trigger graceful shutdown.
async fn shutdown_signal() {
    tokio::signal::ctrl_c()
        .await
        .expect("failed to listen for Ctrl-C");
    info!("received Ctrl-C, initiating graceful shutdown");
}
