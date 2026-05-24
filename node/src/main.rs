//! `pyana-node`: The federation node daemon.
//!
//! This binary runs the backend that:
//! - Hosts an AgentWallet with token management
//! - Participates in federation consensus (attested roots)
//! - Serves a localhost HTTP API for the browser extension wallet
//! - Syncs state with federation peers

mod api;
mod blocklace_sync;
// The old `bridge` module is removed. Cross-group communication now happens
// via multi_group.rs (unified blocklace cross-references + interest-based dissemination).
// See: `pyana-node run --groups` for multi-group participation.
mod genesis;
pub mod gossip;
mod mcp;
pub mod metrics;
pub mod multi_group;
mod relay_service;
mod routing_table;
mod state;
mod ws;

use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use pyana_federation::solo::FederationMode;
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

        #[arg(long, default_value = "0")]
        node_index: usize,

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

        /// Federation mode: "solo" for single-node devnet (default), "full" for BFT quorum.
        ///
        /// In solo mode, the node processes turns immediately without waiting for peers,
        /// skips gossip/consensus, produces Tentative receipts, and uses a local
        /// NullifierLog for sequencing. When peers are detected (via gossip), the node
        /// can auto-upgrade to full mode.
        #[arg(long, default_value = "solo")]
        federation_mode: String,

        ///
        /// "blocklace" uses the Cordial Miners blocklace for quiescent, leaderless
        /// DAG-based BFT consensus with the tau total ordering function.
        #[arg(long, default_value = "blocklace")]
        consensus: String,

        /// Reference groups to join (comma-separated group ID hex strings).
        /// When specified, the node participates in multiple groups simultaneously
        /// using cross-reference dissemination (Phase C) instead of the legacy
        /// bridge relay pattern. Each group ID is a 64-character hex string.
        #[arg(long, value_delimiter = ',')]
        groups: Vec<String>,

        /// (Dangerous) Auto-approve all federation join proposals received via
        /// gossip. F-CRIT-2: if true, ANY peer that publishes a
        /// `MembershipAction::Join` block causes this node to cast an Approve
        /// vote, which combined with the (n*2/3)+1 BFT threshold can flip the
        /// federation. Default: false. Devnet (`.devnet` marker file) implicitly
        /// enables this.
        #[arg(long)]
        auto_approve_joins: bool,
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

    /// Run as a hosted inbox relay operator.
    ///
    /// Starts an HTTP server that accepts CapTP store-and-forward messages,
    /// hosts inboxes for subscribed users, charges deposits, bonds computrons,
    /// runs periodic GC, and exposes status/monitoring endpoints.
    Relay {
        /// Port for the relay HTTP API.
        #[arg(long, default_value = "3100")]
        port: u16,

        /// Bond amount in computrons (operator stake).
        #[arg(long, default_value = "10000")]
        bond: u64,

        /// Maximum total inbox capacity to host.
        #[arg(long, default_value = "100000")]
        max_capacity: usize,

        /// GC interval in seconds.
        #[arg(long, default_value = "300")]
        gc_interval: u64,

        /// Message TTL in blocks (messages older than this are GC'd).
        #[arg(long, default_value = "1000")]
        message_ttl: u64,

        /// Max delivery latency (SLA) in blocks.
        #[arg(long, default_value = "50")]
        max_delivery_latency: u64,

        /// Path for persistent relay state file.
        #[arg(long, default_value = "./relay-state.json")]
        state_file: PathBuf,

        /// Data directory (for reading operator key).
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,

        /// Default inbox capacity for new subscriptions.
        #[arg(long, default_value = "100")]
        default_inbox_capacity: usize,

        /// Default minimum deposit for new inboxes.
        #[arg(long, default_value = "100")]
        default_min_deposit: u64,

        /// Minimum deposit per message (computrons).
        #[arg(long, default_value = "100")]
        min_message_deposit: u64,

        /// One-time subscription fee for creating an inbox.
        #[arg(long, default_value = "1000")]
        subscription_fee: u64,
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
            node_index,
            federation_size,
            enable_pruning,
            checkpoint_interval,
            enable_faucet,
            federation_mode,
            consensus,
            groups,
            auto_approve_joins,
        } => {
            run_node(
                port,
                &bind,
                federation_peers,
                &data_dir,
                &key_file,
                gossip_port,
                node_index,
                federation_size,
                enable_pruning,
                checkpoint_interval,
                enable_faucet,
                &federation_mode,
                &consensus,
                groups,
                auto_approve_joins,
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
        Command::Relay {
            port,
            bond,
            max_capacity,
            gc_interval,
            message_ttl,
            max_delivery_latency,
            state_file,
            data_dir,
            default_inbox_capacity,
            default_min_deposit,
            min_message_deposit,
            subscription_fee,
        } => {
            run_relay(
                port,
                bond,
                max_capacity,
                gc_interval,
                message_ttl,
                max_delivery_latency,
                state_file,
                &data_dir,
                default_inbox_capacity,
                default_min_deposit,
                min_message_deposit,
                subscription_fee,
            )
            .await
        }
    }
}

/// Run the node: start HTTP API server and federation sync.
#[allow(clippy::too_many_arguments)]
async fn run_node(
    port: u16,
    bind: &str,
    peers: Vec<String>,
    data_dir: &str,
    key_file: &str,
    gossip_port: u16,
    _node_index: usize,
    _federation_size: usize,
    enable_pruning: bool,
    checkpoint_interval: u64,
    enable_faucet: bool,
    federation_mode_str: &str,
    consensus_engine: &str,
    groups: Vec<String>,
    auto_approve_joins_flag: bool,
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
    let has_peers = !peers.is_empty();
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

    // Parse federation mode from CLI flag.
    let federation_mode: FederationMode = federation_mode_str.parse().unwrap_or_else(|e| {
        error!("invalid --federation-mode value: {e}; defaulting to solo");
        FederationMode::Solo
    });

    // Configure pruning and federation mode.
    {
        let mut s = node_state.write().await;
        s.pruning_enabled = enable_pruning;
        s.checkpoint_interval = checkpoint_interval;
        s.federation_mode = federation_mode;

        // In solo mode, initialize the SoloConsensusState with the node's signing key.
        if federation_mode == FederationMode::Solo {
            let signing_key = s.wallet.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(pyana_federation::solo::SoloConsensusState::new(signing_key));
            // Solo mode does NOT require federation keys for finalization —
            // the single node is authoritative.
            info!("federation mode: Solo — single-node devnet, no quorum required");
        } else {
            info!("federation mode: Full — BFT quorum required for finality");
        }
    }

    // Phase C: Log multi-group participation if --groups is specified.
    // Actual group membership is resolved once the blocklace syncs and the
    // group registry is available. For now we validate the group IDs.
    if !groups.is_empty() {
        let mut valid_groups = 0usize;
        for group_hex in &groups {
            if group_hex.len() != 64 {
                error!(
                    group = %group_hex,
                    "invalid group ID (expected 64 hex chars), skipping"
                );
                continue;
            }
            if hex_decode_32(group_hex).is_some() {
                valid_groups += 1;
            } else {
                error!(
                    group = %group_hex,
                    "invalid hex for group ID, skipping"
                );
            }
        }
        if valid_groups > 0 {
            info!(
                group_count = valid_groups,
                "multi-group mode enabled (Phase C cross-reference dissemination)"
            );
        }
    }

    // Install Prometheus metrics recorder.
    let metrics_handle = metrics::install_recorder();

    info!(
        port = port,
        data_dir = %data_path.display(),
        pruning = enable_pruning,
        checkpoint_interval = checkpoint_interval,
        faucet = enable_faucet,
        federation_mode = %federation_mode,
        "starting pyana-node"
    );

    // F-CRIT-2: gate auto-approval of federation join proposals on CLI flag or
    // `.devnet` marker. Defaults to false otherwise — any peer publishing a
    // MembershipAction::Join used to be enough to flip the federation.
    let auto_approve_joins =
        auto_approve_joins_flag || data_path.join(".devnet").exists();
    if auto_approve_joins {
        tracing::warn!(
            "auto-approve-joins is ENABLED — any peer publishing a join proposal \
             will receive our approval vote. Disable in production."
        );
    }

    // Spawn federation sync background task based on the chosen consensus engine.
    // In solo mode with no peers, skip gossip entirely regardless of engine.
    match consensus_engine {
        "blocklace" => {
            // Blocklace consensus: quiescent, leaderless DAG-based BFT.
            if federation_mode == FederationMode::Full || has_peers {
                info!(
                    consensus = "blocklace",
                    "using blocklace (Cordial Miners) consensus"
                );
                let sync_state = node_state.clone();
                let gossip_port_copy = gossip_port;
                tokio::spawn(async move {
                    blocklace_sync::run_blocklace_sync(
                        sync_state,
                        gossip_port_copy,
                        auto_approve_joins,
                    )
                    .await;
                });
            } else {
                info!("solo mode with no peers configured — blocklace sync skipped");
            }
        }
        _ => {
            error!(
                consensus = %consensus_engine,
                "unknown consensus engine"
            );
            std::process::exit(1);
        }
    }

    // Build and serve the HTTP API.
    let app = api::router(node_state.clone(), enable_faucet, metrics_handle)
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

/// Run the relay operator service.
#[allow(clippy::too_many_arguments)]
async fn run_relay(
    port: u16,
    bond: u64,
    max_capacity: usize,
    gc_interval: u64,
    message_ttl: u64,
    max_delivery_latency: u64,
    state_file: PathBuf,
    data_dir: &str,
    default_inbox_capacity: usize,
    default_min_deposit: u64,
    min_message_deposit: u64,
    subscription_fee: u64,
) {
    let data_path = expand_path(data_dir);

    // Read operator key from the data directory.
    let operator_key = if data_path.join("node.key").exists() {
        let key_bytes = std::fs::read(data_path.join("node.key"))
            .expect("failed to read node.key for relay operator identity");
        let mut key = [0u8; 32];
        key.copy_from_slice(&key_bytes[..32]);
        key
    } else {
        error!(
            "no node.key found in {}. Run `pyana-node init` first.",
            data_path.display()
        );
        std::process::exit(1);
    };

    let config = relay_service::RelayConfig {
        listen_port: port,
        operator_key,
        bond_amount: bond,
        fee_policy: relay_service::FeePolicy {
            min_deposit_computrons: min_message_deposit,
            subscription_fee,
            accept_external_assets: false,
            external_rate_micros: 1_000_000,
        },
        max_total_capacity: max_capacity,
        gc_interval_secs: gc_interval,
        message_ttl_blocks: message_ttl,
        max_delivery_latency_blocks: max_delivery_latency,
        state_file,
        default_inbox_capacity,
        default_min_deposit,
    };

    relay_service::run_relay_service(config).await;
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
