//! `pyana-node`: The federation node daemon.
//!
//! This binary runs the backend that:
//! - Hosts an AgentWallet with token management
//! - Participates in federation consensus (attested roots)
//! - Serves a localhost HTTP API for the browser extension wallet
//! - Syncs state with federation peers

mod api;
mod federation_sync;
mod genesis;
mod mcp;
mod routing_table;
mod state;
mod ws;

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

        /// Federation peer addresses (host:port), comma-separated.
        #[arg(long, value_delimiter = ',')]
        federation_peers: Vec<String>,

        /// Data directory for persistent state.
        #[arg(long, default_value = "~/.pyana")]
        data_dir: String,

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
}

#[tokio::main]
async fn main() {
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
            federation_peers,
            data_dir,
            morpheus,
            node_index,
            federation_size,
            enable_pruning,
            checkpoint_interval,
            enable_faucet,
        } => {
            run_node(
                port,
                federation_peers,
                &data_dir,
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
    }
}

/// Run the node: start HTTP API server and federation sync.
async fn run_node(
    port: u16,
    peers: Vec<String>,
    data_dir: &str,
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

    // Initialize node state.
    let node_state = match state::NodeState::new(&data_path, peers) {
        Ok(s) => s,
        Err(e) => {
            error!("failed to initialize node state: {e}");
            std::process::exit(1);
        }
    };

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
    tokio::spawn(async move {
        federation_sync::run_federation_sync(sync_state, morpheus_config).await;
    });

    // Build and serve the HTTP API.
    let app = api::router(node_state.clone(), enable_faucet)
        .into_make_service_with_connect_info::<SocketAddr>();
    let addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), port);

    info!(%addr, "HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind HTTP listener");

    // P2 Fix 8: Graceful shutdown on Ctrl-C.
    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
        .expect("HTTP server error");

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

/// P2 Fix 8: Wait for Ctrl-C (SIGINT) to trigger graceful shutdown.
async fn shutdown_signal() {
    tokio::signal::ctrl_c()
        .await
        .expect("failed to listen for Ctrl-C");
    info!("received Ctrl-C, initiating graceful shutdown");
}
