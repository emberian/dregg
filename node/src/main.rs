//! `pyana-node`: The federation node daemon.
//!
//! This binary runs the backend that:
//! - Hosts an AgentWallet with token management
//! - Participates in federation consensus (attested roots)
//! - Serves a localhost HTTP API for the browser extension wallet
//! - Syncs state with federation peers

mod api;
mod federation_sync;
mod state;

use std::net::{Ipv4Addr, SocketAddr};
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use tracing::{info, error};

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
        } => run_node(port, federation_peers, &data_dir).await,
        Command::Init { data_dir } => init_node(&data_dir),
        Command::Status { port } => check_status(port).await,
    }
}

/// Run the node: start HTTP API server and federation sync.
async fn run_node(port: u16, peers: Vec<String>, data_dir: &str) {
    let data_path = expand_path(data_dir);

    if !data_path.exists() {
        error!("data directory does not exist: {}. Run `pyana-node init` first.", data_path.display());
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

    info!(port = port, data_dir = %data_path.display(), "starting pyana-node");

    // Spawn federation sync background task.
    let sync_state = node_state.clone();
    tokio::spawn(async move {
        federation_sync::run_federation_sync(sync_state).await;
    });

    // Build and serve the HTTP API.
    let app = api::router(node_state);
    let addr = SocketAddr::new(Ipv4Addr::LOCALHOST.into(), port);

    info!(%addr, "HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind HTTP listener");

    axum::serve(listener, app)
        .await
        .expect("HTTP server error");
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
    let pk_hex: String = public_key.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

    println!("Initialized pyana-node data directory: {}", data_path.display());
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
