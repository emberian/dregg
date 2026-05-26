//! Node operations: status, connect, peers, sync.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, abbrev_hex, format_number};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum NodeCommand {
    /// Show node health, connections, and sync state.
    Status,

    /// Connect to a peer.
    Connect {
        /// Peer address (host:port).
        address: String,
    },

    /// List connected peers.
    Peers,

    /// Force sync with peers.
    Sync,

    /// Fetch blocklace checkpoint (supports new blocklace fast-sync / observability).
    /// Returns DAG snapshot + ledger snapshot (hex) + integrity hashes.
    BlocklaceCheckpoint {
        /// Specific height (default: latest available checkpoint).
        #[arg(long)]
        height: Option<u64>,
    },
}

pub async fn run(
    cmd: NodeCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        NodeCommand::Status => status(cfg, ctx).await,
        NodeCommand::Connect { address } => connect(cfg, ctx, &address).await,
        NodeCommand::Peers => peers(cfg, ctx).await,
        NodeCommand::Sync => sync(cfg, ctx).await,
        NodeCommand::BlocklaceCheckpoint { height } => blocklace_checkpoint(cfg, ctx, height).await,
    }
}

async fn status(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Checking node status...");
    let data = get_json(cfg, "/status").await.map_err(|e| {
        spinner.finish_and_clear();
        format!(
            "Cannot reach node at {}. Is pyana-node running?\n  Error: {}",
            cfg.node.url, e
        )
    })?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let healthy = data["healthy"].as_bool().unwrap_or(false);
    let peer_count = data["peer_count"].as_u64().unwrap_or(0);
    let height = data["latest_height"].as_u64().unwrap_or(0);
    let revocations = data["revocation_count"].as_u64().unwrap_or(0);
    let notes = data["note_count"].as_u64().unwrap_or(0);
    let mode = data["federation_mode"].as_str().unwrap_or("unknown");

    let health_indicator = if healthy {
        console::style("HEALTHY").green().bold().to_string()
    } else {
        console::style("UNHEALTHY").red().bold().to_string()
    };

    ctx.header("Node Status");
    ctx.kv("Health", &health_indicator);
    ctx.kv("URL", &cfg.node.url);
    ctx.kv("Federation mode", mode);
    ctx.kv("Height", &format_number(height));
    ctx.kv("Peers", &peer_count.to_string());
    ctx.kv("Revocations", &format_number(revocations));
    ctx.kv("Notes", &format_number(notes));

    Ok(())
}

async fn connect(
    cfg: &Config,
    ctx: &Context,
    address: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Connecting to {}...", address));
    let body = serde_json::json!({
        "address": address,
    });
    // There's no dedicated connect endpoint; this would be a gossip-layer operation.
    // For now we document that this talks to the node's peer management.
    let data = post_json(cfg, "/api/node/connect", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Connected to peer: {}", address));
    Ok(())
}

async fn peers(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching peers...");
    let data = get_json(cfg, "/status").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let peer_count = data["peer_count"].as_u64().unwrap_or(0);
    let peers_arr = data["peers"].as_array();

    ctx.header(&format!("Connected Peers ({})", peer_count));

    match peers_arr {
        Some(ps) if !ps.is_empty() => {
            let rows: Vec<Vec<String>> = ps
                .iter()
                .map(|p| {
                    let addr = p["address"].as_str().unwrap_or("?");
                    let status_str = p["status"].as_str().unwrap_or("?");
                    let wave = p["wave"].as_u64().unwrap_or(0);
                    vec![addr.to_string(), status_str.to_string(), wave.to_string()]
                })
                .collect();
            ctx.table(&["Address", "Status", "Wave"], &rows);
        }
        _ => {
            if peer_count > 0 {
                ctx.info(&format!(
                    "{peer_count} peer(s) connected (details not available via this endpoint)."
                ));
            } else {
                ctx.info("No peers connected. Use `pyana node connect <address>` to add one.");
            }
        }
    }

    Ok(())
}

async fn sync(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Forcing sync...");
    let body = serde_json::json!({});
    let data = post_json(cfg, "/api/node/sync", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success("Sync initiated.");
    let new_height = data["height"].as_u64();
    if let Some(h) = new_height {
        ctx.kv("New height", &format_number(h));
    }

    Ok(())
}

async fn blocklace_checkpoint(
    cfg: &Config,
    ctx: &Context,
    height: Option<u64>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching blocklace checkpoint...");
    let path = match height {
        Some(h) => format!("/api/blocklace/checkpoint?height={}", h),
        None => "/api/blocklace/checkpoint".to_string(),
    };
    let data = get_json(cfg, &path).await.map_err(|e| {
        spinner.finish_and_clear();
        format!(
            "Blocklace checkpoint unavailable: {}. (Node may not have checkpoints yet.)",
            e
        )
    })?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let h = data["height"].as_u64().unwrap_or(0);
    let bl_hash = data["blocklace_hash"].as_str().unwrap_or("?");
    let ld_hash = data["ledger_hash"].as_str().unwrap_or("?");

    ctx.header(&format!(
        "Blocklace Checkpoint @ height {}",
        format_number(h)
    ));
    ctx.kv("Blocklace hash", &abbrev_hex(bl_hash, 8, 4));
    ctx.kv("Ledger hash", &abbrev_hex(ld_hash, 8, 4));
    ctx.info("  Use --json for full DAG + snapshot (large). Supports fast sync for new nodes.");
    ctx.info("  See node/src/blocklace_sync.rs for checkpoint format.");

    Ok(())
}
