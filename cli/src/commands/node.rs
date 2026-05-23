//! Node operations: status, connect, peers, sync.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, format_number};

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
