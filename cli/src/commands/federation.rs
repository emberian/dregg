//! Federation info: constitution, participants, routes, governance.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex, format_number};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum FederationCommand {
    /// Show constitution, participants, threshold, and height.
    Status,

    /// Submit a governance proposal.
    Propose {
        /// Proposal type (e.g., "add-validator", "change-threshold", "parameter").
        #[arg(value_name = "TYPE")]
        proposal_type: String,

        /// Additional arguments as JSON.
        #[arg(value_name = "ARGS")]
        args: Option<String>,
    },

    /// Vote on a governance proposal.
    Vote {
        /// Proposal ID.
        proposal_id: String,

        /// Vote: "yes" or "no".
        #[arg(value_parser = ["yes", "no"])]
        vote: String,
    },

    /// Show the current route table and commitment.
    Routes,
}

pub async fn run(
    cmd: FederationCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        FederationCommand::Status => status(cfg, ctx).await,
        FederationCommand::Propose {
            proposal_type,
            args,
        } => propose(cfg, ctx, &proposal_type, args).await,
        FederationCommand::Vote { proposal_id, vote } => {
            vote_cmd(cfg, ctx, &proposal_id, &vote).await
        }
        FederationCommand::Routes => routes(cfg, ctx).await,
    }
}

async fn status(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching federation status...");
    let data = get_json(cfg, "/status").await?;
    let roots = get_json(cfg, "/federation/roots").await.ok();
    spinner.finish_and_clear();

    if cfg.is_json() {
        let combined = serde_json::json!({
            "status": data,
            "roots": roots,
        });
        ctx.json_stdout(&combined);
        return Ok(());
    }

    let mode = data["federation_mode"].as_str().unwrap_or("unknown");
    let height = data["latest_height"].as_u64().unwrap_or(0);
    let peer_count = data["peer_count"].as_u64().unwrap_or(0);

    // Build tree display.
    let federation_label = format!(
        "Federation: {} ({})",
        cfg.node.url.replace("http://", "").replace("https://", ""),
        mode
    );

    let mut children = vec![];

    // Participants.
    let participant_label = format!(
        "Participants: {}/{} online",
        peer_count,
        peer_count + 1 // include self
    );
    let mut participant_children = vec![];

    // Self node is always present.
    participant_children.push(TreeNode::leaf(format!(
        "self (this node) {} wave {}",
        console::style("\u{2713}").green(),
        height
    )));

    // Add peers from roots if available.
    if let Some(ref roots_data) = roots {
        if let Some(root_entries) = roots_data.as_array() {
            for (i, entry) in root_entries.iter().enumerate().take(10) {
                let fallback = format!("node-{}", i + 1);
                let node_label = entry["node_id"].as_str().unwrap_or(&fallback);
                let wave = entry["wave"].as_u64().unwrap_or(0);
                participant_children.push(TreeNode::leaf(format!(
                    "{} {} wave {}",
                    abbrev_hex(node_label, 8, 4),
                    console::style("\u{2713}").green(),
                    wave
                )));
            }
        }
    }

    children.push(TreeNode::branch(participant_label, participant_children));

    // Threshold.
    let threshold = if peer_count > 0 {
        let total = peer_count + 1;
        let t = (total * 2 / 3) + 1;
        format!("{} (\u{2154}+1 of {})", t, total)
    } else {
        "1 (solo mode)".to_string()
    };
    children.push(TreeNode::leaf(format!("Threshold: {}", threshold)));

    // Height.
    children.push(TreeNode::leaf(format!(
        "Height: {} (finalized: {})",
        format_number(height),
        format_number(height.saturating_sub(2))
    )));

    ctx.tree(&federation_label, &children);

    Ok(())
}

async fn propose(
    cfg: &Config,
    ctx: &Context,
    proposal_type: &str,
    args: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let parsed_args: serde_json::Value = match args {
        Some(ref a) => serde_json::from_str(a).unwrap_or(serde_json::Value::String(a.clone())),
        None => serde_json::Value::Null,
    };

    let spinner = ctx.spinner("Submitting proposal...");
    let body = serde_json::json!({
        "type": proposal_type,
        "args": parsed_args,
    });
    let data = post_json(cfg, "/turn/atomic", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let proposal_id = data["proposal_id"].as_str().unwrap_or("?");
    ctx.success(&format!("Proposal submitted: {}", proposal_id));
    ctx.kv("Type", proposal_type);
    ctx.info("  Validators can vote with: dregg federation vote <id> yes|no");

    Ok(())
}

async fn vote_cmd(
    cfg: &Config,
    ctx: &Context,
    proposal_id: &str,
    vote: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Casting vote...");
    let body = serde_json::json!({
        "proposal_id": proposal_id,
        "vote": vote == "yes",
    });
    let data = post_json(cfg, "/turn/atomic/vote", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let accepted = data["accepted"].as_bool().unwrap_or(true);
    if accepted {
        ctx.success(&format!(
            "Vote '{}' cast on proposal {}",
            vote,
            abbrev_hex(proposal_id, 8, 4)
        ));
    } else {
        ctx.warn("Vote was not accepted (possibly already voted or proposal expired).");
    }

    Ok(())
}

async fn routes(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching route table...");
    let data = get_json(cfg, "/federation/roots").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let entries = data.as_array().unwrap_or(&empty);
    if entries.is_empty() {
        ctx.info("No routes in the federation route table.");
        return Ok(());
    }

    ctx.header(&format!("Route Table ({} entries)", entries.len()));
    let rows: Vec<Vec<String>> = entries
        .iter()
        .map(|e| {
            let node_id = e["node_id"].as_str().unwrap_or("?");
            let wave = e["wave"].as_u64().unwrap_or(0);
            let hash = e["root_hash"].as_str().unwrap_or("?");
            vec![
                abbrev_hex(node_id, 8, 4),
                wave.to_string(),
                abbrev_hex(hash, 8, 4),
            ]
        })
        .collect();

    ctx.table(&["Node", "Wave", "Root Hash"], &rows);

    // Compute commitment hash over all root hashes.
    let mut hasher = blake3::Hasher::new();
    for entry in entries {
        if let Some(h) = entry["root_hash"].as_str() {
            hasher.update(h.as_bytes());
        }
    }
    let commitment = hasher.finalize();
    ctx.kv_dim("Commitment", &abbrev_hex(commitment.to_hex().as_ref(), 8, 4));

    Ok(())
}
