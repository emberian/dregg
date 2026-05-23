//! Route commands: DFA route table inspection, classification, amendments.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex, format_number};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum RouteCommand {
    /// Show current DFA route table (paths to targets).
    Table,

    /// Classify a path through the DFA (show which handler matches).
    Classify {
        /// Path to classify (e.g., "/api/cell/abc123").
        path: String,
    },

    /// Propose a route amendment from a JSON file.
    Propose {
        /// Path to JSON file with route amendment.
        routes_file: String,
    },

    /// Show current route table blake3 commitment.
    Commitment,

    /// Show route amendment history.
    History {
        /// Maximum entries to show.
        #[arg(long, default_value = "20")]
        limit: usize,
    },
}

pub async fn run(
    cmd: RouteCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        RouteCommand::Table => table(cfg, ctx).await,
        RouteCommand::Classify { path } => classify(cfg, ctx, &path).await,
        RouteCommand::Propose { routes_file } => propose(cfg, ctx, &routes_file).await,
        RouteCommand::Commitment => commitment(cfg, ctx).await,
        RouteCommand::History { limit } => history(cfg, ctx, limit).await,
    }
}

async fn table(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching route table...");
    let data = get_json(cfg, "/federation/routes").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let routes = data["routes"].as_array().unwrap_or(&empty);

    if routes.is_empty() {
        ctx.info("No routes in the DFA route table.");
        ctx.info("  Propose routes with: pyana route propose <routes.json>");
        return Ok(());
    }

    ctx.header(&format!("DFA Route Table ({} routes)", routes.len()));
    let rows: Vec<Vec<String>> = routes
        .iter()
        .map(|r| {
            let pattern = r["pattern"].as_str().unwrap_or("?");
            let target = r["target"].as_str().unwrap_or("?");
            let priority = r["priority"].as_u64().unwrap_or(0);
            let state = r["state"].as_str().unwrap_or("active");
            vec![
                pattern.to_string(),
                target.to_string(),
                priority.to_string(),
                state.to_string(),
            ]
        })
        .collect();

    ctx.table(&["Pattern", "Target", "Priority", "State"], &rows);

    Ok(())
}

async fn classify(
    cfg: &Config,
    ctx: &Context,
    path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Classifying '{}'...", path));
    let body = serde_json::json!({
        "path": path,
    });
    let data = post_json(cfg, "/federation/routes/classify", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let matched = data["matched"].as_bool().unwrap_or(false);

    if matched {
        let pattern = data["pattern"].as_str().unwrap_or("?");
        let target = data["target"].as_str().unwrap_or("?");
        let dfa_state = data["dfa_state"].as_u64().unwrap_or(0);

        ctx.success(&format!("Path '{}' matches route:", path));
        ctx.kv("Pattern", pattern);
        ctx.kv("Target", target);
        ctx.kv("DFA state", &dfa_state.to_string());

        // Show DFA transitions if available.
        if let Some(transitions) = data["transitions"].as_array() {
            let children: Vec<TreeNode> = transitions
                .iter()
                .enumerate()
                .map(|(i, t)| {
                    let from = t["from"].as_u64().unwrap_or(0);
                    let to = t["to"].as_u64().unwrap_or(0);
                    let on = t["on"].as_str().unwrap_or("?");
                    TreeNode::leaf(format!("step {}: S{} --[{}]--> S{}", i, from, on, to))
                })
                .collect();
            ctx.tree("  DFA transitions:", &children);
        }
    } else {
        ctx.warn(&format!("Path '{}' does not match any route.", path));
        // Suggest closest patterns if available.
        if let Some(suggestions) = data["suggestions"].as_array() {
            let similar: Vec<&str> = suggestions
                .iter()
                .filter_map(|s| s.as_str())
                .take(3)
                .collect();
            if !similar.is_empty() {
                ctx.info(&format!("  Similar patterns: {}", similar.join(", ")));
            }
        }
    }

    Ok(())
}

async fn propose(
    cfg: &Config,
    ctx: &Context,
    routes_file: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(routes_file)
        .map_err(|e| format!("Could not read '{}': {}", routes_file, e))?;

    let routes_json: serde_json::Value = serde_json::from_str(&content)
        .map_err(|e| format!("Invalid JSON in '{}': {}", routes_file, e))?;

    let spinner = ctx.spinner("Proposing route amendment...");
    let body = serde_json::json!({
        "amendment": routes_json,
    });
    let data = post_json(cfg, "/federation/routes/propose", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let proposal_id = data["proposal_id"].as_str().unwrap_or("?");
    let route_count = data["route_count"].as_u64().unwrap_or(0);
    ctx.success("Route amendment proposed:");
    ctx.kv("Proposal ID", &abbrev_hex(proposal_id, 8, 4));
    ctx.kv("Routes", &route_count.to_string());
    ctx.info("  Validators vote with: pyana federation vote <proposal-id> yes|no");

    Ok(())
}

async fn commitment(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Computing route table commitment...");
    let data = get_json(cfg, "/federation/routes/commitment").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let hash = data["commitment"].as_str().unwrap_or("?");
    let route_count = data["route_count"].as_u64().unwrap_or(0);
    let last_amendment = data["last_amendment_height"].as_u64().unwrap_or(0);

    ctx.header("Route Table Commitment");
    ctx.kv("Blake3", hash);
    ctx.kv("Routes", &format_number(route_count));
    ctx.kv(
        "Last amendment",
        &format!("height {}", format_number(last_amendment)),
    );

    Ok(())
}

async fn history(
    cfg: &Config,
    ctx: &Context,
    limit: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching route amendment history...");
    let data = get_json(cfg, "/federation/routes/history").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let amendments = data["amendments"].as_array().unwrap_or(&empty);

    if amendments.is_empty() {
        ctx.info("No route amendments in history.");
        return Ok(());
    }

    ctx.header(&format!(
        "Route Amendment History ({} total)",
        amendments.len()
    ));
    let displayed: Vec<Vec<String>> = amendments
        .iter()
        .take(limit)
        .map(|a| {
            let height = a["height"].as_u64().unwrap_or(0);
            let kind = a["kind"].as_str().unwrap_or("?");
            let proposer = a["proposer"].as_str().unwrap_or("?");
            let route_count = a["route_count"].as_u64().unwrap_or(0);
            vec![
                format!("#{}", height),
                kind.to_string(),
                abbrev_hex(proposer, 8, 4),
                format!("{} routes", route_count),
            ]
        })
        .collect();

    ctx.table(&["Height", "Kind", "Proposer", "Routes"], &displayed);

    if amendments.len() > limit {
        ctx.info(&format!(
            "  Showing {} of {}. Use --limit to see more.",
            limit,
            amendments.len()
        ));
    }

    Ok(())
}
