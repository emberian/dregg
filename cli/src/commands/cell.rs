//! Cell inspection and manipulation commands.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum CellCommand {
    /// Show cell state, nonce, permissions, c-list.
    Inspect {
        /// Cell ID (hex or base58).
        cell_id: String,
    },

    /// List cells in your cclerk.
    List,

    /// Create a new cell.
    Create {
        /// Optional program to install on the new cell.
        #[arg(long)]
        program: Option<String>,

        /// Optional label for the cell.
        #[arg(long)]
        label: Option<String>,
    },

    /// Show turn history for a cell.
    History {
        /// Cell ID.
        cell_id: String,

        /// Maximum number of turns to show.
        #[arg(long, default_value = "20")]
        limit: usize,
    },
}

pub async fn run(
    cmd: CellCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        CellCommand::Inspect { cell_id } => inspect(cfg, ctx, &cell_id).await,
        CellCommand::List => list(cfg, ctx).await,
        CellCommand::Create { program, label } => create(cfg, ctx, program, label).await,
        CellCommand::History { cell_id, limit } => history(cfg, ctx, &cell_id, limit).await,
    }
}

async fn inspect(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching cell state...");
    let path = format!("/api/cell/{cell_id}");
    let data = get_json(cfg, &path).await.map_err(|e| {
        spinner.finish_and_clear();
        format!("Failed to fetch cell {}: {}", abbrev_hex(cell_id, 6, 4), e)
    })?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let nonce = data["nonce"].as_u64().unwrap_or(0);
    let state_hash = data["state_hash"].as_str().unwrap_or("unknown");
    let committed = data["committed"].as_bool().unwrap_or(false);
    let mode = data["mode"].as_str().unwrap_or("Unknown");
    let program = data["program"].as_str().unwrap_or("(none)");

    let state_display = format!(
        "{} ({})",
        abbrev_hex(state_hash, 6, 4),
        if committed { "committed" } else { "pending" }
    );

    let send_perm = data["permissions"]["send"].as_str().unwrap_or("None");
    let recv_perm = data["permissions"]["receive"].as_str().unwrap_or("None");
    let perm_display = format!("send={send_perm}, receive={recv_perm}");

    let title = format!("Cell {}", abbrev_hex(cell_id, 6, 4));
    let mut rows: Vec<(&str, String)> = vec![
        ("Nonce", nonce.to_string()),
        ("State", state_display),
        ("Permissions", perm_display),
        ("Mode", mode.to_string()),
        ("Program", program.to_string()),
    ];

    // C-list entries.
    let clist = data["clist"].as_array();
    if let Some(entries) = clist {
        rows.push(("C-list", format!("{} entries", entries.len())));
    }

    let row_refs: Vec<(&str, &str)> = rows.iter().map(|(k, v)| (*k, v.as_str())).collect();
    ctx.boxed(&title, &row_refs);

    // Print c-list entries underneath if present.
    if let Some(entries) = clist {
        if !entries.is_empty() {
            let children: Vec<TreeNode> = entries
                .iter()
                .enumerate()
                .map(|(i, entry)| {
                    let label_str = entry["label"].as_str().unwrap_or("?");
                    let target = entry["target"].as_str().unwrap_or("?");
                    TreeNode::leaf(format!(
                        "[{i}] {:<12} \u{2192} {}",
                        label_str,
                        abbrev_hex(target, 6, 4)
                    ))
                })
                .collect();
            ctx.tree("  C-list:", &children);
        }
    }

    Ok(())
}

async fn list(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching cells...");
    let data = get_json(cfg, "/api/cells").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let cells = data.as_array().unwrap_or(&empty);
    if cells.is_empty() {
        ctx.info("No cells found. Create one with `pyana cell create`.");
        return Ok(());
    }

    ctx.header(&format!("Cells ({})", cells.len()));
    let mut rows: Vec<Vec<String>> = Vec::new();
    for cell in cells {
        let id = cell["id"].as_str().unwrap_or("?");
        let label = cell["label"].as_str().unwrap_or("-");
        let nonce = cell["nonce"].as_u64().unwrap_or(0);
        let mode = cell["mode"].as_str().unwrap_or("?");
        rows.push(vec![
            abbrev_hex(id, 8, 4),
            label.to_string(),
            nonce.to_string(),
            mode.to_string(),
        ]);
    }
    ctx.table(&["ID", "Label", "Nonce", "Mode"], &rows);

    Ok(())
}

async fn create(
    cfg: &Config,
    ctx: &Context,
    program: Option<String>,
    label: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Creating cell...");
    let body = serde_json::json!({
        "program": program.unwrap_or_default(),
        "label": label.unwrap_or_default(),
    });
    let data = post_json(cfg, "/cells/register", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let cell_id = data["cell_id"].as_str().unwrap_or("unknown");
    ctx.success(&format!("Created cell: {}", cell_id));
    ctx.info("  Use `pyana cell inspect` to view its state.");

    Ok(())
}

async fn history(
    cfg: &Config,
    ctx: &Context,
    cell_id: &str,
    limit: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Fetching turn history...");
    let path = format!("/api/cell/{cell_id}");
    let data = get_json(cfg, &path).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let turns = data["history"].as_array();
    match turns {
        Some(entries) if !entries.is_empty() => {
            ctx.header(&format!("Turn history for {}", abbrev_hex(cell_id, 6, 4)));
            let display: Vec<Vec<String>> = entries
                .iter()
                .take(limit)
                .enumerate()
                .map(|(_i, t)| {
                    let height = t["height"].as_u64().unwrap_or(0);
                    let hash = t["hash"].as_str().unwrap_or("?");
                    let effects = t["effect_count"].as_u64().unwrap_or(0);
                    vec![
                        format!("#{}", height),
                        abbrev_hex(hash, 6, 4),
                        format!("{} effects", effects),
                    ]
                })
                .collect();
            ctx.table(&["Height", "Hash", "Effects"], &display);
        }
        _ => {
            ctx.info(&format!(
                "No turn history for cell {}",
                abbrev_hex(cell_id, 6, 4)
            ));
        }
    }

    Ok(())
}
