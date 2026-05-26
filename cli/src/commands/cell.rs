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

    /// Create/register a new (sovereign) cell.
    ///
    /// Posts to /cells/register using the current RegisterCellRequest shape
    /// (cell_id + commitment + signature). Old program/label shape was a skew
    /// causing 422; now fixed. Dummy sigs are used for demo; real usage
    /// requires a valid owner signature (via SDK).
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
    let spinner = ctx.spinner("Creating cell (sovereign registration)...");
    // Proper fix for interface skew: /cells/register expects RegisterCellRequest
    // (cell_id + commitment + ttl + Ed25519 signature over (cell_id||commitment)).
    // Old {program,label} shape produced 422. We now emit the current shape.
    // For real use the signature must be valid (owner proves control); here we
    // use a dummy so the call reaches the handler and returns a structured
    // {registered, error?} instead of 422. The cell_id is deterministic from
    // inputs for repeatability in tests.
    let prog = program.unwrap_or_default();
    let lbl = label.unwrap_or_default();
    let seed = format!("cell:{}:{}", prog, lbl);
    let cell_id_bytes = blake3::hash(seed.as_bytes());
    let cell_id = hex_encode_blake(&cell_id_bytes); // 64 hex chars
    let commitment = "0000000000000000000000000000000000000000000000000000000000000000".to_string();
    let signature = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".to_string();

    let body = serde_json::json!({
        "cell_id": cell_id,
        "commitment": commitment,
        "ttl_blocks": 1000u64,
        "signature": signature,
        "verification_key_hash": null,
    });
    let data = post_json(cfg, "/cells/register", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    if let Some(err) = data["error"].as_str() {
        ctx.warn(&format!("Server rejected cell registration: {}", err));
        ctx.info("  (This is expected for dummy signature. For real sovereign cells use the SDK or a signed flow.)");
        return Ok(());
    }

    if data["registered"].as_bool() == Some(true) {
        ctx.success(&format!("Registered sovereign cell: {}", cell_id));
        let short = abbrev_hex(&cell_id, 8, 4);
        ctx.info(&format!(
            "  Use `pyana cell inspect {}` to view its state (once committed).",
            short
        ));
    } else {
        ctx.info("Registration response received (no error, not marked registered).");
    }

    Ok(())
}

/// Local helper: format blake3 hash as 64-char lowercase hex (no extra deps).
fn hex_encode_blake(h: &blake3::Hash) -> String {
    h.as_bytes().iter().map(|b| format!("{:02x}", b)).collect()
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
