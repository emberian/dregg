//! Service mesh namespace commands: mount, discover, resolve, browse, unmount.

use clap::Subcommand;
use dialoguer::Input;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum NamespaceCommand {
    /// Mount a service at a namespace path.
    Mount {
        /// Namespace path (e.g., "/services/oracle/price-feed").
        path: String,

        /// Sturdy reference URI for the service.
        sturdy_ref: String,

        /// Kind of entry (service, factory, data, dir).
        #[arg(long, value_parser = ["service", "factory", "data", "dir"])]
        kind: Option<String>,

        /// Tags for service discovery.
        #[arg(long, value_delimiter = ',')]
        tags: Vec<String>,
    },

    /// Discover services by tag or kind.
    Discover {
        /// Filter by tags.
        #[arg(long, value_delimiter = ',')]
        tag: Vec<String>,

        /// Filter by kind.
        #[arg(long, value_delimiter = ',')]
        kind: Vec<String>,
    },

    /// Resolve a namespace path to its sturdy reference.
    Resolve {
        /// Namespace path to resolve.
        path: String,
    },

    /// Browse the namespace tree interactively.
    Browse {
        /// Starting path (default: root "/").
        #[arg(default_value = "/")]
        path: String,
    },

    /// Remove a service from a namespace path.
    Unmount {
        /// Namespace path to unmount.
        path: String,
    },
}

pub async fn run(
    cmd: NamespaceCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        NamespaceCommand::Mount {
            path,
            sturdy_ref,
            kind,
            tags,
        } => mount(cfg, ctx, &path, &sturdy_ref, kind, &tags).await,
        NamespaceCommand::Discover { tag, kind } => discover(cfg, ctx, &tag, &kind).await,
        NamespaceCommand::Resolve { path } => resolve(cfg, ctx, &path).await,
        NamespaceCommand::Browse { path } => browse(cfg, ctx, &path).await,
        NamespaceCommand::Unmount { path } => unmount(cfg, ctx, &path).await,
    }
}

async fn mount(
    cfg: &Config,
    ctx: &Context,
    path: &str,
    sturdy_ref: &str,
    kind: Option<String>,
    tags: &[String],
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Mounting service at {}...", path));
    let kind_str = kind.unwrap_or_else(|| "service".to_string());
    let body = serde_json::json!({
        "path": path,
        "sturdy_ref": sturdy_ref,
        "kind": kind_str,
        "tags": tags,
    });
    let data = post_json(cfg, "/cells/register", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Mounted service at {}", path));
    ctx.kv("Kind", &kind_str);
    ctx.kv("Sturdy ref", &abbrev_hex(sturdy_ref, 12, 4));
    if !tags.is_empty() {
        ctx.kv("Tags", &tags.join(", "));
    }

    Ok(())
}

async fn discover(
    cfg: &Config,
    ctx: &Context,
    tags: &[String],
    kinds: &[String],
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Discovering services...");
    // Query the cells endpoint with namespace-style filtering.
    let data = get_json(cfg, "/api/cells").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let cells = data.as_array().unwrap_or(&empty);

    // Filter by tags/kinds if provided.
    let filtered: Vec<&serde_json::Value> = cells
        .iter()
        .filter(|c| {
            if tags.is_empty() && kinds.is_empty() {
                return true;
            }
            let cell_tags = c["tags"]
                .as_array()
                .map(|a| {
                    a.iter()
                        .filter_map(|v| v.as_str())
                        .map(String::from)
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            let cell_kind = c["kind"].as_str().unwrap_or("");

            let tag_match = tags.is_empty() || tags.iter().any(|t| cell_tags.contains(t));
            let kind_match = kinds.is_empty() || kinds.iter().any(|k| k == cell_kind);

            tag_match && kind_match
        })
        .collect();

    if filtered.is_empty() {
        ctx.info("No services found matching the given filters.");
        if !tags.is_empty() {
            ctx.info(&format!("  Tags: {}", tags.join(", ")));
        }
        if !kinds.is_empty() {
            ctx.info(&format!("  Kinds: {}", kinds.join(", ")));
        }
        return Ok(());
    }

    ctx.header(&format!("Services ({})", filtered.len()));
    let rows: Vec<Vec<String>> = filtered
        .iter()
        .map(|c| {
            let id = c["id"].as_str().unwrap_or("?");
            let path = c["path"].as_str().unwrap_or("/");
            let kind = c["kind"].as_str().unwrap_or("-");
            let cell_tags = c["tags"]
                .as_array()
                .map(|a| {
                    a.iter()
                        .filter_map(|v| v.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            vec![
                path.to_string(),
                abbrev_hex(id, 8, 4),
                kind.to_string(),
                cell_tags,
            ]
        })
        .collect();

    ctx.table(&["Path", "Cell", "Kind", "Tags"], &rows);

    Ok(())
}

async fn resolve(
    cfg: &Config,
    ctx: &Context,
    path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Resolving {}...", path));
    let data = get_json(cfg, "/api/cells").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    // Look for a cell mounted at the given path.
    let empty = vec![];
    let cells = data.as_array().unwrap_or(&empty);
    let found = cells.iter().find(|c| c["path"].as_str() == Some(path));

    match found {
        Some(cell) => {
            let id = cell["id"].as_str().unwrap_or("?");
            let sturdy_ref = cell["sturdy_ref"].as_str().unwrap_or("(no ref)");
            ctx.success(&format!("Resolved: {}", path));
            ctx.kv("Cell", &abbrev_hex(id, 8, 4));
            ctx.kv("Sturdy ref", sturdy_ref);
        }
        None => {
            ctx.warn(&format!("Path '{}' not found in namespace.", path));
            // Suggest closest match.
            let similar: Vec<&str> = cells
                .iter()
                .filter_map(|c| {
                    let p = c["path"].as_str()?;
                    if p.starts_with(&path[..path.len().clamp(1, 3)]) {
                        Some(p)
                    } else {
                        None
                    }
                })
                .take(3)
                .collect();
            if !similar.is_empty() {
                ctx.info(&format!("  Did you mean: {}?", similar.join(", ")));
            }
        }
    }

    Ok(())
}

async fn browse(
    cfg: &Config,
    ctx: &Context,
    start_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Loading namespace tree...");
    let data = get_json(cfg, "/api/cells").await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let cells = data.as_array().unwrap_or(&empty);

    // Build a simple tree structure from paths.
    let mut paths: Vec<(&str, &str)> = cells
        .iter()
        .filter_map(|c| {
            let path = c["path"].as_str()?;
            let id = c["id"].as_str().unwrap_or("?");
            if path.starts_with(start_path) || start_path == "/" {
                Some((path, id))
            } else {
                None
            }
        })
        .collect();
    paths.sort_by_key(|(p, _)| *p);

    if paths.is_empty() {
        ctx.info(&format!("Namespace is empty at '{}'.", start_path));
        ctx.info("  Mount a service with: dregg namespace mount <path> <sturdy-ref>");
        return Ok(());
    }

    let children: Vec<TreeNode> = paths
        .iter()
        .map(|(path, id)| TreeNode::leaf(format!("{} \u{2192} {}", path, abbrev_hex(id, 8, 4))))
        .collect();

    let root_label = format!("Namespace ({})", start_path);
    ctx.tree(&root_label, &children);

    // Interactive mode: let user pick a path to inspect.
    if ctx.mode != crate::output::Mode::Json && ctx.mode != crate::output::Mode::Plain {
        eprintln!();
        let input: String = Input::new()
            .with_prompt("Resolve path (or press Enter to exit)")
            .allow_empty(true)
            .interact_text()?;

        if !input.is_empty() {
            resolve(cfg, ctx, &input).await?;
        }
    }

    Ok(())
}

async fn unmount(
    cfg: &Config,
    ctx: &Context,
    path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Unmounting {}...", path));
    let body = serde_json::json!({
        "path": path,
    });
    let data = post_json(cfg, "/cells/deregister", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Unmounted service at {}", path));

    Ok(())
}
