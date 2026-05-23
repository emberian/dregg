//! Directory commands: structured name resolution, mounting, discovery.

use clap::Subcommand;

use crate::config::Config;
use crate::output::{Context, TreeNode, abbrev_hex};

use super::{get_json, post_json};

#[derive(Subcommand)]
pub enum DirectoryCommand {
    /// List entries in a directory (name, kind, version, tags).
    List {
        /// Directory path (default: root "/").
        #[arg(default_value = "/")]
        path: String,
    },

    /// Resolve a name to its sturdy ref and metadata.
    Get {
        /// Full path including name (e.g., "/services/oracle").
        path: String,
    },

    /// Mount an entry in a directory.
    Mount {
        /// Full path including name (e.g., "/services/oracle").
        path: String,

        /// URI to mount (sturdy ref or service address).
        uri: String,

        /// Kind of entry.
        #[arg(long, value_parser = ["service", "factory", "data", "dir"])]
        kind: Option<String>,

        /// Tags for discovery.
        #[arg(long, value_delimiter = ',')]
        tags: Vec<String>,
    },

    /// Remove an entry from a directory (CAS with current version).
    Unmount {
        /// Full path including name.
        path: String,
    },

    /// Update an entry's URI (compare-and-swap with version).
    Update {
        /// Full path including name.
        path: String,

        /// New URI to set.
        new_uri: String,

        /// Expected current version (for CAS). If omitted, fetches current.
        #[arg(long)]
        version: Option<u64>,
    },

    /// Create a new sub-directory.
    Create {
        /// Path for the new directory.
        path: String,
    },

    /// Search across directories by tag or kind.
    Discover {
        /// Filter by tag.
        #[arg(long, value_delimiter = ',')]
        tag: Vec<String>,

        /// Filter by kind.
        #[arg(long, value_parser = ["service", "factory", "data", "dir"])]
        kind: Option<String>,
    },

    /// Show recursive directory tree (like unix `tree`).
    Tree {
        /// Starting path (default: root "/").
        #[arg(default_value = "/")]
        path: String,
    },
}

pub async fn run(
    cmd: DirectoryCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        DirectoryCommand::List { path } => list(cfg, ctx, &path).await,
        DirectoryCommand::Get { path } => get(cfg, ctx, &path).await,
        DirectoryCommand::Mount {
            path,
            uri,
            kind,
            tags,
        } => mount(cfg, ctx, &path, &uri, kind, &tags).await,
        DirectoryCommand::Unmount { path } => unmount(cfg, ctx, &path).await,
        DirectoryCommand::Update {
            path,
            new_uri,
            version,
        } => update(cfg, ctx, &path, &new_uri, version).await,
        DirectoryCommand::Create { path } => create(cfg, ctx, &path).await,
        DirectoryCommand::Discover { tag, kind } => discover(cfg, ctx, &tag, kind).await,
        DirectoryCommand::Tree { path } => tree(cfg, ctx, &path).await,
    }
}

async fn list(cfg: &Config, ctx: &Context, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Listing {}...", path));
    let encoded = urlencoding::encode(path);
    let data = get_json(cfg, &format!("/registry/list?path={}", encoded)).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let entries = data["entries"].as_array().unwrap_or(&empty);

    if entries.is_empty() {
        ctx.info(&format!("Directory '{}' is empty.", path));
        ctx.info("  Create entries with: pyana directory mount <path> <uri>");
        return Ok(());
    }

    ctx.header(&format!("Directory: {} ({} entries)", path, entries.len()));
    let rows: Vec<Vec<String>> = entries
        .iter()
        .map(|e| {
            let name = e["name"].as_str().unwrap_or("?");
            let kind = e["kind"].as_str().unwrap_or("-");
            let version = e["version"].as_u64().unwrap_or(0);
            let tags = e["tags"]
                .as_array()
                .map(|a| {
                    a.iter()
                        .filter_map(|v| v.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            vec![
                name.to_string(),
                kind.to_string(),
                format!("v{}", version),
                tags,
            ]
        })
        .collect();

    ctx.table(&["Name", "Kind", "Version", "Tags"], &rows);

    Ok(())
}

async fn get(cfg: &Config, ctx: &Context, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Resolving {}...", path));
    let encoded = urlencoding::encode(path);
    let data = get_json(cfg, &format!("/registry/get?path={}", encoded)).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let name = data["name"].as_str().unwrap_or("?");
    let uri = data["uri"].as_str().unwrap_or("(not set)");
    let kind = data["kind"].as_str().unwrap_or("-");
    let version = data["version"].as_u64().unwrap_or(0);
    let created = data["created_at"].as_str().unwrap_or("?");
    let updated = data["updated_at"].as_str().unwrap_or("?");

    let tags = data["tags"]
        .as_array()
        .map(|a| {
            a.iter()
                .filter_map(|v| v.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        })
        .unwrap_or_else(|| "-".to_string());

    let title = format!("Entry: {}", name);
    ctx.boxed(
        &title,
        &[
            ("Path", path),
            ("URI", uri),
            ("Kind", kind),
            ("Version", &format!("v{}", version)),
            ("Tags", &tags),
            ("Created", created),
            ("Updated", updated),
        ],
    );

    Ok(())
}

async fn mount(
    cfg: &Config,
    ctx: &Context,
    path: &str,
    uri: &str,
    kind: Option<String>,
    tags: &[String],
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Mounting at {}...", path));
    let body = serde_json::json!({
        "path": path,
        "uri": uri,
        "kind": kind.unwrap_or_else(|| "service".to_string()),
        "tags": tags,
    });
    let data = post_json(cfg, "/registry/mount", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let version = data["version"].as_u64().unwrap_or(1);
    ctx.success(&format!("Mounted at {}", path));
    ctx.kv("URI", &abbrev_hex(uri, 16, 4));
    ctx.kv("Version", &format!("v{}", version));
    if !tags.is_empty() {
        ctx.kv("Tags", &tags.join(", "));
    }

    Ok(())
}

async fn unmount(
    cfg: &Config,
    ctx: &Context,
    path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // Fetch current version for CAS.
    let encoded = urlencoding::encode(path);
    let current = get_json(cfg, &format!("/registry/get?path={}", encoded))
        .await
        .ok();
    let version = current
        .as_ref()
        .and_then(|d| d["version"].as_u64())
        .unwrap_or(0);

    let spinner = ctx.spinner(&format!("Unmounting {}...", path));
    let body = serde_json::json!({
        "path": path,
        "version": version,
    });
    let data = post_json(cfg, "/registry/unmount", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Unmounted: {}", path));

    Ok(())
}

async fn update(
    cfg: &Config,
    ctx: &Context,
    path: &str,
    new_uri: &str,
    version: Option<u64>,
) -> Result<(), Box<dyn std::error::Error>> {
    // If version not specified, fetch current.
    let cas_version = match version {
        Some(v) => v,
        None => {
            let encoded = urlencoding::encode(path);
            let current = get_json(cfg, &format!("/registry/get?path={}", encoded)).await?;
            current["version"].as_u64().unwrap_or(0)
        }
    };

    let spinner = ctx.spinner(&format!("Updating {}...", path));
    let body = serde_json::json!({
        "path": path,
        "uri": new_uri,
        "expected_version": cas_version,
    });
    let data = post_json(cfg, "/registry/update", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let new_version = data["version"].as_u64().unwrap_or(cas_version + 1);
    ctx.success(&format!("Updated: {}", path));
    ctx.kv("New URI", &abbrev_hex(new_uri, 16, 4));
    ctx.kv("Version", &format!("v{} -> v{}", cas_version, new_version));

    Ok(())
}

async fn create(cfg: &Config, ctx: &Context, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Creating directory {}...", path));
    let body = serde_json::json!({
        "path": path,
        "kind": "dir",
    });
    let data = post_json(cfg, "/registry/create", &body).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    ctx.success(&format!("Created directory: {}", path));

    Ok(())
}

async fn discover(
    cfg: &Config,
    ctx: &Context,
    tags: &[String],
    kind: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner("Searching directories...");

    let mut query_params = Vec::new();
    for tag in tags {
        query_params.push(format!("tag={}", urlencoding::encode(tag)));
    }
    if let Some(ref k) = kind {
        query_params.push(format!("kind={}", urlencoding::encode(k)));
    }

    let query = if query_params.is_empty() {
        String::new()
    } else {
        format!("?{}", query_params.join("&"))
    };

    let data = get_json(cfg, &format!("/registry/discover{}", query)).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let results = data["results"].as_array().unwrap_or(&empty);

    if results.is_empty() {
        ctx.info("No entries found matching the given filters.");
        return Ok(());
    }

    ctx.header(&format!("Discovery Results ({})", results.len()));
    let rows: Vec<Vec<String>> = results
        .iter()
        .map(|e| {
            let path = e["path"].as_str().unwrap_or("?");
            let name = e["name"].as_str().unwrap_or("?");
            let kind_str = e["kind"].as_str().unwrap_or("-");
            let uri = e["uri"].as_str().unwrap_or("?");
            vec![
                format!("{}/{}", path, name),
                kind_str.to_string(),
                abbrev_hex(uri, 12, 4),
            ]
        })
        .collect();

    ctx.table(&["Path", "Kind", "URI"], &rows);

    Ok(())
}

async fn tree(cfg: &Config, ctx: &Context, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let spinner = ctx.spinner(&format!("Building tree from {}...", path));
    let encoded = urlencoding::encode(path);
    let data = get_json(cfg, &format!("/registry/tree?path={}", encoded)).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }

    let empty = vec![];
    let entries = data["entries"].as_array().unwrap_or(&empty);

    if entries.is_empty() {
        ctx.info(&format!("No entries under '{}'.", path));
        return Ok(());
    }

    // Build tree nodes from flat list with depth info.
    let children: Vec<TreeNode> = entries
        .iter()
        .map(|e| {
            let name = e["name"].as_str().unwrap_or("?");
            let kind = e["kind"].as_str().unwrap_or("-");
            let _entry_path = e["path"].as_str().unwrap_or("");

            let label = match kind {
                "dir" => format!("{}/", name),
                _ => {
                    let uri = e["uri"].as_str().unwrap_or("");
                    if uri.is_empty() {
                        format!("{} [{}]", name, kind)
                    } else {
                        format!("{} [{}] -> {}", name, kind, abbrev_hex(uri, 10, 4))
                    }
                }
            };

            // Check for sub-entries.
            let sub_entries: Vec<TreeNode> = e["children"]
                .as_array()
                .unwrap_or(&vec![])
                .iter()
                .map(|sub| {
                    let sub_name = sub["name"].as_str().unwrap_or("?");
                    let sub_kind = sub["kind"].as_str().unwrap_or("-");
                    TreeNode::leaf(format!("{} [{}]", sub_name, sub_kind))
                })
                .collect();

            if sub_entries.is_empty() {
                TreeNode::leaf(label)
            } else {
                TreeNode::branch(label, sub_entries)
            }
        })
        .collect();

    let root_label = format!("{} ({} entries)", path, entries.len());
    ctx.tree(&root_label, &children);

    Ok(())
}
