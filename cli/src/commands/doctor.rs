//! Doctor command: system health checks.

use crate::config::Config;
use crate::output::{Context, format_number};

use super::{api_url, get_json, http_client};

/// A single health check result.
struct Check {
    #[allow(dead_code)]
    name: String,
    passed: bool,
    detail: String,
}

pub async fn run(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    ctx.header("System Health Check");

    let mut checks: Vec<Check> = Vec::new();

    // 1. Node reachable.
    checks.push(check_node(cfg).await);

    // 2. Federation connected.
    checks.push(check_federation(cfg).await);

    // 3. Routes committed.
    checks.push(check_routes(cfg).await);

    // 4. Storage quota.
    checks.push(check_storage(cfg).await);

    // 5. Shell completions.
    checks.push(check_completions());

    // 6. Blocklace checkpoints (new feature observability).
    checks.push(check_blocklace(cfg).await);

    // 7. Receipts / receipt chain health.
    checks.push(check_receipts(cfg).await);

    // Display results.
    let pass_count = checks.iter().filter(|c| c.passed).count();
    let fail_count = checks.len() - pass_count;

    for check in &checks {
        let indicator = if check.passed {
            console::style("\u{2713}").green().bold().to_string()
        } else {
            console::style("\u{2717}").red().bold().to_string()
        };
        eprintln!("  {} {}", indicator, check.detail);
    }

    eprintln!();
    if fail_count == 0 {
        ctx.success(&format!("All {} checks passed.", pass_count));
    } else {
        ctx.warn(&format!("{} passed, {} failed.", pass_count, fail_count));
    }

    Ok(())
}

async fn check_node(cfg: &Config) -> Check {
    let client = http_client();
    let url = api_url(cfg, "/status");
    let result = client
        .get(&url)
        .timeout(std::time::Duration::from_secs(5))
        .send()
        .await;

    match result {
        Ok(resp) if resp.status().is_success() => Check {
            name: "node".to_string(),
            passed: true,
            detail: format!("Node reachable at {}", cfg.node.url),
        },
        Ok(resp) => Check {
            name: "node".to_string(),
            passed: false,
            detail: format!("Node at {} returned HTTP {}", cfg.node.url, resp.status()),
        },
        Err(e) => Check {
            name: "node".to_string(),
            passed: false,
            detail: format!("Node unreachable at {} ({})", cfg.node.url, e),
        },
    }
}

async fn check_federation(cfg: &Config) -> Check {
    match get_json(cfg, "/status").await {
        Ok(data) => {
            let peer_count = data["peer_count"].as_u64().unwrap_or(0);
            let height = data["latest_height"].as_u64().unwrap_or(0);
            if peer_count > 0 {
                Check {
                    name: "federation".to_string(),
                    passed: true,
                    detail: format!(
                        "Federation connected ({} peers, height {})",
                        peer_count, height
                    ),
                }
            } else {
                Check {
                    name: "federation".to_string(),
                    passed: false,
                    detail: "Federation: no peers connected (solo mode)".to_string(),
                }
            }
        }
        Err(_) => Check {
            name: "federation".to_string(),
            passed: false,
            detail: "Federation status unavailable (node unreachable)".to_string(),
        },
    }
}

async fn check_routes(cfg: &Config) -> Check {
    match get_json(cfg, "/federation/routes").await {
        Ok(data) => {
            let route_count = data["routes"].as_array().map(|a| a.len()).unwrap_or(0);
            if route_count > 0 {
                Check {
                    name: "routes".to_string(),
                    passed: true,
                    detail: format!("Routes committed ({} active routes)", route_count),
                }
            } else {
                // No routes might just mean empty, which is fine for solo.
                Check {
                    name: "routes".to_string(),
                    passed: true,
                    detail: "Routes: table empty (no routes configured)".to_string(),
                }
            }
        }
        Err(_) => Check {
            name: "routes".to_string(),
            passed: false,
            detail: "Routes: could not fetch route table".to_string(),
        },
    }
}

async fn check_storage(cfg: &Config) -> Check {
    match get_json(cfg, "/storage/quota").await {
        Ok(data) => {
            let bytes_stored = data["bytes_stored"].as_u64().unwrap_or(0);
            let bytes_limit = data["bytes_limit"].as_u64().unwrap_or(0);
            let remaining_pct = if bytes_limit > 0 {
                ((bytes_limit - bytes_stored) as f64 / bytes_limit as f64 * 100.0) as u64
            } else {
                100
            };

            if remaining_pct < 10 {
                Check {
                    name: "storage".to_string(),
                    passed: false,
                    detail: format!(
                        "Storage quota low (< 10% remaining, {}% used)",
                        100 - remaining_pct
                    ),
                }
            } else {
                Check {
                    name: "storage".to_string(),
                    passed: true,
                    detail: format!("Storage quota OK ({}% remaining)", remaining_pct),
                }
            }
        }
        Err(_) => Check {
            name: "storage".to_string(),
            passed: true,
            detail: "Storage: quota endpoint not available (OK for basic setups)".to_string(),
        },
    }
}

fn check_completions() -> Check {
    // Check common completion file locations.
    let home = dirs::home_dir().unwrap_or_default();
    let locations = [
        home.join(".zsh/completions/_pyana"),
        home.join(".local/share/bash-completion/completions/pyana"),
        home.join(".config/fish/completions/pyana.fish"),
        // Also check if they might be system-wide.
        std::path::PathBuf::from("/usr/local/share/zsh/site-functions/_pyana"),
        std::path::PathBuf::from("/opt/homebrew/share/zsh/site-functions/_pyana"),
    ];

    let found = locations.iter().any(|p| p.exists());

    if found {
        Check {
            name: "completions".to_string(),
            passed: true,
            detail: "Shell completions installed".to_string(),
        }
    } else {
        Check {
            name: "completions".to_string(),
            passed: false,
            detail: "Shell completions not found (run: pyana completions <shell> > ...)"
                .to_string(),
        }
    }
}

/// Check for blocklace checkpoint availability (parity with node blocklace_sync + /api/blocklace/checkpoint).
async fn check_blocklace(cfg: &Config) -> Check {
    match get_json(cfg, "/api/blocklace/checkpoint").await {
        Ok(data) => {
            let h = data["height"].as_u64().unwrap_or(0);
            if h > 0 {
                Check {
                    name: "blocklace".to_string(),
                    passed: true,
                    detail: format!(
                        "Blocklace checkpoint available (height {})",
                        format_number(h)
                    ),
                }
            } else {
                Check {
                    name: "blocklace".to_string(),
                    passed: true,
                    detail: "Blocklace: no checkpoints yet (normal for fresh node)".to_string(),
                }
            }
        }
        Err(_) => Check {
            name: "blocklace".to_string(),
            passed: true, // not fatal
            detail:
                "Blocklace checkpoints: endpoint not present or node unreachable (OK for basic)"
                    .to_string(),
        },
    }
}

/// Receipt chain / cipherclerk health (observability + receipts parity).
async fn check_receipts(cfg: &Config) -> Check {
    match get_json(cfg, "/cipherclerk").await {
        Ok(data) => {
            let rc_len = data["receipt_chain_length"].as_u64().unwrap_or(0);
            if rc_len > 0 {
                Check {
                    name: "receipts".to_string(),
                    passed: true,
                    detail: format!("Receipt chain healthy ({} receipts)", format_number(rc_len)),
                }
            } else {
                Check {
                    name: "receipts".to_string(),
                    passed: true,
                    detail: "Receipt chain: empty (fresh cipherclerk)".to_string(),
                }
            }
        }
        Err(_) => Check {
            name: "receipts".to_string(),
            passed: false,
            detail: "Receipt chain status unavailable (node/cipherclerk unreachable)".to_string(),
        },
    }
}
