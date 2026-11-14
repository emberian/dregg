//! `/status`, `/proof verify`, `/metrics` commands — federation health and verification.
//!
//! These read the **real** node surface through the shared `DevnetClient`
//! (`/status`, `/api/federations`, `/api/turn/{hash}/proof`) — no reinvention.
//! `/status` surfaces the full producer-fidelity picture the node reports
//! (verified-Lean vs legacy-Rust state producer, full-turn proving, and the
//! count of SWAP-safe effect kinds the verified producer covers), and
//! `/proof verify` fetches the genuine STARK proof artifact a committed turn
//! emitted rather than asking for a raw hex blob the public node won't verify.

use serde::Deserialize;
use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Real node read shapes (subset of the node's `/status` + proof routes) ───
//
// `devnet.rs` (shared infra) only deserializes the liveness subset of `/status`;
// the producer-fidelity fields below are read here directly off the same real
// route via `state.devnet.client()`, the established pattern for node routes the
// shared client doesn't model yet (see dashboard.rs `/queues/*`).

#[derive(Debug, Clone, Deserialize)]
struct StatusProducer {
    #[serde(default)]
    healthy: bool,
    #[serde(default)]
    peer_count: u32,
    #[serde(default)]
    latest_height: u64,
    #[serde(default)]
    dag_height: u64,
    #[serde(default)]
    block_count: u64,
    #[serde(default)]
    consensus_live: bool,
    #[serde(default)]
    federation_mode: String,
    #[serde(default)]
    state_producer: String,
    #[serde(default)]
    lean_producer: bool,
    #[serde(default)]
    full_turn_proving: bool,
    #[serde(default)]
    producer_covered_effects: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct FederationInfoWire {
    #[serde(default)]
    id: String,
    #[serde(default)]
    committee_epoch: u64,
    #[serde(default)]
    threshold: u32,
    #[serde(default)]
    member_count: usize,
    #[serde(default)]
    is_local: bool,
    #[serde(default)]
    latest_height: u64,
    #[serde(default)]
    latest_root: Option<String>,
    #[serde(default)]
    num_finalized_roots: usize,
}

#[derive(Debug, Clone, Deserialize)]
struct TurnProofWire {
    #[serde(default)]
    turn_hash: String,
    #[serde(default)]
    proof_len: u64,
    #[serde(default)]
    proof_hex: Option<String>,
    #[serde(default)]
    proof_status: String,
}

/// Fetch the full `/status` producer picture off the real node route.
async fn fetch_status_producer(state: &BotState) -> Result<StatusProducer, String> {
    let url = format!("{}/status", state.config.devnet_url.trim_end_matches('/'));
    let resp = state
        .devnet
        .client()
        .get(&url)
        .send()
        .await
        .map_err(|e| format!("could not reach the node: {e}"))?;
    if !resp.status().is_success() {
        return Err(format!("node returned HTTP {}", resp.status().as_u16()));
    }
    resp.json::<StatusProducer>()
        .await
        .map_err(|e| format!("could not parse /status: {e}"))
}

/// Fetch the real federation table off `/api/federations`.
async fn fetch_federations(state: &BotState) -> Result<Vec<FederationInfoWire>, String> {
    let url = format!(
        "{}/api/federations",
        state.config.devnet_url.trim_end_matches('/')
    );
    let resp = state
        .devnet
        .client()
        .get(&url)
        .send()
        .await
        .map_err(|e| format!("could not reach the node: {e}"))?;
    if !resp.status().is_success() {
        return Err(format!("node returned HTTP {}", resp.status().as_u16()));
    }
    resp.json::<Vec<FederationInfoWire>>()
        .await
        .map_err(|e| format!("could not parse /api/federations: {e}"))
}

fn short(s: &str, n: usize) -> String {
    if s.len() > n {
        format!("{}...", &s[..n])
    } else {
        s.to_string()
    }
}

/// Register the /status command. (Retired from the slash surface; the read
/// lives on behind the `start:status` button every menu carries.)
#[allow(dead_code)]
pub fn register_status() -> CreateCommand {
    CreateCommand::new("status").description("Show federation health status")
}

/// Register the /proof command (for proof artifact lookup on a committed turn).
pub fn register_proof() -> CreateCommand {
    CreateCommand::new("proof")
        .description("Fetch the STARK proof artifact a committed turn emitted")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "turn",
                "Fetch the proof artifact attached to a committed turn",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "hash",
                    "Turn hash (64 hex) of a committed turn",
                )
                .required(true),
            ),
        )
}

/// Register the /metrics command.
///
/// Retired from the slash surface (folded into `/status` + `/dashboard`); kept
/// so it can be re-registered if wanted.
#[allow(dead_code)]
pub fn register_metrics() -> CreateCommand {
    CreateCommand::new("metrics").description("Show key devnet metrics")
}

/// Handle /status interaction — the full node + producer-fidelity surface.
/// (Retired from the slash surface; `execute_status` carries the read.)
#[allow(dead_code)]
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;
    let embed = execute_status(state).await;
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Build the node-status embed (the read behind `/status` and the `/start`
/// "Node status" button) — health, producer fidelity, and the federation table.
pub(crate) async fn execute_status(state: &BotState) -> serenity::all::CreateEmbed {
    let status = match fetch_status_producer(state).await {
        Ok(status) => status,
        Err(e) => {
            return embeds::error_embed(
                "Node Offline",
                &format!(
                    "Could not reach the node `{}`: {e}\n\nDevnet may be offline. Try again shortly.",
                    state.config.devnet_url
                ),
            );
        }
    };

    let health_icon = if status.healthy {
        "\u{2705}"
    } else if status.consensus_live {
        "\u{26a0}\u{fe0f}"
    } else {
        "\u{274c}"
    };
    let health_word = if status.healthy {
        "HEALTHY"
    } else if status.consensus_live {
        "DEGRADED"
    } else {
        "OFFLINE"
    };

    // Producer fidelity — the SWAP story: verified-Lean producer vs legacy Rust.
    let producer_icon = if status.lean_producer {
        "\u{2705}" // verified Lean producer
    } else {
        "\u{26a0}\u{fe0f}" // legacy Rust path
    };
    let producer_label = if status.state_producer.is_empty() {
        if status.lean_producer { "lean" } else { "rust" }.to_string()
    } else {
        status.state_producer.clone()
    };
    let proving_icon = if status.full_turn_proving {
        "\u{2705}"
    } else {
        "\u{2796}" // heavy minus — proving off (still honest, not an error)
    };

    let nodes = if status.federation_mode == "solo" {
        "1 (solo)".to_string()
    } else {
        format!("{} peer(s) + self", status.peer_count)
    };

    let mut embed = embeds::dregg_embed("Node Status")
        .field("Health", format!("{health_icon} {health_word}"), true)
        .field(
            "Consensus",
            if status.consensus_live {
                "\u{2705} live"
            } else {
                "\u{274c} not running"
            },
            true,
        )
        .field("Federation Mode", &status.federation_mode, true)
        .field("Attested Height", status.latest_height.to_string(), true)
        .field("DAG Tip", status.dag_height.to_string(), true)
        .field("Blocks (local DAG)", status.block_count.to_string(), true)
        .field("Nodes", nodes, true)
        .field(
            "State Producer",
            format!("{producer_icon} {producer_label}"),
            true,
        )
        .field(
            "Full-Turn Proving",
            format!("{proving_icon} {}", status.full_turn_proving),
            true,
        )
        .field(
            "SWAP-Safe Effects Covered",
            status.producer_covered_effects.to_string(),
            true,
        );

    // Append the real federation table, when the node exposes it.
    match fetch_federations(state).await {
        Ok(feds) if !feds.is_empty() => {
            let mut lines = String::new();
            for fed in feds.iter().take(5) {
                let root = fed
                    .latest_root
                    .as_deref()
                    .map(|r| short(r, 12))
                    .unwrap_or_else(|| "none".to_string());
                lines.push_str(&format!(
                    "{} `{}` epoch {} · {}/{} thr · h{} · root `{}` · {} finalized\n",
                    if fed.is_local { "\u{2b50}" } else { "\u{2022}" },
                    short(&fed.id, 12),
                    fed.committee_epoch,
                    fed.threshold,
                    fed.member_count,
                    fed.latest_height,
                    root,
                    fed.num_finalized_roots,
                ));
            }
            embed = embed.field("Federations", lines, false);
        }
        _ => {}
    }

    embed
}

/// Handle /proof interaction — fetch the real proof artifact a committed turn
/// emitted, off `/api/turn/{hash}/proof`.
pub async fn handle_proof(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let turn_hash = sub_opts
        .iter()
        .find(|o| o.name == "hash")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.trim().to_string()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    if turn_hash.len() != 64 || hex::decode(&turn_hash).is_err() {
        let embed = embeds::error_embed(
            "Invalid Turn Hash",
            "Provide the 64-hex hash of a committed turn (find one via `/explorer recent`).",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let url = format!(
        "{}/api/turn/{turn_hash}/proof",
        state.config.devnet_url.trim_end_matches('/')
    );
    let resp = match state.devnet.client().get(&url).send().await {
        Ok(resp) => resp,
        Err(e) => {
            let embed = embeds::error_embed(
                "Node Unreachable",
                &format!("Could not reach the node to fetch the proof: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    if resp.status().as_u16() == 404 {
        let embed = embeds::warning_embed(
            "No Proof Attached",
            &format!(
                "Turn `{}...` has no proof artifact on record. Either the hash is unknown, or this turn committed on the executor-signed-receipt path without a full-turn STARK proof (check `/status` → Full-Turn Proving).",
                short(&turn_hash, 16)
            ),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }
    if !resp.status().is_success() {
        let embed = embeds::error_embed(
            "Proof Lookup Failed",
            &format!("Node returned HTTP {}.", resp.status().as_u16()),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match resp.json::<TurnProofWire>().await {
        Ok(proof) => {
            if proof.proof_status == "not_required"
                || proof.proof_hex.as_ref().is_none_or(|p| p.is_empty())
            {
                let embed = embeds::error_embed(
                    "No Validity Proof",
                    "Coordination policy or missing artifact: the anchor is signature attestation only. Proof verification requires an actual STARK.",
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            let proof_hex = proof.proof_hex.as_ref().expect("checked above");
            let kib = proof.proof_len as f64 / 1024.0;
            let preview = short(proof_hex, 32);
            // ⚑ THE ANCHOR FIRST, AND IT IS REQUIRED. Without a committee-signed anchor this
            // command has nothing external to judge the artifact against, so it REFUSES to
            // report a verdict rather than comparing the artifact against itself. See
            // `proof_verify`'s docblock.
            let anchor = match crate::commands::proof_verify::fetch_and_verify_anchor(
                state.devnet.client(),
                &state.config.devnet_url,
                &turn_hash,
            )
            .await
            {
                Ok(anchor) => anchor,
                Err(why) => {
                    let embed = embeds::warning_embed(
                        "Proof Artifact · NO VERDICT (unanchored)",
                        &crate::commands::proof_verify::no_anchor_text(&turn_hash, &why),
                    );
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };
            // VERIFY the fetched artifact right here — the bot runs the same audited
            // Plonky3 verifier a remote peer would, against the turn hash the COMMITTEE
            // signed, and reports the verdict rather than "Attached ✅" trust-me.
            // The TITLE says "legs verify", not "verifies": the state anchors compared are
            // still the proof's own (seam 1), so the bytes are not tied to the chain's state
            // transition. Every seam is spelled out in the Verification field below.
            let check =
                crate::commands::proof_verify::check_proof_hex_blocking(proof_hex.clone(), anchor)
                    .await;
            // THREE outcomes, not two. `Err` is a REFUSAL (this bot could not obtain a
            // state-commit pair to judge the artifact against — a `cipherclerk`-minted or
            // proof-carrying turn) and must not be painted as "the bytes failed", which reads as
            // evidence against the artifact when it is evidence about what could be obtained.
            let base = match &check {
                Ok(c) if c.verified => embeds::success_embed(
                    "Proof Artifact · legs verify, bound to the committee-signed turn and the \
                     node's derived state commits",
                ),
                Ok(_) => embeds::error_embed(
                    "Proof Artifact · DOES NOT VERIFY",
                    "The fetched bytes failed the bot's own re-check.",
                ),
                Err(_) => embeds::warning_embed(
                    "Proof Artifact · NO VERDICT",
                    "This bot could not obtain values to judge the artifact against.",
                ),
            };
            let embed = base
                .field(
                    "Turn",
                    format!("`{}...`", short(&proof.turn_hash, 16)),
                    false,
                )
                .field(
                    "Proof Size",
                    format!("{} bytes ({kib:.1} KiB)", proof.proof_len),
                    true,
                )
                .field("Proof (head)", format!("`{preview}...`"), false)
                .field(
                    "Verification",
                    crate::commands::proof_verify::verdict_text(&check),
                    false,
                )
                .field(
                    "Re-check it yourself",
                    crate::commands::proof_verify::offline_recheck_text(
                        &state.config.devnet_url,
                        &turn_hash,
                    ),
                    false,
                )
                .field(
                    "Explorer",
                    crate::explorer_link::view_link("turn", &turn_hash, "View turn"),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Proof Decode Failed",
                &format!("The node returned a proof body the bot couldn't parse: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /metrics interaction.
#[allow(dead_code)]
pub async fn handle_metrics(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.metrics().await {
        Ok(metrics) => {
            let uptime_str = format_uptime(metrics.uptime_secs);

            let embed = embeds::dregg_embed("Devnet Metrics")
                .field("TPS", format!("{:.2}", metrics.tps), true)
                .field("Block Height", metrics.block_height.to_string(), true)
                .field("Pending Turns", metrics.pending_turns.to_string(), true)
                .field("Active Cells", metrics.active_cells.to_string(), true)
                .field("Memory", format!("{} MB", metrics.memory_usage_mb), true)
                .field("Uptime", uptime_str, true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Metrics Unavailable",
                &format!(
                    "Could not load metrics: {e}\n\nDevnet is currently offline, try again later."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

fn format_uptime(secs: u64) -> String {
    let days = secs / 86400;
    let hours = (secs % 86400) / 3600;
    let mins = (secs % 3600) / 60;
    if days > 0 {
        format!("{days}d {hours}h {mins}m")
    } else if hours > 0 {
        format!("{hours}h {mins}m")
    } else {
        format!("{mins}m")
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}
