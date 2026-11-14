//! `/explorer` command — browse devnet state from Discord.
//!
//! Subcommands: feed, cell, turn, block, blocklace, federations, witnesses,
//! checkpoint, note, proof, factory, search, stats, recent, watch, unwatch.
//!
//! Every read hits the **real** node surface through the shared `DevnetClient`
//! (its modelled methods, or `state.devnet.client()` for routes the shared
//! client doesn't model yet — `/api/blocklace/blocks`, `/api/federations`,
//! `/api/receipts/{hash}/witnesses`, `/checkpoint/latest`). Nothing here
//! reimplements a node query.

use serde::Deserialize;
use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Real node read shapes for routes the shared client doesn't model yet ────

#[derive(Debug, Clone, Deserialize)]
struct BlockViewWire {
    #[serde(default)]
    height: u64,
    #[serde(default)]
    view: u64,
    #[serde(default)]
    #[allow(dead_code)] // Deserialized from the block-view wire but not rendered.
    proposer: String,
    #[serde(default)]
    block_hash: String,
    #[serde(default)]
    predecessors: Vec<String>,
    #[serde(default)]
    num_votes: usize,
    #[serde(default)]
    qc_threshold: usize,
    #[serde(default)]
    kind: String,
    #[serde(default)]
    finality_round: Option<u64>,
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
    members: Vec<String>,
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
struct WitnessesWire {
    #[serde(default)]
    receipt_hash: String,
    #[serde(default)]
    witness_count: usize,
    #[serde(default)]
    artifact_format: String,
    #[serde(default)]
    witness_artifacts: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct CheckpointWire {
    #[serde(default)]
    height: u64,
    #[serde(default)]
    ledger_state_root: String,
    #[serde(default)]
    note_tree_root: String,
    #[serde(default)]
    nullifier_set_root: String,
    #[serde(default)]
    revocation_tree_root: String,
    #[serde(default)]
    epoch: u64,
    #[serde(default)]
    timestamp: i64,
    #[serde(default)]
    federation_members: usize,
    #[serde(default)]
    qc_votes: usize,
}

/// GET a JSON route off the real node via the shared client, returning a framed
/// error string on any failure. `route` is the path (e.g. "/api/federations").
async fn node_get_json<T: for<'de> Deserialize<'de>>(
    state: &BotState,
    route: &str,
) -> Result<T, String> {
    let url = format!("{}{route}", state.config.devnet_url.trim_end_matches('/'));
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
    resp.json::<T>()
        .await
        .map_err(|e| format!("could not parse {route}: {e}"))
}

/// Register the /explorer command with all subcommands.
pub fn register() -> CreateCommand {
    CreateCommand::new("explorer")
        .description("Browse devnet state · cells, turns, blocks, stats, activity")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "feed",
                "Set the channel for the activity feed",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Channel,
                    "channel",
                    "Channel to post activity to",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "cell",
                "Look up a cell by ID",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "cell_id",
                    "Cell ID to look up",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "turn",
                "Look up a turn by hash",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "turn_hash",
                    "Turn hash to look up",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "block",
                "Look up a block by height",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "height", "Block height")
                    .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "blocklace",
                "Browse recent blocks in the consensus DAG (blocklace)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "count",
                    "Number of recent DAG blocks to show (default 8, max 20)",
                )
                .required(false),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "federations",
            "List the federations this node tracks (epoch, threshold, roots)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "checkpoint",
            "Show the latest finalized state checkpoint (the four roots)",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "witnesses",
                "Show the witness artifacts attached to a committed receipt",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "receipt_hash",
                    "Receipt hash (64 hex) of a committed turn",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "note",
                "Look up a note by commitment",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "commitment",
                    "Note commitment",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "proof",
                "Fetch the proof artifact attached to a committed turn",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::String, "hash", "Turn hash (64 hex)")
                    .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "factory",
                "Look up a factory by VK hash",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "vk_hash",
                    "Factory verification key hash",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "search",
                "Search by partial cell_id, turn_hash, or commitment",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "query",
                    "Search query (prefix match)",
                )
                .required(true),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "stats",
            "Show current devnet stats dashboard",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "recent",
                "Show recent activity",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::Integer,
                    "count",
                    "Number of events to show (default 5, max 20)",
                )
                .required(false),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::User,
                    "user",
                    "Filter to a specific user's cell activity",
                )
                .required(false),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "watch",
                "Get DM'd on activity for a cell",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::String, "cell_id", "Cell ID to watch")
                    .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "unwatch",
                "Stop watching a cell",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "cell_id",
                    "Cell ID to stop watching",
                )
                .required(true),
            ),
        )
}

/// Handle /explorer interactions — dispatch to the appropriate subcommand handler.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "feed" => handle_feed(ctx, command, state).await,
        "cell" => handle_cell(ctx, command, state).await,
        "turn" => handle_turn(ctx, command, state).await,
        "block" => handle_block(ctx, command, state).await,
        "blocklace" => handle_blocklace(ctx, command, state).await,
        "federations" => handle_federations(ctx, command, state).await,
        "checkpoint" => handle_checkpoint(ctx, command, state).await,
        "witnesses" => handle_witnesses(ctx, command, state).await,
        "note" => handle_note(ctx, command, state).await,
        "proof" => handle_proof(ctx, command, state).await,
        "factory" => handle_factory(ctx, command, state).await,
        "search" => handle_search(ctx, command, state).await,
        "stats" => handle_stats(ctx, command, state).await,
        "recent" => handle_recent(ctx, command, state).await,
        "watch" => handle_watch(ctx, command, state).await,
        "unwatch" => handle_unwatch(ctx, command, state).await,
        _ => {}
    }
}

// ─── Subcommand handlers ────────────────────────────────────────────────────

async fn handle_feed(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);

    let channel_id = options
        .iter()
        .find(|o| o.name == "channel")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Channel(c) => Some(c.get().to_string()),
            _ => None,
        })
        .unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(gid) => gid.get().to_string(),
        None => {
            respond_ephemeral(
                ctx,
                command,
                embeds::error_embed("Error", "This command can only be used in a server."),
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    match state.db.set_feed_channel(&guild_id, &channel_id).await {
        Ok(()) => {
            let embed = embeds::success_embed("Activity Feed Configured")
                .description(format!(
                    "Activity feed will post to <#{channel_id}>.\n\nNew turns, auctions, swaps, and other events will appear there automatically."
                ));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::store_unavailable_embed(&e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_cell(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let cell_id = get_string_option(&options, "cell_id");

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_cell_details(&cell_id).await {
        Ok(cell) => {
            let short_id = truncate(&cell.cell_id, 16);
            let short_vk = cell
                .program_vk
                .as_deref()
                .map(|v| truncate(v, 16))
                .unwrap_or_else(|| "None".to_string());

            let embed = embeds::dregg_embed("Cell Details")
                .field("Cell ID", format!("`{short_id}...`"), false)
                .field("Mode", &cell.mode, true)
                .field("Balance", format!("{} DEC", cell.balance), true)
                .field("Nonce", cell.nonce.to_string(), true)
                .field("Capabilities", cell.capabilities_count.to_string(), true)
                .field("Program VK", format!("`{short_vk}`"), true)
                .field(
                    "Provenance",
                    cell.provenance.as_deref().unwrap_or("None"),
                    true,
                )
                .field(
                    "Created By",
                    cell.created_by_factory
                        .as_deref()
                        .map(|f| format!("`{}`", truncate(f, 12)))
                        .unwrap_or_else(|| "Direct".to_string()),
                    true,
                )
                .field(
                    "Explorer",
                    crate::explorer_link::view_link("cell", &cell.cell_id, "View"),
                    false,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed =
                embeds::error_embed("Cell Lookup Failed", &e.user_message("look up the cell"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_turn(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let turn_hash = get_string_option(&options, "turn_hash");

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_turn_details(&turn_hash).await {
        Ok(turn) => {
            let short_hash = truncate(&turn.turn_hash, 16);
            let short_signer = truncate(&turn.signer, 16);

            let effects_str: String = turn
                .effects
                .iter()
                .take(10)
                .map(|e| format!("- **{}**: {}", e.effect_type, e.details))
                .collect::<Vec<_>>()
                .join("\n");

            let embed = embeds::dregg_embed("Turn Details")
                .field("Hash", format!("`{short_hash}...`"), false)
                .field("Signer", format!("`{short_signer}...`"), true)
                .field("Fee", format!("{} DEC", turn.fee), true)
                .field("Result", &turn.result, true)
                .field("Proof Type", &turn.proof_type, true)
                .field(
                    "Effects",
                    if effects_str.is_empty() {
                        "None".to_string()
                    } else {
                        effects_str
                    },
                    false,
                )
                .field(
                    "Explorer",
                    crate::explorer_link::view_link("turn", &turn.turn_hash, "View"),
                    false,
                )
                .field(
                    "Turn hash (full, copyable)",
                    format!("```\n{}\n```", turn.turn_hash),
                    false,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed =
                embeds::error_embed("Turn Lookup Failed", &e.user_message("look up the turn"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_block(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let height = options
        .iter()
        .find(|o| o.name == "height")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        })
        .unwrap_or(0);

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_block_details(height).await {
        Ok(block) => {
            let short_root = truncate(&block.root_hash, 16);

            let tx_list: String = if block.transactions.is_empty() {
                "None".to_string()
            } else {
                block
                    .transactions
                    .iter()
                    .take(10)
                    .map(|t| format!("`{}`", truncate(t, 12)))
                    .collect::<Vec<_>>()
                    .join(", ")
            };

            let embed = embeds::dregg_embed(&format!("Block #{}", block.height))
                .field("Height", block.height.to_string(), true)
                .field("Timestamp", &block.timestamp, true)
                .field("Proposer", truncate(&block.proposer, 16), true)
                .field("Root Hash", format!("`{short_root}...`"), false)
                .field(
                    "Transactions",
                    format!("{} total: {}", block.transactions.len(), tx_list),
                    false,
                )
                .field(
                    "Explorer",
                    crate::explorer_link::view_link("block", &block.height.to_string(), "View"),
                    false,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed =
                embeds::error_embed("Block Lookup Failed", &e.user_message("look up the block"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_blocklace(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let count = options
        .iter()
        .find(|o| o.name == "count")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some((*n as usize).clamp(1, 20)),
            _ => None,
        })
        .unwrap_or(8);

    defer_ephemeral(ctx, command).await;

    match node_get_json::<Vec<BlockViewWire>>(state, "/api/blocklace/blocks").await {
        Ok(mut blocks) => {
            if blocks.is_empty() {
                let embed = embeds::warning_embed(
                    "No DAG Blocks",
                    "The node reports an empty blocklace. Consensus may not be running on this node.",
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            // Newest first.
            blocks.sort_by_key(|b| std::cmp::Reverse(b.height));
            let total = blocks.len();
            let mut desc = String::new();
            for block in blocks.iter().take(count) {
                let final_mark = match block.finality_round {
                    Some(round) => format!("\u{2705} final (r{round})"),
                    None => "\u{231b} pending".to_string(),
                };
                desc.push_str(&format!(
                    "{} **#{}** `{}` · {} · {} pred · {}/{} votes · {}\n",
                    kind_icon(&block.kind),
                    block.height,
                    truncate(&block.block_hash, 12),
                    if block.kind.is_empty() {
                        "block"
                    } else {
                        &block.kind
                    },
                    block.predecessors.len(),
                    block.num_votes,
                    block.qc_threshold,
                    final_mark,
                ));
                let _ = block.view; // view is carried by the wire shape; height is the user-facing index
            }

            let embed = embeds::dregg_embed("Blocklace (consensus DAG)")
                .description(desc)
                .field("Local DAG Blocks", total.to_string(), true)
                .field("Showing", count.min(total).to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Blocklace Unavailable", &e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_federations(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match node_get_json::<Vec<FederationInfoWire>>(state, "/api/federations").await {
        Ok(feds) => {
            if feds.is_empty() {
                let embed =
                    embeds::warning_embed("No Federations", "The node tracks no federations yet.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            let mut embed = embeds::dregg_embed("Federations")
                .description("Federations this node tracks. \u{2b50} marks the local federation.");
            for fed in feds.iter().take(8) {
                let root = fed
                    .latest_root
                    .as_deref()
                    .map(|r| truncate(r, 16))
                    .unwrap_or_else(|| "none".to_string());
                let title = format!(
                    "{} {}",
                    if fed.is_local {
                        "\u{2b50}"
                    } else {
                        "\u{1f517}"
                    },
                    truncate(&fed.id, 16)
                );
                embed = embed.field(
                    title,
                    format!(
                        "epoch {} · threshold {}/{} · {} members · h{} · {} finalized roots\nlatest root: `{}`",
                        fed.committee_epoch,
                        fed.threshold,
                        fed.member_count,
                        fed.members.len().max(fed.member_count),
                        fed.latest_height,
                        fed.num_finalized_roots,
                        root,
                    ),
                    false,
                );
            }
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Federations Unavailable", &e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_checkpoint(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match node_get_json::<CheckpointWire>(state, "/checkpoint/latest").await {
        Ok(cp) => {
            let embed = embeds::dregg_embed("Latest Finalized Checkpoint")
                .description(
                    "The four authenticated roots that pin global state at this finalized height.",
                )
                .field("Height", cp.height.to_string(), true)
                .field("Epoch", cp.epoch.to_string(), true)
                .field(
                    "QC Votes",
                    format!("{}/{}", cp.qc_votes, cp.federation_members),
                    true,
                )
                .field(
                    "Ledger State Root",
                    format!("`{}...`", truncate(&cp.ledger_state_root, 24)),
                    false,
                )
                .field(
                    "Note Tree Root",
                    format!("`{}...`", truncate(&cp.note_tree_root, 24)),
                    false,
                )
                .field(
                    "Nullifier Set Root",
                    format!("`{}...`", truncate(&cp.nullifier_set_root, 24)),
                    false,
                )
                .field(
                    "Revocation Tree Root",
                    format!("`{}...`", truncate(&cp.revocation_tree_root, 24)),
                    false,
                )
                .field("Timestamp", cp.timestamp.to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::warning_embed(
                "No Checkpoint",
                &format!(
                    "Could not load the latest checkpoint: {e}\n\nA fresh node may not have finalized one yet."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_witnesses(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let receipt_hash = get_string_option(&options, "receipt_hash");
    let receipt_hash = receipt_hash.trim().to_string();

    defer_ephemeral(ctx, command).await;

    if receipt_hash.len() != 64 || hex::decode(&receipt_hash).is_err() {
        let embed = embeds::error_embed(
            "Invalid Receipt Hash",
            "Provide a 64-hex receipt hash (find one via `/explorer recent`).",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let route = format!("/api/receipts/{receipt_hash}/witnesses");
    match node_get_json::<WitnessesWire>(state, &route).await {
        Ok(w) => {
            if w.witness_count == 0 && w.witness_artifacts.is_empty() {
                let embed = embeds::warning_embed(
                    "No Witnesses",
                    &format!(
                        "Receipt `{}...` has no witness artifacts on record (unknown hash, or a turn that committed without witnesses).",
                        truncate(&receipt_hash, 16)
                    ),
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            let mut desc = String::new();
            for (i, art) in w.witness_artifacts.iter().take(6).enumerate() {
                desc.push_str(&format!(
                    "`#{i}` `{}...` ({} bytes)\n",
                    truncate(art, 24),
                    art.len() / 2
                ));
            }
            let embed = embeds::dregg_embed("Receipt Witnesses")
                .field(
                    "Receipt",
                    format!("`{}...`", truncate(&w.receipt_hash, 16)),
                    false,
                )
                .field("Witness Count", w.witness_count.to_string(), true)
                .field(
                    "Artifact Format",
                    if w.artifact_format.is_empty() {
                        "n/a".to_string()
                    } else {
                        w.artifact_format
                    },
                    true,
                )
                .field(
                    "Artifacts (head)",
                    if desc.is_empty() {
                        "none".to_string()
                    } else {
                        desc
                    },
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Witnesses Unavailable", &e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_note(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let commitment = get_string_option(&options, "commitment");

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_note_status(&commitment).await {
        Ok(note) => {
            let short_commitment = truncate(&note.commitment, 16);
            let status_icon = if note.status == "unspent" {
                "\u{2705}" // check
            } else {
                "\u{274c}" // cross
            };

            let embed = embeds::dregg_embed("Note Status")
                .field("Commitment", format!("`{short_commitment}...`"), false)
                .field("Status", format!("{status_icon} {}", note.status), true)
                .field(
                    "Nullifier",
                    if note.nullifier_exists {
                        "Exists (spent)"
                    } else {
                        "Not found (unspent)"
                    },
                    true,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Note Lookup Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
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

impl TurnProofWire {
    fn has_validity_artifact(&self) -> bool {
        self.proof_status != "not_required"
            && self.proof_hex.as_ref().is_some_and(|p| !p.is_empty())
    }
}

async fn handle_proof(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let hash = get_string_option(&options, "hash");
    let hash = hash.trim().to_string();

    defer_ephemeral(ctx, command).await;

    // The real proof surface is keyed by a committed *turn* hash.
    if hash.len() != 64 || hex::decode(&hash).is_err() {
        let embed = embeds::error_embed(
            "Invalid Hash",
            "Provide the 64-hex hash of a committed turn (find one via `/explorer recent`).",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let url = format!(
        "{}/api/turn/{hash}/proof",
        state.config.devnet_url.trim_end_matches('/')
    );
    let resp = match state.devnet.client().get(&url).send().await {
        Ok(resp) => resp,
        Err(e) => {
            let embed = embeds::error_embed(
                "Node Unreachable",
                &format!("Could not fetch the proof: {e}"),
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
                "Turn `{}...` has no proof artifact (unknown hash, or it committed on the executor-signed-receipt path; see `/status`).",
                truncate(&hash, 16)
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
            if !proof.has_validity_artifact() {
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
            // ⚑ THE ANCHOR FIRST, AND IT IS REQUIRED — the same forcing shape `/proof turn`
            // takes. No committee-signed anchor, no verdict; see `proof_verify`'s docblock.
            let anchor = match crate::commands::proof_verify::fetch_and_verify_anchor(
                state.devnet.client(),
                &state.config.devnet_url,
                &hash,
            )
            .await
            {
                Ok(anchor) => anchor,
                Err(why) => {
                    let embed = embeds::warning_embed(
                        "Turn Proof Artifact · NO VERDICT (unanchored)",
                        &crate::commands::proof_verify::no_anchor_text(&hash, &why),
                    );
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };
            // VERIFY the fetched artifact right here (the audited `verify_full_turn`) against
            // the turn hash the COMMITTEE signed AND the state-commit pair the node derived at
            // commit time, and report the verdict — never an "Attached ✅" trust-me. Every seam
            // is in the Verification field below.
            let check =
                crate::commands::proof_verify::check_proof_hex_blocking(proof_hex.clone(), anchor)
                    .await;
            // THREE outcomes, not two. `Err` is a REFUSAL (no bindable pair to judge against) and
            // must not be painted as "the bytes failed" — that reads as evidence against the
            // artifact when it is evidence about what this bot could obtain.
            let base = match &check {
                Ok(c) if c.verified => embeds::dregg_embed(
                    "Turn Proof Artifact · legs verify, bound to the committee-signed turn and the \
                     node's derived state commits",
                ),
                Ok(_) => embeds::error_embed(
                    "Turn Proof Artifact · DOES NOT VERIFY",
                    "The fetched bytes failed the bot's own re-check.",
                ),
                Err(_) => embeds::warning_embed(
                    "Turn Proof Artifact · NO VERDICT",
                    "This bot could not obtain values to judge the artifact against.",
                ),
            };
            let embed = base
                .field(
                    "Turn",
                    format!("`{}...`", truncate(&proof.turn_hash, 16)),
                    false,
                )
                .field(
                    "Proof Size",
                    format!("{} bytes ({kib:.1} KiB)", proof.proof_len),
                    true,
                )
                .field(
                    "Proof (head)",
                    format!("`{}...`", truncate(proof_hex, 32)),
                    false,
                )
                .field(
                    "Verification",
                    crate::commands::proof_verify::verdict_text(&check),
                    false,
                )
                .field(
                    "Re-check it yourself",
                    crate::commands::proof_verify::offline_recheck_text(
                        &state.config.devnet_url,
                        &hash,
                    ),
                    false,
                )
                .field(
                    "Explorer",
                    crate::explorer_link::view_link("turn", &hash, "View turn"),
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

async fn handle_factory(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let vk_hash = get_string_option(&options, "vk_hash");

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_factory_details(&vk_hash).await {
        Ok(factory) => {
            let short_vk = truncate(&factory.vk_hash, 16);

            let embed = embeds::dregg_embed("Factory Details")
                .field("VK Hash", format!("`{short_vk}...`"), false)
                .field("Descriptor", &factory.descriptor, false)
                .field(
                    "Creation Budget",
                    format!("{} DEC", factory.creation_budget),
                    true,
                )
                .field("Cells Created", factory.cells_created.to_string(), true)
                .field("VK Strategy", &factory.vk_strategy, true);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Factory Lookup Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_search(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let query = get_string_option(&options, "query");

    defer_ephemeral(ctx, command).await;

    match state.devnet.explorer_search(&query).await {
        Ok(results) => {
            if results.is_empty() {
                let embed = embeds::warning_embed(
                    "No Results",
                    &format!("No matches found for `{query}`."),
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for result in results.iter().take(10) {
                description.push_str(&format!(
                    "**{}** {}\n{}\n\n",
                    result.kind,
                    crate::explorer_link::short_ref(&result.kind, &result.id, 16),
                    result.summary
                ));
            }

            let embed = embeds::dregg_embed(&format!("Search: {query}"))
                .description(description)
                .field("Results", results.len().to_string(), true);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Search Failed", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_stats(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.explorer_stats().await {
        Ok(stats) => {
            let federation_health = if stats.federation_nodes_up == stats.federation_nodes_total {
                "\u{2705} Healthy"
            } else if stats.federation_nodes_up > stats.federation_nodes_total / 2 {
                "\u{26a0}\u{fe0f} Degraded"
            } else {
                "\u{274c} Critical"
            };

            let embed = embeds::dregg_embed("Devnet Stats Dashboard")
                .field("Block Height", format!("{}", stats.block_height), true)
                .field(
                    "Cells",
                    format!(
                        "{} hosted / {} sovereign",
                        stats.total_cells_hosted, stats.total_cells_sovereign
                    ),
                    true,
                )
                .field(
                    "Notes",
                    format!(
                        "{} spent / {} unspent",
                        stats.total_notes_spent, stats.total_notes_unspent
                    ),
                    true,
                )
                .field("Turns (epoch)", stats.turns_this_epoch.to_string(), true)
                .field("Active Auctions", stats.active_auctions.to_string(), true)
                .field(
                    "Federation",
                    format!(
                        "{} ({}/{})",
                        federation_health, stats.federation_nodes_up, stats.federation_nodes_total
                    ),
                    true,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Stats Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_recent(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);

    let count = options
        .iter()
        .find(|o| o.name == "count")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some((*n as u32).clamp(1, 20)),
            _ => None,
        })
        .unwrap_or(5);

    // Check if filtering by user.
    let user_cell_id = if let Some(opt) = options.iter().find(|o| o.name == "user") {
        if let CommandDataOptionValue::User(uid) = &opt.value {
            let discord_id = uid.get().to_string();
            state.db.get_cell_id(&discord_id).await.ok().flatten()
        } else {
            None
        }
    } else {
        None
    };

    defer_ephemeral(ctx, command).await;

    match state
        .devnet
        .get_recent_events(count, user_cell_id.as_deref())
        .await
    {
        Ok(events) => {
            if events.is_empty() {
                let embed =
                    embeds::dregg_embed("Recent Activity").description("No recent activity found.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for event in &events {
                let icon = event_icon(&event.event_type);
                description.push_str(&format!(
                    "{icon} **{}** · {}\n",
                    event.event_type, event.summary
                ));
                if let Some(tx) = &event.tx_hash {
                    // Linked when DREGG_EXPLORER_BASE is configured; plain copyable
                    // full hash otherwise — never a dead link.
                    description.push_str(&format!(
                        "  {}\n",
                        crate::explorer_link::short_ref("tx", tx, 12)
                    ));
                }
            }

            let embed = embeds::dregg_embed("Recent Activity")
                .description(description)
                .field("Showing", format!("{} events", events.len()), true);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Recent Activity Error",
                &e.user_message("read recent activity"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_watch(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let cell_id = get_string_option(&options, "cell_id");
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    match state.db.add_watch(&discord_id, &cell_id).await {
        Ok(true) => {
            let short = truncate(&cell_id, 16);
            let embed = embeds::success_embed("Watch Added").description(format!(
                "You will be DM'd when cell `{short}...` has activity.\n\nUse `/explorer unwatch` to stop."
            ));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(false) => {
            let embed =
                embeds::warning_embed("Already Watching", "You are already watching this cell.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::store_unavailable_embed(&e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_unwatch(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let cell_id = get_string_option(&options, "cell_id");
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    match state.db.remove_watch(&discord_id, &cell_id).await {
        Ok(true) => {
            let short = truncate(&cell_id, 16);
            let embed = embeds::success_embed("Watch Removed")
                .description(format!("Stopped watching cell `{short}...`."));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(false) => {
            let embed = embeds::warning_embed("Not Watching", "You were not watching this cell.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::store_unavailable_embed(&e);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Extract suboption values from the first option (which is the subcommand).
fn get_sub_options(command: &CommandInteraction) -> Vec<serenity::all::CommandDataOption> {
    match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => Vec::new(),
    }
}

/// Get a string option value by name.
fn get_string_option(options: &[serenity::all::CommandDataOption], name: &str) -> String {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default()
}

/// Truncate a string to `max_len` characters.
fn truncate(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        s[..max_len].to_string()
    }
}

/// Get the icon for an event type.
fn event_icon(event_type: &str) -> &'static str {
    match event_type.to_lowercase().as_str() {
        s if s.contains("transfer") || s.contains("settlement") || s.contains("settled") => {
            "\u{1f7e2}" // green circle
        }
        s if s.contains("cell") || s.contains("register") || s.contains("sovereign") => {
            "\u{1f535}" // blue circle
        }
        s if s.contains("auction") || s.contains("order") || s.contains("swap") => {
            "\u{1f7e1}" // yellow circle
        }
        s if s.contains("liquidat") || s.contains("slash") => {
            "\u{1f534}" // red circle
        }
        _ => "\u{26aa}", // white circle
    }
}

/// Icon for a blocklace block kind.
fn kind_icon(kind: &str) -> &'static str {
    match kind {
        "turn" | "turn_bundle" => "\u{1f7e2}", // green: state-advancing
        "heartbeat" => "\u{1f499}",            // blue heart: liveness
        "checkpoint" => "\u{1f4cd}",           // pin: finalization
        "membership" => "\u{1f465}",           // people: committee change
        "data" => "\u{1f4e6}",                 // package
        _ => "\u{26aa}",                       // white circle
    }
}

/// Defer the response as ephemeral.
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

/// Send an ephemeral embed response.
async fn respond_ephemeral(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

#[cfg(test)]
mod coordination_policy_tests {
    use super::TurnProofWire;
    #[test]
    fn signature_only_response_never_reaches_proof_verification() {
        for hex in [serde_json::Value::Null, serde_json::json!("abcd")] {
            let response: TurnProofWire = serde_json::from_value(serde_json::json!({
                "turn_hash": "00", "proof_status": "not_required", "proof_hex": hex
            }))
            .unwrap();
            assert!(!response.has_validity_artifact());
        }
        let response: TurnProofWire = serde_json::from_value(serde_json::json!({
            "turn_hash": "00", "proof_status": "proved", "proof_hex": "abcd"
        }))
        .unwrap();
        assert!(response.has_validity_artifact());
    }
}
