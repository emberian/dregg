//! `/explorer` command — browse devnet state from Discord.
//!
//! Subcommands: feed, cell, turn, block, note, proof, factory, search, stats, recent, watch, unwatch.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

/// Register the /explorer command with all subcommands.
pub fn register() -> CreateCommand {
    CreateCommand::new("explorer")
        .description("Browse devnet state — cells, turns, blocks, stats, activity")
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
                "Look up proof metadata by hash",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::String, "hash", "Proof hash")
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
            let embed = embeds::error_embed("Database Error", &e.to_string());
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
            let explorer_url =
                format!("{}/cell/{}", state.devnet.explorer_base_url(), cell.cell_id);
            let short_id = truncate(&cell.cell_id, 16);
            let short_vk = cell
                .program_vk
                .as_deref()
                .map(|v| truncate(v, 16))
                .unwrap_or_else(|| "None".to_string());

            let embed = embeds::pyana_embed("Cell Details")
                .field("Cell ID", format!("`{short_id}...`"), false)
                .field("Mode", &cell.mode, true)
                .field("Balance", format!("{} PYN", cell.balance), true)
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
                .field("Explorer", format!("[View]({explorer_url})"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Cell Lookup Failed", &e.to_string());
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
            let explorer_url = format!(
                "{}/turn/{}",
                state.devnet.explorer_base_url(),
                turn.turn_hash
            );
            let short_hash = truncate(&turn.turn_hash, 16);
            let short_signer = truncate(&turn.signer, 16);

            let effects_str: String = turn
                .effects
                .iter()
                .take(10)
                .map(|e| format!("- **{}**: {}", e.effect_type, e.details))
                .collect::<Vec<_>>()
                .join("\n");

            let embed = embeds::pyana_embed("Turn Details")
                .field("Hash", format!("`{short_hash}...`"), false)
                .field("Signer", format!("`{short_signer}...`"), true)
                .field("Fee", format!("{} PYN", turn.fee), true)
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
                .field("Explorer", format!("[View]({explorer_url})"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Turn Lookup Failed", &e.to_string());
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
            let explorer_url = format!(
                "{}/block/{}",
                state.devnet.explorer_base_url(),
                block.height
            );
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

            let embed = embeds::pyana_embed(&format!("Block #{}", block.height))
                .field("Height", block.height.to_string(), true)
                .field("Timestamp", &block.timestamp, true)
                .field("Proposer", truncate(&block.proposer, 16), true)
                .field("Root Hash", format!("`{short_root}...`"), false)
                .field(
                    "Transactions",
                    format!("{} total: {}", block.transactions.len(), tx_list),
                    false,
                )
                .field("Explorer", format!("[View]({explorer_url})"), false);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Block Lookup Failed", &e.to_string());
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

            let embed = embeds::pyana_embed("Note Status")
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

async fn handle_proof(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let options = get_sub_options(command);
    let hash = get_string_option(&options, "hash");

    defer_ephemeral(ctx, command).await;

    match state.devnet.get_proof_details(&hash).await {
        Ok(proof) => {
            let short_hash = truncate(&proof.hash, 16);
            let verified_icon = if proof.verified {
                "\u{2705}"
            } else {
                "\u{274c}"
            };

            let embed = embeds::pyana_embed("Proof Metadata")
                .field("Hash", format!("`{short_hash}...`"), false)
                .field("AIR", &proof.air_name, true)
                .field("Trace Size", proof.trace_size.to_string(), true)
                .field("Public Inputs", proof.public_inputs_count.to_string(), true)
                .field(
                    "Verified",
                    format!("{verified_icon} {}", proof.verified),
                    true,
                );

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Proof Lookup Failed", &e.to_string());
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

            let embed = embeds::pyana_embed("Factory Details")
                .field("VK Hash", format!("`{short_vk}...`"), false)
                .field("Descriptor", &factory.descriptor, false)
                .field(
                    "Creation Budget",
                    format!("{} PYN", factory.creation_budget),
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
                let short_id = truncate(&result.id, 16);
                let explorer_url = format!(
                    "{}/{}/{}",
                    state.devnet.explorer_base_url(),
                    result.kind,
                    result.id
                );
                description.push_str(&format!(
                    "**{}** [`{short_id}...`]({explorer_url})\n{}\n\n",
                    result.kind, result.summary
                ));
            }

            let embed = embeds::pyana_embed(&format!("Search: {query}"))
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

            let embed = embeds::pyana_embed("Devnet Stats Dashboard")
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
                .field("AMM TVL", format!("{} PYN", stats.amm_tvl), true)
                .field("Active Orders", stats.active_orders.to_string(), true)
                .field("Open CDPs", stats.open_cdps.to_string(), true)
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
            CommandDataOptionValue::Integer(n) => Some((*n as u32).min(20).max(1)),
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
                    embeds::pyana_embed("Recent Activity").description("No recent activity found.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for event in &events {
                let icon = event_icon(&event.event_type);
                description.push_str(&format!(
                    "{icon} **{}** — {}\n",
                    event.event_type, event.summary
                ));
                if let Some(tx) = &event.tx_hash {
                    let short = truncate(tx, 12);
                    description.push_str(&format!(
                        "  [`{short}...`](https://devnet.pyana.fg-goose.online/explorer/tx/{tx})\n"
                    ));
                }
            }

            let embed = embeds::pyana_embed("Recent Activity")
                .description(description)
                .field("Showing", format!("{} events", events.len()), true);

            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Recent Activity Error", &e.to_string());
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
            let embed = embeds::error_embed("Database Error", &e.to_string());
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
            let embed = embeds::error_embed("Database Error", &e.to_string());
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
