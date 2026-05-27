//! Name service commands: `/name-register`, `/name-resolve`, `/name-whois`.
//!
//! Guild-scoped namespace registration and resolution via the dregg governed namespace.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dregg_app_framework::{CellId, field_from_bytes};
use starbridge_nameservice::{build_register_action, build_set_target_action};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::{IdentityMode, StarbridgeActivity};
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/name-register <name> <registry-cell> <expiry-height> [target]`.
pub fn register_register() -> CreateCommand {
    CreateCommand::new("name-register")
        .description("Register a name in the guild's namespace")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Name to register")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "registry-cell",
                "Nameservice registry cell ID (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "expiry-height",
                "Rent expiry block height",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "target",
                "Optional resolve target URI to hash into the target slot",
            )
            .required(false),
        )
}

/// Register `/name-resolve <name>`.
pub fn register_resolve() -> CreateCommand {
    CreateCommand::new("name-resolve")
        .description("Explain nameservice resolve read status")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "name", "Name to resolve")
                .required(true),
        )
}

/// Register `/name-whois <cell-id>`.
pub fn register_whois() -> CreateCommand {
    CreateCommand::new("name-whois")
        .description("Explain nameservice reverse lookup read status")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "cell-id", "Cell ID to look up")
                .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/name-register`.
pub async fn handle_register(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();
    let registry_cell_hex =
        get_string_option(&command.data.options, "registry-cell").unwrap_or_default();
    let target = get_string_option(&command.data.options, "target").unwrap_or_default();
    let expiry_height = match get_integer_option(&command.data.options, "expiry-height") {
        Some(value) if value >= 0 => value as u64,
        _ => {
            respond_warning(
                ctx,
                command,
                "Invalid Expiry",
                "Expiry height must be an unsigned integer.",
            )
            .await;
            return;
        }
    };

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Name service commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let owner = match hosted_user_cell(command.user.id.get(), state).await {
        Ok(cell) => cell,
        Err(embed) => {
            edit_embed(ctx, command, embed).await;
            return;
        }
    };
    let owner_bytes = match parse_cell_bytes(&owner) {
        Ok(bytes) => bytes,
        Err(msg) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Invalid Owner Cell", &msg),
            )
            .await;
            return;
        }
    };
    let registry_cell = match parse_cell_id(&registry_cell_hex) {
        Ok(cell) => cell,
        Err(msg) => {
            edit_embed(
                ctx,
                command,
                embeds::warning_embed("Invalid Registry Cell", &msg),
            )
            .await;
            return;
        }
    };

    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        command.user.id.get(),
        state.federation_id_bytes,
    );
    let mut actions = vec![build_register_action(
        &cclerk.app,
        registry_cell,
        &name,
        owner_bytes,
        expiry_height,
    )];
    if !target.trim().is_empty() {
        actions.push(build_set_target_action(
            &cclerk.app,
            registry_cell,
            &name,
            field_from_bytes(target.as_bytes()),
        ));
    }

    let embed = match state
        .devnet
        .submit_app_actions(
            &cclerk,
            actions,
            Some(format!(
                "discord:nameservice:register:guild:{guild_id}:{name}"
            )),
        )
        .await
    {
        Ok(result) if result.accepted => {
            let turn_hash = result.turn_hash.clone();
            let _ = state
                .db
                .record_starbridge_activity(
                    "nameservice",
                    "register",
                    &command.user.id.get().to_string(),
                    Some(&guild_id.to_string()),
                    Some(&name),
                    "accepted",
                    serde_json::json!({
                        "name": name,
                        "owner": owner,
                        "registry": registry_cell_hex,
                        "expiry_height": expiry_height,
                        "target": if target.trim().is_empty() { None::<String> } else { Some(target.trim().to_string()) },
                        "turn_hash": turn_hash,
                    }),
                )
                .await;

            embeds::success_embed("Name Registered")
                .field("Name", name, true)
                .field("Owner", short_cell(&owner), true)
                .field("Registry", short_cell(&registry_cell_hex), true)
                .field("Expiry Height", expiry_height.to_string(), true)
                .field("Turn", turn_hash_field(result.turn_hash), false)
        }
        Ok(result) => embeds::error_embed(
            "Registration Rejected",
            result
                .error
                .as_deref()
                .unwrap_or("node rejected the signed nameservice action"),
        ),
        Err(e) => embeds::error_embed("Registration Failed", &e.to_string()),
    };
    edit_embed(ctx, command, embed).await;
}

/// Handle `/name-resolve`.
pub async fn handle_resolve(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let name = get_string_option(&command.data.options, "name").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Name service commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;
    let embed = nameservice_read_embed(state, NameserviceRead::Resolve { guild_id, name }).await;
    edit_embed(ctx, command, embed).await;
}

/// Handle `/name-whois`.
pub async fn handle_whois(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = get_string_option(&command.data.options, "cell-id").unwrap_or_default();

    if command.guild_id.is_none() {
        respond_error(
            ctx,
            command,
            "Guild Required",
            "Name service commands must be run in a server.",
        )
        .await;
        return;
    }

    defer_ephemeral(ctx, command).await;
    let embed = nameservice_read_embed(state, NameserviceRead::Whois { cell_id }).await;
    edit_embed(ctx, command, embed).await;
}

// ─── Helpers ────────────────────────────────────────────────────────────────

enum NameserviceRead {
    Resolve { guild_id: u64, name: String },
    Whois { cell_id: String },
}

async fn nameservice_read_embed(state: &BotState, read: NameserviceRead) -> CreateEmbed {
    let activities = state
        .db
        .get_recent_starbridge_activity_for_app("nameservice", 50)
        .await
        .unwrap_or_default();
    let events = state
        .devnet
        .get_recent_events(25, None)
        .await
        .unwrap_or_default();

    match read {
        NameserviceRead::Resolve { guild_id, name } => {
            let matches: Vec<_> = activities
                .iter()
                .filter(|activity| {
                    activity.action == "register"
                        && activity.guild_id.as_deref() == Some(&guild_id.to_string())
                        && activity.subject.as_deref() == Some(name.as_str())
                })
                .take(3)
                .collect();
            let mut embed = if let Some(activity) = matches.first() {
                let details = activity_details(activity);
                embeds::success_embed("Recent Name Registration")
                    .field("Name", format!("`{name}`"), true)
                    .field("Namespace", format!("`/discord/{guild_id}/`"), true)
                    .field("Owner", detail_cell(&details, "owner"), true)
                    .field("Registry", detail_cell(&details, "registry"), true)
                    .field(
                        "Expiry Height",
                        detail_string(&details, "expiry_height"),
                        true,
                    )
                    .field("Target", detail_string(&details, "target"), true)
                    .field("Turn", detail_turn(&details), false)
            } else {
                embeds::warning_embed(
                    "No Recent Local Registration",
                    &format!(
                        "No bot-recorded registration for `{name}` in `/discord/{guild_id}/`. The node still does not expose a nameservice slot/index read, so this is a recent activity lookup, not canonical resolution."
                    ),
                )
            };

            let event_lines = recent_nameservice_event_lines(&events, Some(&name));
            if !event_lines.is_empty() {
                embed = embed.field("Recent Devnet Turns", event_lines.join("\n"), false);
            }
            embed
        }
        NameserviceRead::Whois { cell_id } => {
            let needle = normalize_cell(&cell_id);
            let matches: Vec<_> = activities
                .iter()
                .filter(|activity| {
                    activity.action == "register"
                        && activity_details(activity)
                            .get("owner")
                            .and_then(|value| value.as_str())
                            .map(normalize_cell)
                            .as_deref()
                            == Some(needle.as_str())
                })
                .take(5)
                .collect();
            let mut embed = if matches.is_empty() {
                embeds::warning_embed(
                    "No Recent Local Owner Match",
                    &format!(
                        "No bot-recorded nameservice registrations for `{}`. The node has receipts/events, but not a reverse nameservice index yet.",
                        short_cell(&cell_id)
                    ),
                )
            } else {
                embeds::success_embed("Recent Names For Owner")
                    .field("Owner", short_cell(&cell_id), false)
                    .field("Names", activity_lines(&matches), false)
            };

            let event_lines = recent_nameservice_event_lines(&events, Some(&cell_id));
            if !event_lines.is_empty() {
                embed = embed.field("Recent Devnet Turns", event_lines.join("\n"), false);
            }
            embed
        }
    }
}

fn activity_details(activity: &StarbridgeActivity) -> serde_json::Value {
    serde_json::from_str(&activity.details_json).unwrap_or_else(|_| serde_json::json!({}))
}

fn activity_lines(activities: &[&StarbridgeActivity]) -> String {
    activities
        .iter()
        .map(|activity| {
            let details = activity_details(activity);
            let name = activity.subject.as_deref().unwrap_or("unknown");
            let turn = details
                .get("turn_hash")
                .and_then(|value| value.as_str())
                .map(short_hash_tick)
                .unwrap_or_else(|| "`turn unknown`".to_string());
            let guild = activity.guild_id.as_deref().unwrap_or("unknown");
            format!("`{name}` in `/discord/{guild}/` - {turn}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn recent_nameservice_event_lines(
    events: &[crate::devnet::RecentEvent],
    needle: Option<&str>,
) -> Vec<String> {
    let needle = needle.map(|value| value.to_ascii_lowercase());
    events
        .iter()
        .filter(|event| {
            let haystack = format!(
                "{} {} {} {}",
                event.event_type,
                event.summary,
                event.cell_id.as_deref().unwrap_or_default(),
                event.tx_hash.as_deref().unwrap_or_default()
            )
            .to_ascii_lowercase();
            haystack.contains("nameservice")
                && needle
                    .as_ref()
                    .map(|needle| haystack.contains(needle))
                    .unwrap_or(true)
        })
        .take(5)
        .map(|event| {
            let turn = event
                .tx_hash
                .as_deref()
                .map(short_hash_tick)
                .unwrap_or_else(|| "`turn unknown`".to_string());
            format!("{turn} {}", event.summary)
        })
        .collect()
}

fn detail_cell(details: &serde_json::Value, key: &str) -> String {
    details
        .get(key)
        .and_then(|value| value.as_str())
        .map(short_cell)
        .unwrap_or_else(|| "`unknown`".to_string())
}

fn detail_string(details: &serde_json::Value, key: &str) -> String {
    match details.get(key) {
        Some(value) if value.is_string() => value.as_str().unwrap_or_default().to_string(),
        Some(value) if !value.is_null() => value.to_string(),
        _ => "`none`".to_string(),
    }
}

fn detail_turn(details: &serde_json::Value) -> String {
    details
        .get("turn_hash")
        .and_then(|value| value.as_str())
        .map(|hash| format!("`{hash}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
}

fn normalize_cell(cell_id: &str) -> String {
    cell_id
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| cell_id.trim())
        .to_ascii_lowercase()
}

fn get_string_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<String> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn get_integer_option(options: &[serenity::all::CommandDataOption], name: &str) -> Option<i64> {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(value) => Some(*value),
            _ => None,
        })
}

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

async fn respond_error(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::error_embed(title, desc);
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn respond_warning(ctx: &Context, command: &CommandInteraction, title: &str, desc: &str) {
    let embed = embeds::warning_embed(title, desc);
    let msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .ephemeral(true);
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn edit_embed(ctx: &Context, command: &CommandInteraction, embed: CreateEmbed) {
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn hosted_user_cell(user_id: u64, state: &BotState) -> Result<String, CreateEmbed> {
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => Ok(identity.cell_id),
        Ok(Some(identity)) if identity.mode == IdentityMode::ExternalPending => {
            Err(embeds::warning_embed(
                "Identity Pending",
                "Your external identity link is pending ownership proof. Nameservice writes must be signed by a hosted `/cipherclerk create` identity.",
            ))
        }
        Ok(Some(_)) => Err(embeds::warning_embed(
            "Hosted Identity Required",
            "The Discord bot can only submit canonical nameservice actions for hosted `/cipherclerk create` identities.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` before registering names.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}

fn parse_cell_id(input: &str) -> Result<CellId, String> {
    parse_cell_bytes(input).map(CellId)
}

fn parse_cell_bytes(input: &str) -> Result<[u8; 32], String> {
    let trimmed = input
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| input.trim());
    let bytes = hex::decode(trimmed).map_err(|e| format!("cell id must be hex: {e}"))?;
    bytes
        .try_into()
        .map_err(|_| "cell id must decode to exactly 32 bytes / 64 hex chars".to_string())
}

fn short_cell(cell_id: &str) -> String {
    let trimmed = cell_id
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| cell_id.trim());
    format!("`{}...`", &trimmed[..16.min(trimmed.len())])
}

fn short_hash_tick(hash: &str) -> String {
    format!("`{}...`", &hash[..12.min(hash.len())])
}

fn turn_hash_field(turn_hash: Option<String>) -> String {
    turn_hash
        .map(|hash| format!("`{hash}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
}
