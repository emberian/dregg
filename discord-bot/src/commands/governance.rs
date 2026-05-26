//! Governance commands: `/gov-propose`, `/gov-vote`, `/gov-status`, `/gov-routes`.
//!
//! Guild-as-federation governance over canonical governed-namespace cells.

use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::{BotState, embeds};
use dregg_app_framework::{CellId, FieldElement, hex_encode_32};
use dregg_dfa::{RouteTable, RouteTarget};
use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};
use starbridge_governed_namespace::{
    DISPUTE_WINDOW_HEIGHT_SLOT, GOVERNANCE_COMMITTEE_ROOT_SLOT, PENDING_PROPOSAL_ROOT_SLOT,
    ROUTE_TABLE_ROOT_SLOT, THRESHOLD_SLOT, VERSION_SLOT, VoteKind,
    build_propose_table_update_action, build_route_table, build_vote_on_proposal_action,
    route_table_commitment,
};

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/gov-propose <namespace-cell> <routes-json> <dispute-window-height> <description>`.
pub fn register_propose() -> CreateCommand {
    CreateCommand::new("gov-propose")
        .description("Propose a governed-namespace route table update")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "namespace-cell",
                "Governed namespace cell ID (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "routes-json",
                r#"Route JSON, e.g. [{"path":"/public/*","target":"public"}]"#,
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "dispute-window-height",
                "Block height at which the proposal finalizes",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "description",
                "Human-readable proposal description",
            )
            .required(true),
        )
}

/// Register `/gov-vote <namespace-cell> <prior-proposal-root> <yes|no>`.
pub fn register_vote() -> CreateCommand {
    CreateCommand::new("gov-vote")
        .description("Vote on a governed-namespace proposal")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "namespace-cell",
                "Governed namespace cell ID (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "prior-proposal-root",
                "Current pending proposal root from slot 5 (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "vote", "Your vote")
                .required(true)
                .add_string_choice("Yes", "yes")
                .add_string_choice("No", "no"),
        )
}

/// Register `/gov-status`.
pub fn register_status() -> CreateCommand {
    CreateCommand::new("gov-status")
        .description("Show governed-namespace cell metadata")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "namespace-cell",
                "Governed namespace cell ID (64 hex chars)",
            )
            .required(false),
        )
}

/// Register `/gov-routes`.
pub fn register_routes() -> CreateCommand {
    CreateCommand::new("gov-routes")
        .description("Explain governed-namespace route table read status")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "namespace-cell",
                "Governed namespace cell ID (64 hex chars)",
            )
            .required(false),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/gov-propose`.
pub async fn handle_propose(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let namespace_cell_hex =
        get_string_option(&command.data.options, "namespace-cell").unwrap_or_default();
    let routes_json = get_string_option(&command.data.options, "routes-json").unwrap_or_default();
    let dispute_window_height =
        match get_integer_option(&command.data.options, "dispute-window-height") {
            Some(value) if value >= 0 => value as u64,
            _ => {
                respond_error(
                    ctx,
                    command,
                    "Invalid Dispute Window",
                    "`dispute-window-height` must be a non-negative integer.",
                )
                .await;
                return;
            }
        };
    let description = get_string_option(&command.data.options, "description").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Governance commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let cclerk = match hosted_cclerk(command.user.id.get(), state).await {
        Ok(cclerk) => cclerk,
        Err(embed) => {
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let namespace_cell = match parse_cell_id(&namespace_cell_hex) {
        Ok(cell) => cell,
        Err(msg) => {
            let embed = embeds::error_embed("Invalid Namespace Cell", &msg);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let route_table = match parse_route_table(&routes_json) {
        Ok(table) => table,
        Err(msg) => {
            let embed = embeds::error_embed("Invalid Routes JSON", &msg);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let proposed_root = route_table_commitment(&route_table);
    let action = build_propose_table_update_action(
        &cclerk.app,
        namespace_cell,
        &route_table,
        dispute_window_height,
        &description,
    );

    let resp = state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:governance:propose:guild:{guild_id}")),
        )
        .await;

    match resp {
        Ok(result) if result.accepted => {
            let embed = embeds::success_embed("Proposal Submitted")
                .field("Namespace", short_hex(&namespace_cell_hex), true)
                .field(
                    "Proposed Root",
                    format!("`{}`", hex_encode_32(&proposed_root)),
                    false,
                )
                .field("Dispute Window", dispute_window_height.to_string(), true)
                .field("Description", &description, false)
                .field("Turn", turn_hash_display(result.turn_hash), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(result) => {
            let embed = embeds::error_embed(
                "Proposal Rejected",
                result
                    .error
                    .as_deref()
                    .unwrap_or("node rejected the signed governance action"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Node Unreachable", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/gov-vote`.
pub async fn handle_vote(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let namespace_cell_hex =
        get_string_option(&command.data.options, "namespace-cell").unwrap_or_default();
    let prior_proposal_root_hex =
        get_string_option(&command.data.options, "prior-proposal-root").unwrap_or_default();
    let vote = get_string_option(&command.data.options, "vote").unwrap_or_default();

    let guild_id = match command.guild_id {
        Some(id) => id.get(),
        None => {
            respond_error(
                ctx,
                command,
                "Guild Required",
                "Governance commands must be run in a server.",
            )
            .await;
            return;
        }
    };

    defer_ephemeral(ctx, command).await;

    let cclerk = match hosted_cclerk(command.user.id.get(), state).await {
        Ok(cclerk) => cclerk,
        Err(embed) => {
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let namespace_cell = match parse_cell_id(&namespace_cell_hex) {
        Ok(cell) => cell,
        Err(msg) => {
            let embed = embeds::error_embed("Invalid Namespace Cell", &msg);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let prior_proposal_root = match parse_field_hex(&prior_proposal_root_hex) {
        Ok(root) => root,
        Err(msg) => {
            let embed = embeds::error_embed("Invalid Proposal Root", &msg);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let vote_kind = match vote.as_str() {
        "yes" => VoteKind::Approve,
        "no" => VoteKind::Reject,
        _ => {
            let embed = embeds::error_embed("Invalid Vote", "`vote` must be `yes` or `no`.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let action = build_vote_on_proposal_action(
        &cclerk.app,
        namespace_cell,
        prior_proposal_root,
        vote_kind,
        1,
    );

    let resp = state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:governance:vote:{vote}:guild:{guild_id}")),
        )
        .await;

    match resp {
        Ok(result) if result.accepted => {
            let embed = embeds::success_embed("Vote Submitted")
                .field("Namespace", short_hex(&namespace_cell_hex), true)
                .field("Vote", vote, true)
                .field(
                    "Prior Proposal Root",
                    short_hex(&prior_proposal_root_hex),
                    false,
                )
                .field("Turn", turn_hash_display(result.turn_hash), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(result) => {
            let embed = embeds::error_embed(
                "Vote Rejected",
                result
                    .error
                    .as_deref()
                    .unwrap_or("node rejected the signed governance action"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Node Unreachable", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/gov-status`.
pub async fn handle_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let Some(namespace_cell_hex) = get_string_option(&command.data.options, "namespace-cell")
    else {
        let embed = embeds::warning_embed(
            "Namespace Cell Required",
            "The legacy guild governance status endpoint has been retired. Run `/gov-status namespace-cell:<cell-id>` to read current cell metadata from `/api/cell`.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };
    if let Err(msg) = parse_cell_id(&namespace_cell_hex) {
        let embed = embeds::error_embed("Invalid Namespace Cell", &msg);
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match state.devnet.get_cell_details(&namespace_cell_hex).await {
        Ok(cell) => {
            let desc = format!(
                "**Cell:** `{}`\n**Mode:** {}\n**Balance:** {}\n**Nonce:** {}\n**Program VK:** {}\n\nGoverned namespace slots: route root={}, version={}, committee root={}, threshold={}, dispute window={}, pending proposal root={}. The current `/api/cell` response exposes metadata, not per-slot field values, so detailed constitutional state requires a node read surface that returns cell fields.",
                cell.cell_id,
                cell.mode,
                cell.balance,
                cell.nonce,
                cell.program_vk.as_deref().unwrap_or("unknown"),
                ROUTE_TABLE_ROOT_SLOT,
                VERSION_SLOT,
                GOVERNANCE_COMMITTEE_ROOT_SLOT,
                THRESHOLD_SLOT,
                DISPUTE_WINDOW_HEIGHT_SLOT,
                PENDING_PROPOSAL_ROOT_SLOT,
            );
            let embed = embeds::dregg_embed("Governed Namespace Status").description(desc);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Status Unavailable", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle `/gov-routes`.
pub async fn handle_routes(ctx: &Context, command: &CommandInteraction, _state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let desc = match get_string_option(&command.data.options, "namespace-cell") {
        Some(namespace_cell_hex) => {
            if let Err(msg) = parse_cell_id(&namespace_cell_hex) {
                let embed = embeds::error_embed("Invalid Namespace Cell", &msg);
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
            format!(
                "Route tables are now governed by the namespace cell {} via slot {} (`route_table_root`). The current node read API does not expose the serialized route table or cell fields, so this command cannot reconstruct routes from `/api/cell` yet.\n\nUse `/gov-propose namespace-cell:<cell-id> routes-json:<json> dispute-window-height:<height>` to submit a canonical route table update.",
                short_hex(&namespace_cell_hex),
                ROUTE_TABLE_ROOT_SLOT,
            )
        }
        None => "The legacy `/governance/routes` endpoint has been retired. Governed namespace routes are committed on the namespace cell; provide `namespace-cell` to see the read-surface caveat for that cell.".to_string(),
    };
    let embed = embeds::warning_embed("Routes Read Surface", &desc);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

// ─── Helpers ────────────────────────────────────────────────────────────────

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

async fn hosted_cclerk(
    user_id: u64,
    state: &BotState,
) -> Result<UserCipherclerk, serenity::builder::CreateEmbed> {
    match state.db.get_user_identity(&user_id.to_string()).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => Ok(UserCipherclerk::derive(
            &state.config.bot_secret,
            user_id,
            state.federation_id_bytes,
        )),
        Ok(Some(identity)) if identity.mode == IdentityMode::ExternalPending => {
            Err(embeds::warning_embed(
                "Identity Pending",
                "Your external identity link is pending ownership proof. Governance turns must be signed by a hosted `/cipherclerk create` identity.",
            ))
        }
        Ok(Some(_)) => Err(embeds::warning_embed(
            "Hosted Identity Required",
            "The Discord bot can only submit canonical governed-namespace actions for hosted `/cipherclerk create` identities.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` before using governance actions.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}

fn parse_cell_id(input: &str) -> Result<CellId, String> {
    parse_32_hex(input, "cell id").map(CellId::from_bytes)
}

fn parse_field_hex(input: &str) -> Result<FieldElement, String> {
    parse_32_hex(input, "field element")
}

fn parse_32_hex(input: &str, label: &str) -> Result<[u8; 32], String> {
    let trimmed = input
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| input.trim());
    let bytes = hex::decode(trimmed).map_err(|e| format!("{label} must be hex: {e}"))?;
    bytes
        .try_into()
        .map_err(|_| format!("{label} must decode to exactly 32 bytes / 64 hex chars"))
}

#[derive(serde::Deserialize)]
struct RouteSpec {
    path: String,
    target: serde_json::Value,
}

fn parse_route_table(input: &str) -> Result<RouteTable, String> {
    let specs: Vec<RouteSpec> =
        serde_json::from_str(input).map_err(|e| format!("expected an array of routes: {e}"))?;
    if specs.is_empty() {
        return Err("at least one route is required".to_string());
    }

    let mut owned = Vec::with_capacity(specs.len());
    for spec in specs {
        if spec.path.trim().is_empty() {
            return Err("route path cannot be empty".to_string());
        }
        owned.push((spec.path, parse_route_target(&spec.target)?));
    }

    let borrowed: Vec<(&str, RouteTarget)> = owned
        .iter()
        .map(|(path, target)| (path.as_str(), target.clone()))
        .collect();
    Ok(build_route_table(&borrowed))
}

fn parse_route_target(value: &serde_json::Value) -> Result<RouteTarget, String> {
    if let Some(name) = value.as_str() {
        return Ok(if name == "drop" {
            RouteTarget::drop()
        } else {
            RouteTarget::handler(name)
        });
    }
    let obj = value
        .as_object()
        .ok_or_else(|| "route target must be a string or object".to_string())?;

    if obj.get("drop").and_then(|v| v.as_bool()) == Some(true) {
        return Ok(RouteTarget::drop());
    }
    if let Some(handler) = obj.get("handler").and_then(|v| v.as_str()) {
        return Ok(RouteTarget::handler(handler));
    }
    if let Some(federation) = obj.get("federation").and_then(|v| v.as_str()) {
        return parse_32_hex(federation, "federation target").map(RouteTarget::federation);
    }

    let target_type = obj
        .get("type")
        .and_then(|v| v.as_str())
        .or_else(|| obj.get("kind").and_then(|v| v.as_str()));
    match target_type {
        Some("drop") => Ok(RouteTarget::drop()),
        Some("handler") => obj
            .get("name")
            .and_then(|v| v.as_str())
            .map(RouteTarget::handler)
            .ok_or_else(|| "handler targets require a string `name`".to_string()),
        Some("federation") => obj
            .get("group_id")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "federation targets require a hex `group_id`".to_string())
            .and_then(|hex| parse_32_hex(hex, "federation group_id"))
            .map(RouteTarget::federation),
        Some("userspace") => {
            let kind = obj
                .get("userspace_kind")
                .or_else(|| obj.get("name"))
                .and_then(|v| v.as_str())
                .ok_or_else(|| {
                    "userspace targets require `userspace_kind` or `name`".to_string()
                })?;
            let payload = match obj.get("payload_hex").and_then(|v| v.as_str()) {
                Some(hex_payload) => {
                    hex::decode(hex_payload).map_err(|e| format!("invalid payload_hex: {e}"))?
                }
                None => obj
                    .get("payload")
                    .and_then(|v| v.as_str())
                    .map(|s| s.as_bytes().to_vec())
                    .unwrap_or_default(),
            };
            Ok(RouteTarget::userspace(kind, payload))
        }
        Some(other) => Err(format!("unsupported route target type `{other}`")),
        None => Err(
            "route target object needs one of `handler`, `federation`, `drop`, or `type`"
                .to_string(),
        ),
    }
}

fn short_hex(value: &str) -> String {
    let trimmed = value
        .trim()
        .strip_prefix("dregg://cell/")
        .unwrap_or_else(|| value.trim());
    format!("`{}...`", &trimmed[..12.min(trimmed.len())])
}

fn turn_hash_display(hash: Option<String>) -> String {
    hash.map(|hash| format!("`{hash}`"))
        .unwrap_or_else(|| "`unknown`".to_string())
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
