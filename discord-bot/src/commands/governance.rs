//! Governance commands: `/gov-propose`, `/gov-vote`, `/gov-status`, `/gov-routes`.
//!
//! Guild-as-federation governance — proposals, votes, constitution state, DFA routes.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/gov-propose <type> <description>`.
pub fn register_propose() -> CreateCommand {
    CreateCommand::new("gov-propose")
        .description("Propose a governance change (route amendment, threshold, etc.)")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "type",
                "Proposal type (route-amendment, threshold, parameter, membership)",
            )
            .required(true)
            .add_string_choice("Route Amendment", "route-amendment")
            .add_string_choice("Threshold Change", "threshold")
            .add_string_choice("Parameter Update", "parameter")
            .add_string_choice("Membership Change", "membership"),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "description",
                "Description of the proposed change",
            )
            .required(true),
        )
}

/// Register `/gov-vote <proposal-id> <yes|no>`.
pub fn register_vote() -> CreateCommand {
    CreateCommand::new("gov-vote")
        .description("Vote on a governance proposal")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "proposal-id",
                "Proposal ID to vote on",
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
    CreateCommand::new("gov-status").description("Show the guild's constitution state")
}

/// Register `/gov-routes`.
pub fn register_routes() -> CreateCommand {
    CreateCommand::new("gov-routes")
        .description("Show the DFA route table for this guild's namespace")
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/gov-propose`.
pub async fn handle_propose(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let proposal_type = get_string_option(&command.data.options, "type").unwrap_or_default();
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

    let discord_id = command.user.id.get().to_string();
    let proposer_cell = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a linked pyana identity to propose. Use `/link-cclerk` first.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let url = format!("{}/governance/propose", state.config.devnet_url);
    let body = serde_json::json!({
        "guild_id": guild_id,
        "proposer": proposer_cell,
        "proposal_type": proposal_type,
        "description": description,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let result: ProposeResponse = match r.json().await {
                Ok(p) => p,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let embed = embeds::success_embed("Proposal Created")
                .field("ID", format!("`{}`", result.proposal_id), true)
                .field("Type", &proposal_type, true)
                .field("Description", &description, false)
                .field(
                    "Voting Period",
                    format!("{} blocks", result.voting_period),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Proposal Failed", &body);
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
    let proposal_id = get_string_option(&command.data.options, "proposal-id").unwrap_or_default();
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

    let discord_id = command.user.id.get().to_string();
    let voter_cell = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a linked pyana identity to vote. Use `/link-cclerk` first.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let url = format!("{}/governance/vote", state.config.devnet_url);
    let body = serde_json::json!({
        "guild_id": guild_id,
        "proposal_id": proposal_id,
        "voter": voter_cell,
        "vote": vote,
    });

    let resp = state.devnet.client().post(&url).json(&body).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let emoji = if vote == "yes" { "+" } else { "-" };
            let embed = embeds::success_embed("Vote Cast")
                .field("Proposal", format!("`{proposal_id}`"), true)
                .field("Vote", format!("{emoji} {vote}"), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Vote Failed", &body);
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

    let url = format!(
        "{}/governance/status?guild_id={guild_id}",
        state.config.devnet_url
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let status: GovStatusResponse = match r.json().await {
                Ok(s) => s,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let mut desc = format!("**Constitution:** {}\n", status.constitution_hash);
            desc.push_str(&format!("**Members:** {}\n", status.member_count));
            desc.push_str(&format!("**Quorum:** {}%\n", status.quorum_percent));
            desc.push_str(&format!(
                "**Active Proposals:** {}\n",
                status.active_proposals
            ));

            if !status.recent_proposals.is_empty() {
                desc.push_str("\n**Recent Proposals:**\n");
                for p in &status.recent_proposals {
                    let status_icon = match p.status.as_str() {
                        "passed" => "[PASSED]",
                        "rejected" => "[REJECTED]",
                        "active" => "[ACTIVE]",
                        _ => "[PENDING]",
                    };
                    desc.push_str(&format!(
                        "- `{}` {} — {}\n",
                        &p.id[..8.min(p.id.len())],
                        status_icon,
                        p.description
                    ));
                }
            }

            let embed = embeds::pyana_embed("Governance Status").description(desc);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Status Unavailable", &body);
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

/// Handle `/gov-routes`.
pub async fn handle_routes(ctx: &Context, command: &CommandInteraction, state: &BotState) {
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

    let url = format!(
        "{}/governance/routes?guild_id={guild_id}",
        state.config.devnet_url
    );

    let resp = state.devnet.client().get(&url).send().await;

    match resp {
        Ok(r) if r.status().is_success() => {
            let routes: RoutesResponse = match r.json().await {
                Ok(r) => r,
                Err(e) => {
                    let embed = embeds::error_embed("Parse Error", &e.to_string());
                    let _ = command
                        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                        .await;
                    return;
                }
            };

            let mut desc = format!("**DFA States:** {}\n", routes.state_count);
            desc.push_str(&format!("**Transitions:** {}\n\n", routes.transition_count));

            if !routes.routes.is_empty() {
                desc.push_str("```\n");
                for route in &routes.routes {
                    desc.push_str(&format!(
                        "{} -> {} [{}]\n",
                        route.from, route.to, route.label
                    ));
                }
                desc.push_str("```");
            } else {
                desc.push_str("No routes configured yet.");
            }

            let embed = embeds::pyana_embed("Namespace Route Table").description(desc);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Ok(r) => {
            let body = r.text().await.unwrap_or_default();
            let embed = embeds::error_embed("Routes Unavailable", &body);
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

// ─── Wire types ─────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct ProposeResponse {
    proposal_id: String,
    voting_period: u64,
}

#[derive(serde::Deserialize)]
struct GovStatusResponse {
    constitution_hash: String,
    member_count: u64,
    quorum_percent: u64,
    active_proposals: u64,
    recent_proposals: Vec<ProposalSummary>,
}

#[derive(serde::Deserialize)]
struct ProposalSummary {
    id: String,
    status: String,
    description: String,
}

#[derive(serde::Deserialize)]
struct RoutesResponse {
    state_count: u64,
    transition_count: u64,
    routes: Vec<RouteEntry>,
}

#[derive(serde::Deserialize)]
struct RouteEntry {
    from: String,
    to: String,
    label: String,
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
