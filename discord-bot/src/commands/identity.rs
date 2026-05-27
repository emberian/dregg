//! `/credential` command — issue, verify, and list verifiable credentials.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::credential_issue;
use crate::db::IdentityMode;
use crate::embeds;

/// Register the /credential command.
pub fn register() -> CreateCommand {
    CreateCommand::new("credential")
        .description("Issue, verify, and manage verifiable credentials")
        .add_option(
            CreateCommandOption::new(CommandOptionType::SubCommand, "issue", "Issue a credential")
                .add_sub_option(
                    CreateCommandOption::new(
                        CommandOptionType::String,
                        "schema",
                        "Credential schema (e.g. age, membership, kyc)",
                    )
                    .required(true),
                )
                .add_sub_option(
                    CreateCommandOption::new(
                        CommandOptionType::String,
                        "attributes",
                        "JSON attributes for the credential",
                    )
                    .required(true),
                ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "verify",
                "Request a proof from another user",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::User, "user", "User to verify")
                    .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "predicate",
                    "Predicate to verify (e.g. age>=18)",
                )
                .required(true),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "List your held credentials",
        ))
}

/// Handle /credential interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "issue" => handle_issue(ctx, command, state).await,
        "verify" => handle_verify(ctx, command, state).await,
        "list" => handle_list(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_issue(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let schema = sub_opts
        .iter()
        .find(|o| o.name == "schema")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    let attributes = sub_opts
        .iter()
        .find(|o| o.name == "attributes")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => identity.cell_id,
        Ok(Some(_)) => {
            let embed = embeds::warning_embed(
                "Hosted Identity Required",
                "Credential issuance signs a canonical Starbridge turn, so it currently requires a hosted `/cipherclerk create` identity.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to issue credentials. Use `/cipherclerk create` first.",
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

    match credential_issue::issue_from_discord_input(state, user_id, &cell_id, &schema, &attributes)
        .await
    {
        Ok(result) => {
            let turn_hash = result.turn.turn_hash.clone();
            let embed = embeds::success_embed("Credential Issued")
                .field("Schema", &result.schema, true)
                .field("Credential ID", format!("`{}`", result.credential_id), true)
                .field(
                    "Turn",
                    turn_hash
                        .as_ref()
                        .map(|hash| format!("`{hash}`"))
                        .unwrap_or_else(|| "`unknown`".to_string()),
                    false,
                )
                .field(
                    "What Is Stored",
                    "The node committed the identity issue action as a signed turn. It does not expose a holder-private credential store yet, so keep the credential ID and turn hash for audit.",
                    false,
                )
                .field("Attributes", format!("```json\n{attributes}\n```"), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed =
                embeds::error_embed("Issue Failed", &format!("Could not issue credential: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_verify(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let target_user_id = sub_opts
        .iter()
        .find(|o| o.name == "user")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        });

    let predicate = sub_opts
        .iter()
        .find(|o| o.name == "predicate")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    match state.db.get_cell_id(&discord_id).await {
        Ok(Some(_)) => {}
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to verify credentials. Use `/cipherclerk create` first.",
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
    }

    let target_id = match target_user_id {
        Some(id) => id,
        None => {
            let embed =
                embeds::error_embed("Invalid Arguments", "Please specify a user to verify.");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let target_discord = target_id.to_string();
    let subject_cell = match state.db.get_cell_id(&target_discord).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Target Has No Cipherclerk",
                &format!("<@{target_id}> does not have a dregg cclerk."),
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

    let embed = embeds::warning_embed(
        "Proof Requests Unavailable",
        &format!(
            "Credential proof requests are not exposed by the current node API. Target <@{target_id}> has cell `{}` and predicate `{}` was accepted.\n\nActionable next step: ask the holder to share a credential issue turn hash from `/credential list`, then inspect that turn in the explorer. Selective disclosure still needs a holder-private credential store plus a proof request/read surface.",
            &subject_cell[..16.min(subject_cell.len())],
            predicate
        ),
    )
    .field(
        "Recent Target Turns",
        recent_identity_turns_field(state, &subject_cell).await,
        false,
    );
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_list(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to view credentials. Use `/cipherclerk create` first.",
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

    let embed = embeds::warning_embed(
        "Credential Store Unavailable",
        &format!(
            "Credential issuance commits canonical identity actions for `{}`, but the current node read API does not expose holder-private credential storage or an identity index yet.\n\nUse the recent committed turns below as audit checkpoints. If you just issued a credential, keep its credential ID and turn hash from the issue response.",
            &cell_id[..16.min(cell_id.len())],
        ),
    )
    .field(
        "Recent Turns For This Cell",
        recent_identity_turns_field(state, &cell_id).await,
        false,
    );
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
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

async fn recent_identity_turns_field(state: &BotState, cell_id: &str) -> String {
    match state
        .devnet
        .get_recent_identity_issue_turns(cell_id, 5)
        .await
    {
        Ok(events) if events.is_empty() => {
            "No recent committed turns were returned for this cell.".to_string()
        }
        Ok(events) => events
            .iter()
            .map(|event| {
                let turn = event
                    .tx_hash
                    .as_deref()
                    .map(|hash| format!("`{}`", short_hash(hash)))
                    .unwrap_or_else(|| "`unknown`".to_string());
                format!("{} — {} at {}", turn, event.summary, event.timestamp)
            })
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("Could not load recent turns from `/api/events`: {e}"),
    }
}

fn short_hash(hash: &str) -> String {
    format!("{}...", &hash[..12.min(hash.len())])
}
