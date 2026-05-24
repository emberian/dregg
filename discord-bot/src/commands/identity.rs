//! `/credential` command — issue, verify, and list verifiable credentials.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::wallet::DerivedWallet;

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

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to issue credentials. Use `/wallet create` first.",
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

    let wallet = DerivedWallet::derive(&state.config.bot_secret, user_id);
    let signature = sign_action(&wallet, &format!("issue:{schema}:{attributes}"));

    match state
        .devnet
        .issue_credential(&cell_id, &schema, &attributes, &signature)
        .await
    {
        Ok(credential_id) => {
            let embed = embeds::success_embed("Credential Issued")
                .field("Schema", &schema, true)
                .field("Credential ID", format!("`{credential_id}`"), true)
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

    let verifier_cell = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to verify credentials. Use `/wallet create` first.",
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
                "Target Has No Wallet",
                &format!("<@{target_id}> does not have a pyana wallet."),
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

    match state
        .devnet
        .request_proof(&verifier_cell, &subject_cell, &predicate)
        .await
    {
        Ok(result) => {
            let embed = embeds::success_embed("Proof Requested")
                .field("Subject", format!("<@{target_id}>"), true)
                .field("Predicate", &predicate, true)
                .field("Request ID", format!("`{}`", result.request_id), true)
                .field("Status", &result.status, true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Verification Request Failed",
                &format!("Could not request proof: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_list(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to view credentials. Use `/wallet create` first.",
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

    match state.devnet.list_credentials(&cell_id).await {
        Ok(creds) => {
            if creds.is_empty() {
                let embed = embeds::pyana_embed("Your Credentials").description(
                    "You have no credentials yet. Use `/credential issue` to create one.",
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for cred in &creds {
                let short_issuer = if cred.issuer.len() > 16 {
                    format!("{}...", &cred.issuer[..16])
                } else {
                    cred.issuer.clone()
                };
                description.push_str(&format!(
                    "**{}** — `{}`\nIssuer: `{short_issuer}` | Issued: {}\n\n",
                    cred.schema, cred.credential_id, cred.issued_at,
                ));
            }

            let embed = embeds::pyana_embed("Your Credentials")
                .description(description)
                .field("Total", creds.len().to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Credentials Unavailable",
                &format!("Could not load credentials: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign an action using BLAKE3.
fn sign_action(wallet: &DerivedWallet, action: &str) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(action.as_bytes());
    msg.extend_from_slice(&wallet.private_key);
    let sig = blake3::hash(&msg);
    hex::encode(sig.as_bytes())
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
