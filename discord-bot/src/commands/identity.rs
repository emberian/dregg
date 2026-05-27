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
            if let Err(e) = state
                .db
                .store_held_credential(
                    &discord_id,
                    &cell_id,
                    &cell_id,
                    &result.credential_id,
                    &result.schema,
                    result.issued_at,
                    turn_hash.as_deref(),
                    &result.encoded_credential,
                    &result.attributes_json,
                )
                .await
            {
                let embed = embeds::error_embed(
                    "Holder Store Failed",
                    &format!(
                        "The node accepted the credential turn, but the bot could not persist the held credential locally: {e}"
                    ),
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

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
                    "Stored locally in the bot holder store: credential metadata, holder-private encoded credential material, attributes JSON, and the committed turn hash.",
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

    let candidate = match state
        .db
        .find_held_credential_for_predicate(&target_discord, &subject_cell, &predicate)
        .await
    {
        Ok(candidate) => candidate,
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    let status = if candidate.is_some() {
        "credential_metadata_found"
    } else {
        "no_local_credential"
    };
    let credential_id = candidate
        .as_ref()
        .map(|credential| credential.credential_id.as_str());
    let presentation_json = serde_json::json!({
        "type": "presentation_placeholder",
        "predicate": predicate,
        "status": status,
        "credential_id": credential_id,
        "cryptographic_proof": null,
        "note": "Selective disclosure proof generation is not implemented in the Discord bot."
    })
    .to_string();
    let presentation = match state
        .db
        .create_identity_presentation(
            &discord_id,
            &target_discord,
            &subject_cell,
            &predicate,
            status,
            credential_id,
            &presentation_json,
        )
        .await
    {
        Ok(presentation) => presentation,
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let mut embed = embeds::warning_embed(
        "Proof Request Stored",
        &format!(
            "Stored request `{}` for <@{target_id}> cell `{}` with status `{}`. No selective disclosure proof was generated.",
            presentation.request_id,
            &subject_cell[..16.min(subject_cell.len())],
            presentation.status
        ),
    )
    .field("Predicate", format!("`{predicate}`"), false);
    if let Some(credential) = candidate {
        embed = embed.field(
            "Matched Local Credential",
            format!(
                "`{}` — schema `{}` issued at {}",
                short_hash(&credential.credential_id),
                credential.schema,
                credential.issued_at
            ),
            false,
        );
    } else {
        embed = embed.field(
            "Matched Local Credential",
            "None. The request was persisted as a placeholder only.",
            false,
        );
    }
    let embed = embed.field(
        "Proof Checkpoints",
        identity_proof_checkpoints_field(state, &subject_cell).await,
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

    let held_credentials = match state
        .db
        .list_held_credentials(&discord_id, &cell_id, 10)
        .await
    {
        Ok(credentials) => credentials,
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let embed = embeds::success_embed("Held Credentials")
        .description(format!(
            "Local holder store for `{}` plus node checkpoint links from committed receipts.",
            &cell_id[..16.min(cell_id.len())],
        ))
        .field(
            "Local Credentials",
            held_credentials_field(&held_credentials),
            false,
        )
        .field(
            "Node Checkpoints",
            identity_credentials_field(state, &cell_id).await,
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

async fn identity_credentials_field(state: &BotState, cell_id: &str) -> String {
    match state.devnet.get_identity_credentials(cell_id, 5).await {
        Ok(checkpoints) if checkpoints.is_empty() => {
            recent_identity_turns_field(state, cell_id).await
        }
        Ok(checkpoints) => checkpoints
            .iter()
            .map(|checkpoint| {
                format!(
                    "`{}` — issuer `{}` proof {} finality {}",
                    short_hash(&checkpoint.turn_hash),
                    short_hash(&checkpoint.issuer_cell),
                    checkpoint.proof_status,
                    checkpoint.finality
                )
            })
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("Could not load `/api/starbridge/identity/credentials`: {e}"),
    }
}

fn held_credentials_field(credentials: &[crate::db::HeldCredential]) -> String {
    if credentials.is_empty() {
        return "No locally held credentials are stored for this hosted identity.".to_string();
    }

    credentials
        .iter()
        .map(|credential| {
            let turn = credential
                .turn_hash
                .as_deref()
                .map(short_hash)
                .unwrap_or_else(|| "unknown".to_string());
            format!(
                "`{}` — schema `{}` issuer `{}` turn `{}` issued {}",
                short_hash(&credential.credential_id),
                credential.schema,
                short_hash(&credential.issuer_cell_id),
                turn,
                credential.issued_at
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

async fn identity_proof_checkpoints_field(state: &BotState, cell_id: &str) -> String {
    match state
        .devnet
        .get_identity_proof_checkpoints(cell_id, 5)
        .await
    {
        Ok(checkpoints) if checkpoints.is_empty() => {
            recent_identity_turns_field(state, cell_id).await
        }
        Ok(checkpoints) => checkpoints
            .iter()
            .map(|checkpoint| {
                let witness = if checkpoint.witness_count == 1 {
                    "1 witness".to_string()
                } else {
                    format!("{} witnesses", checkpoint.witness_count)
                };
                format!(
                    "`{}` — proof {} {} finality {}",
                    short_hash(&checkpoint.turn_hash),
                    checkpoint.proof_status,
                    witness,
                    checkpoint.finality
                )
            })
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("Could not load `/api/starbridge/identity/proof-checkpoints`: {e}"),
    }
}

fn short_hash(hash: &str) -> String {
    format!("{}...", &hash[..12.min(hash.len())])
}
