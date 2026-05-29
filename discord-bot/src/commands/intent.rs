//! `/intent post <spec>` — publish a **real** signed intent to the channel.
//!
//! The posted artifact is a canonical `dregg_turn::action::Action` signed with
//! the poster's hosted Ed25519 key (`Authorization::Signature`), produced by
//! [`crate::intent_flow`]. The signature binds the spec content and is
//! verifiable by anyone against the poster's public key. Reactions on the
//! posted message express fulfillment interest (the multi-party `TurnComposer`
//! settlement is a named follow-up — see `STARBRIDGE-DISCORD.md`).

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;
use crate::intent_flow;

/// Register `/intent` with a `post` subcommand.
pub fn register() -> CreateCommand {
    CreateCommand::new("intent")
        .description("Publish a real signed intent to the channel")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "post",
                "Post a signed intent",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "spec",
                    "What you want (e.g. 'want: 5 GOOSE for 1hr compute')",
                )
                .required(true),
            ),
        )
}

/// Handle `/intent post`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Extract the `spec` from the `post` subcommand.
    let spec = command
        .data
        .options
        .iter()
        .find(|o| o.name == "post")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::SubCommand(sub) => sub
                .iter()
                .find(|s| s.name == "spec")
                .and_then(|s| match &s.value {
                    CommandDataOptionValue::String(v) => Some(v.clone()),
                    _ => None,
                }),
            _ => None,
        })
        .unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    if spec.trim().is_empty() {
        let embed = embeds::error_embed("Empty Intent", "Provide a non-empty intent spec.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let invoker_id = command.user.id.get();
    let discord_id = invoker_id.to_string();
    match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => {}
        Ok(Some(_)) | Ok(None) => {
            let embed = embeds::warning_embed(
                "No Hosted Cipherclerk",
                "Create a hosted cipherclerk with `/cipherclerk create` before posting a signed intent.",
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

    // Build the real signed intent from the poster's hosted cipherclerk.
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        invoker_id,
        state.federation_id_bytes,
    );
    let signed = intent_flow::build_signed_intent(&cclerk.app, &spec);

    // Defensive: confirm the artifact verifies before we publish it.
    if !intent_flow::verify_signed_intent(&signed) {
        let embed = embeds::error_embed(
            "Signing Failed",
            "Produced intent did not self-verify; not posting.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let spec_hash = hex::encode(blake3::hash(spec.as_bytes()).as_bytes());

    // Ephemeral confirmation to the poster.
    let confirm = embeds::success_embed("Signed Intent Published")
        .description("Real `Authorization::Signature` action posted to the channel.")
        .field(
            "Poster pubkey",
            format!("`{}`", cclerk.public_key_hex()),
            false,
        )
        .field("Spec hash", format!("`{}`", &spec_hash[..16]), true);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(confirm))
        .await;

    // Public intent card. React to express fulfillment interest.
    let public = serenity::all::CreateMessage::new().content(format!(
        "**Signed intent** from <@{invoker_id}>\n```\n{spec}\n```\nposter-pk: `{}`\nspec-hash: `{}`\nReact to express fulfillment interest.",
        cclerk.public_key_hex(),
        spec_hash,
    ));
    if let Ok(msg) = command.channel_id.send_message(&ctx.http, public).await {
        let _ = msg
            .react(
                &ctx.http,
                serenity::all::ReactionType::Unicode("✋".to_string()),
            )
            .await;
    }
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
