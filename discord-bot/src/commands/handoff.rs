//! `/handoff` — mint a **real** canonical CapTP `HandoffCertificate` and post
//! its compact `dregg-handoff:<base58>` wire form to the channel, and
//! `/handoff-redeem` — redeem one a peer posted.
//!
//! Unlike the legacy `/cap-delegate` path (a BLAKE3-MAC bot-local token, see
//! `captp_client.rs`), this command produces a genuine signed
//! `dregg_captp::handoff::HandoffCertificate` via [`crate::handoff_flow`]. The
//! certificate carries a real Ed25519 introducer signature and redemption runs
//! the canonical `validate_handoff` against the bot's soft-federation swiss
//! table. The artifact-producing logic lives in `handoff_flow.rs` and is
//! unit-tested without Discord.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::IdentityMode;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/handoff <cell-id> <@user>`.
pub fn register() -> CreateCommand {
    CreateCommand::new("handoff")
        .description("Mint a real signed CapTP handoff certificate for a Discord user")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "cell-id",
                "Your hosted cell id (64 hex) to hand off",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "Recipient").required(true),
        )
}

/// Register `/handoff-redeem <dregg-handoff:...>`.
pub fn register_redeem() -> CreateCommand {
    CreateCommand::new("handoff-redeem")
        .description("Redeem a dregg-handoff:<...> certificate posted to the channel")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "certificate",
                "The dregg-handoff:<base58> string",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "introducer-pk",
                "Introducer public key (64 hex), as shown when the handoff was minted",
            )
            .required(true),
        )
}

// ─── Handlers ───────────────────────────────────────────────────────────────

/// Handle `/handoff`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let cell_id = string_opt(command, "cell-id").unwrap_or_default();
    let target_user_id = command
        .data
        .options
        .iter()
        .find(|o| o.name == "user")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        });

    defer_ephemeral(ctx, command).await;

    // Holder right: the invoker must own this hosted cell.
    if let Err(embed) = ensure_hosted_owner(command, state, &cell_id).await {
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let target_id = match target_user_id {
        Some(id) => id,
        None => {
            return reply_err(
                ctx,
                command,
                "Invalid Arguments",
                "Specify a recipient user.",
            )
            .await;
        }
    };

    // The recipient must have a hosted identity (so the bot can derive their
    // canonical Ed25519 public key — the named recipient of the certificate).
    let target_discord = target_id.to_string();
    match state.db.get_user_identity(&target_discord).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => identity,
        Ok(Some(_)) => {
            return reply_warn(
                ctx,
                command,
                "Recipient Not Hosted",
                &format!(
                    "<@{target_id}> must have a hosted cipherclerk to receive a real handoff certificate (the bot derives their recipient public key from the hosted identity)."
                ),
            )
            .await;
        }
        Ok(None) => {
            return reply_warn(
                ctx,
                command,
                "Recipient Has No Cipherclerk",
                &format!(
                    "<@{target_id}> has no dregg identity. They need `/cipherclerk create` first."
                ),
            )
            .await;
        }
        Err(e) => return reply_err(ctx, command, "Database Error", &e.to_string()).await,
    };

    // Derive both peers' canonical key material from the custodial root. This
    // is the same derivation `UserCipherclerk` uses, so the introducer
    // signature verifies against the invoker's public key and the recipient is
    // the recipient's real cell key.
    let invoker_id = command.user.id.get();
    let introducer = UserCipherclerk::derive(
        &state.config.bot_secret,
        invoker_id,
        state.federation_id_bytes,
    );
    let recipient = UserCipherclerk::derive(
        &state.config.bot_secret,
        target_id,
        state.federation_id_bytes,
    );
    let recipient_pk_hex = recipient.public_key_hex().to_string();

    // Mint a real, signed certificate against the bot's soft-federation broker.
    let current_height = state.devnet.current_height().await.unwrap_or(0);
    let minted = {
        let mut broker = state.handoff_broker.lock().await;
        broker.mint_handoff(
            introducer.legacy_secret(),
            &cell_id,
            &recipient_pk_hex,
            current_height,
            None,
            Some(1),
        )
    };

    match minted {
        Ok(minted) => {
            // Ephemeral confirmation to the introducer (carries the introducer
            // pubkey the recipient needs to redeem).
            let confirm = embeds::success_embed("Handoff Certificate Minted")
                .description(
                    "Real signed `dregg_captp::handoff::HandoffCertificate`. Posting the compact form to the channel.",
                )
                .field("Cell", format!("`{}`", short(&cell_id)), true)
                .field("Recipient", format!("<@{target_id}>"), true)
                .field(
                    "Introducer pubkey",
                    format!("`{}`", introducer.public_key_hex()),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(confirm))
                .await;

            // Public, paste-friendly artifact + the introducer pubkey so the
            // recipient can `/handoff-redeem`.
            let public = serenity::all::CreateMessage::new().content(format!(
                "<@{target_id}> — capability handoff from <@{invoker_id}>. Redeem with `/handoff-redeem`:\n```\n{}\n```\nintroducer-pk: `{}`",
                minted.compact,
                introducer.public_key_hex(),
            ));
            let _ = command.channel_id.send_message(&ctx.http, public).await;
        }
        Err(e) => reply_err(ctx, command, "Handoff Failed", &e.to_string()).await,
    }
}

/// Handle `/handoff-redeem`.
pub async fn handle_redeem(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let compact = string_opt(command, "certificate").unwrap_or_default();
    let introducer_pk_hex = string_opt(command, "introducer-pk").unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    // The redeemer must be the hosted user whose key matches the certificate's
    // named recipient — we derive their seed from the custodial root.
    let invoker_id = command.user.id.get();
    let discord_id = invoker_id.to_string();
    match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => {}
        Ok(Some(_)) | Ok(None) => {
            return reply_warn(
                ctx,
                command,
                "No Hosted Cipherclerk",
                "Create a hosted cipherclerk with `/cipherclerk create` before redeeming a handoff.",
            )
            .await;
        }
        Err(e) => return reply_err(ctx, command, "Database Error", &e.to_string()).await,
    }

    let introducer_pk = match hex::decode(&introducer_pk_hex)
        .ok()
        .and_then(|b| <[u8; 32]>::try_from(b).ok())
    {
        Some(pk) => pk,
        None => {
            return reply_err(
                ctx,
                command,
                "Invalid Introducer Key",
                "introducer-pk must be 64 hex characters.",
            )
            .await;
        }
    };

    let recipient = UserCipherclerk::derive(
        &state.config.bot_secret,
        invoker_id,
        state.federation_id_bytes,
    );
    let current_height = state.devnet.current_height().await.unwrap_or(0);

    let result = {
        let mut broker = state.handoff_broker.lock().await;
        broker.redeem_handoff(
            &compact,
            recipient.legacy_secret(),
            &introducer_pk,
            current_height,
        )
    };

    match result {
        Ok(acceptance) => {
            let embed = embeds::success_embed("Handoff Redeemed")
                .description(
                    "Canonical `validate_handoff` accepted the presentation. You now hold a real soft-federation routing grant for the cell.",
                )
                .field("Cell", format!("`{}`", short(&hex::encode(acceptance.cell_id.0))), true)
                .field("Permissions", format!("{:?}", acceptance.permissions), true)
                .field(
                    "Routing token",
                    format!("`{}`", &hex::encode(acceptance.routing_token)[..16]),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => reply_err(ctx, command, "Redeem Failed", &e.to_string()).await,
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn string_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    command
        .data
        .options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn short(s: &str) -> String {
    if s.len() > 16 {
        format!("{}...", &s[..16])
    } else {
        s.to_string()
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

async fn reply_err(ctx: &Context, command: &CommandInteraction, title: &str, msg: &str) {
    let embed = embeds::error_embed(title, msg);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn reply_warn(ctx: &Context, command: &CommandInteraction, title: &str, msg: &str) {
    let embed = embeds::warning_embed(title, msg);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

/// Holder-right check: the invoker must own this *hosted* cell.
async fn ensure_hosted_owner(
    command: &CommandInteraction,
    state: &BotState,
    cell_id: &str,
) -> Result<(), serenity::all::CreateEmbed> {
    if cell_id.len() != 64 || hex::decode(cell_id).is_err() {
        return Err(embeds::error_embed(
            "Invalid Cell ID",
            "Cell IDs must be 64 hex characters.",
        ));
    }
    let discord_id = command.user.id.get().to_string();
    match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity))
            if identity.mode == IdentityMode::Hosted && identity.cell_id == cell_id =>
        {
            Ok(())
        }
        Ok(Some(_)) => Err(embeds::error_embed(
            "Capability Not Held",
            "You can only hand off your own hosted cipherclerk cell.",
        )),
        Ok(None) => Err(embeds::warning_embed(
            "No Cipherclerk",
            "Create a hosted cipherclerk with `/cipherclerk create` first.",
        )),
        Err(e) => Err(embeds::error_embed("Database Error", &e.to_string())),
    }
}
