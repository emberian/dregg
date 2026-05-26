//! `/send` and `/tip` commands — transfer tokens between users.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::cipherclerk::{UserCipherclerk, sign_legacy};
use crate::db::IdentityMode;
use crate::embeds;

/// Register the /send command.
pub fn register_send() -> CreateCommand {
    CreateCommand::new("send")
        .description("Send PYN tokens to another user")
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "Recipient").required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::Integer,
                "amount",
                "Amount of PYN to send",
            )
            .required(true)
            .min_int_value(1),
        )
}

/// Register the /tip command.
pub fn register_tip() -> CreateCommand {
    CreateCommand::new("tip")
        .description("Tip PYN tokens to another user")
        .add_option(
            CreateCommandOption::new(CommandOptionType::User, "user", "Recipient").required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount of PYN to tip")
                .required(true)
                .min_int_value(1),
        )
}

/// Handle /send or /tip interactions (same logic).
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let sender_id = command.user.id.get();
    let sender_discord = sender_id.to_string();

    defer_ephemeral(ctx, command).await;

    // Parse options.
    let recipient_user_id = command
        .data
        .options
        .iter()
        .find(|o| o.name == "user")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::User(uid) => Some(uid.get()),
            _ => None,
        });

    let amount = command
        .data
        .options
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        });

    let (recipient_id, amount) = match (recipient_user_id, amount) {
        (Some(r), Some(a)) => (r, a),
        _ => {
            let embed = embeds::error_embed("Invalid Arguments", "Usage: /send @user <amount>");
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    if recipient_id == sender_id {
        let embed = embeds::error_embed("Invalid Transfer", "You cannot send tokens to yourself.");
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let recipient_discord = recipient_id.to_string();

    // Verify sender has a hosted cclerk. External links are receive-only until
    // a proper external signing flow exists.
    let sender_cell = match state.db.get_user_identity(&sender_discord).await {
        Ok(Some(identity)) if identity.mode == IdentityMode::Hosted => identity.cell_id,
        Ok(Some(identity)) => {
            let embed = embeds::warning_embed(
                "External Signing Required",
                &format!(
                    "Your linked identity is `{}`. The Discord bot cannot sign transfers for external identities yet.",
                    identity.mode.as_str()
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You don't have a cclerk yet. Use `/cipherclerk create` first.",
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

    // Verify recipient has a cclerk.
    let recipient_cell = match state.db.get_cell_id(&recipient_discord).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "Recipient Has No Cipherclerk",
                &format!(
                    "<@{recipient_id}> does not have a dregg cclerk yet. They need to run `/cipherclerk create` first."
                ),
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

    // Derive sender's cclerk to sign the transfer.
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        sender_id,
        state.federation_id_bytes,
    );
    let signature = sign_transfer(&cclerk, &recipient_cell, amount);

    // Submit transfer to devnet.
    match state
        .devnet
        .submit_transfer(&sender_cell, &recipient_cell, amount, &signature)
        .await
    {
        Ok(tx_hash) => {
            // Record locally.
            let _ = state
                .db
                .record_transaction(&sender_discord, &recipient_discord, amount, &tx_hash)
                .await;

            let embed = embeds::success_embed("Transfer Sent")
                .field("To", format!("<@{recipient_id}>"), true)
                .field("Amount", format!("{amount} PYN"), true)
                .field(
                    "Tx Hash",
                    format!("`{}...`", &tx_hash[..16.min(tx_hash.len())]),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Transfer Failed",
                &format!(
                    "Devnet rejected the transfer: {e}\n\nThe devnet may be offline, or you may have insufficient balance."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign a transfer using the legacy BLAKE3-MAC wire scheme the current
/// devnet `/api/turns/submit` endpoint expects. The body is
/// `b"transfer:" + to_cell + b":" + amount_le_bytes` and the MAC is
/// `blake3(body || raw_secret)` per `cclerk::sign_legacy`.
///
/// When the devnet wire format moves to canonical signed Actions,
/// replace with `cclerk.app.make_action(...)` + post the action bytes.
fn sign_transfer(cclerk: &UserCipherclerk, to_cell: &str, amount: u64) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(b"transfer:");
    msg.extend_from_slice(to_cell.as_bytes());
    msg.extend_from_slice(b":");
    msg.extend_from_slice(&amount.to_le_bytes());
    sign_legacy(cclerk, &msg)
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
