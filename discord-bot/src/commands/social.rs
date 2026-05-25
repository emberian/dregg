//! `/faucet`, `/leaderboard`, `/history` commands — social and community features.

use serenity::all::{
    CommandInteraction, Context, CreateCommand, CreateInteractionResponse,
    CreateInteractionResponseMessage, EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;

/// Register the /faucet command.
pub fn register_faucet() -> CreateCommand {
    CreateCommand::new("faucet").description("Claim free PYN tokens (1 per hour)")
}

/// Register the /leaderboard command.
pub fn register_leaderboard() -> CreateCommand {
    CreateCommand::new("leaderboard").description("Show top PYN holders")
}

/// Register the /history command.
pub fn register_history() -> CreateCommand {
    CreateCommand::new("history").description("Show your transaction history")
}

/// Handle /faucet interaction.
pub async fn handle_faucet(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let discord_id = user_id.to_string();

    defer_ephemeral(ctx, command).await;

    // Check cclerk exists.
    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to use the faucet. Use `/cipherclerk create` first.",
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

    // Check rate limit (1 per hour).
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;

    match state.db.get_last_faucet_claim(&discord_id).await {
        Ok(Some(last_claim)) => {
            let elapsed = now - last_claim;
            if elapsed < 3600 {
                let remaining = 3600 - elapsed;
                let mins = remaining / 60;
                let secs = remaining % 60;
                let embed = embeds::warning_embed(
                    "Rate Limited",
                    &format!(
                        "You can claim again in **{mins}m {secs}s**.\n\nThe faucet allows 1 claim per hour."
                    ),
                );
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }
        }
        Ok(None) => {} // First claim ever.
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    }

    // Request from devnet faucet.
    match state.devnet.faucet_request(&cell_id).await {
        Ok(amount) => {
            // Record the claim.
            let _ = state.db.set_faucet_claim(&discord_id, now).await;
            // Also record as a transaction for leaderboard.
            let _ = state
                .db
                .record_transaction("faucet", &discord_id, amount, "faucet")
                .await;

            let embed = embeds::success_embed("Faucet Claimed")
                .field("Amount", format!("{amount} PYN"), true)
                .field("Next Claim", "In 1 hour", true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Faucet Error",
                &format!("Could not claim from faucet: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /leaderboard interaction (NOT ephemeral — visible to all).
pub async fn handle_leaderboard(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Leaderboard is public — not ephemeral.
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(CreateInteractionResponseMessage::new()),
        )
        .await;

    match state.db.get_leaderboard(10).await {
        Ok(entries) => {
            if entries.is_empty() {
                let embed = embeds::pyana_embed("Leaderboard")
                    .description("No transactions recorded yet. Be the first to use `/faucet`!");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for (i, (user_id, total)) in entries.iter().enumerate() {
                let medal = match i {
                    0 => "\u{1f947}",
                    1 => "\u{1f948}",
                    2 => "\u{1f949}",
                    _ => "\u{25ab}\u{fe0f}",
                };
                let user_display = if user_id == "faucet" {
                    "Faucet".to_string()
                } else {
                    format!("<@{user_id}>")
                };
                description.push_str(&format!(
                    "{medal} **#{}** {user_display} — {total} PYN\n",
                    i + 1
                ));
            }

            let embed = embeds::pyana_embed("Leaderboard").description(description);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Leaderboard Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /history interaction.
pub async fn handle_history(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    // Ensure user has a cclerk.
    if !state.db.user_exists(&discord_id).await.unwrap_or(false) {
        let embed = embeds::warning_embed(
            "No Cipherclerk",
            "You need a cclerk to view history. Use `/cipherclerk create` first.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    match state.db.get_user_transactions(&discord_id, 15).await {
        Ok(txs) => {
            if txs.is_empty() {
                let embed =
                    embeds::pyana_embed("Transaction History").description("No transactions yet.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for tx in &txs {
                let direction = if tx.from_user == discord_id {
                    let to_display = if tx.to_user == "faucet" {
                        "Faucet".to_string()
                    } else {
                        format!("<@{}>", tx.to_user)
                    };
                    format!("\u{1f4e4} Sent {} PYN to {to_display}", tx.amount)
                } else {
                    let from_display = if tx.from_user == "faucet" {
                        "Faucet".to_string()
                    } else {
                        format!("<@{}>", tx.from_user)
                    };
                    format!("\u{1f4e5} Received {} PYN from {from_display}", tx.amount)
                };
                description.push_str(&format!("{direction}\n<t:{}:R>\n\n", tx.timestamp));
            }

            let embed = embeds::pyana_embed("Transaction History").description(description);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("History Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
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
