//! `/swap`, `/pool`, `/lend` commands — AMM and lending protocol interactions.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::wallet::DerivedWallet;

/// Register the /swap command.
pub fn register_swap() -> CreateCommand {
    CreateCommand::new("swap")
        .description("Swap tokens on the AMM")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "from", "Token to sell")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "to", "Token to buy")
                .required(true),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount to swap")
                .required(true)
                .min_int_value(1),
        )
}

/// Register the /pool command.
pub fn register_pool() -> CreateCommand {
    CreateCommand::new("pool")
        .description("Get pool info")
        .add_option(
            CreateCommandOption::new(CommandOptionType::String, "pool_id", "Pool ID to query")
                .required(true),
        )
}

/// Register the /lend command.
pub fn register_lend() -> CreateCommand {
    CreateCommand::new("lend")
        .description("Lending protocol operations")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "supply",
                "Supply tokens to the lending pool",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount to supply")
                    .required(true)
                    .min_int_value(1),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "borrow",
                "Borrow tokens from the lending pool",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount to borrow")
                    .required(true)
                    .min_int_value(1),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "status",
            "View your lending positions",
        ))
}

/// Handle /swap interactions.
pub async fn handle_swap(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    defer_ephemeral(ctx, command).await;

    let from_token = get_top_string_option(&command.data.options, "from");
    let to_token = get_top_string_option(&command.data.options, "to");
    let amount = command
        .data
        .options
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        })
        .unwrap_or(0);

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to swap. Use `/wallet create` first.",
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
    let signature = sign_action(&wallet, &format!("swap:{from_token}:{to_token}:{amount}"));

    match state
        .devnet
        .amm_swap(&cell_id, &from_token, &to_token, amount, &signature)
        .await
    {
        Ok(result) => {
            let embed = embeds::success_embed("Swap Executed")
                .field("Sold", format!("{amount} {from_token}"), true)
                .field(
                    "Received",
                    format!("{} {to_token}", result.amount_out),
                    true,
                )
                .field(
                    "Price Impact",
                    format!("{:.2}%", result.price_impact * 100.0),
                    true,
                )
                .field(
                    "Tx Hash",
                    format!("`{}...`", &result.tx_hash[..16.min(result.tx_hash.len())]),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Swap Failed",
                &format!(
                    "Could not execute swap: {e}\n\nDevnet may be offline or pool may have insufficient liquidity."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /pool interactions.
pub async fn handle_pool(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let pool_id = get_top_string_option(&command.data.options, "pool_id");

    match state.devnet.get_pool(&pool_id).await {
        Ok(pool) => {
            let embed = embeds::pyana_embed(&format!("Pool: {}", pool.pool_id))
                .field("Token A", &pool.token_a, true)
                .field("Token B", &pool.token_b, true)
                .field("Reserve A", pool.reserve_a.to_string(), true)
                .field("Reserve B", pool.reserve_b.to_string(), true)
                .field("TVL", format!("{} PYN", pool.tvl), true)
                .field("Fee Rate", format!("{:.2}%", pool.fee_rate * 100.0), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Pool Not Found",
                &format!("Could not load pool info: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /lend interactions.
pub async fn handle_lend(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "supply" => handle_lend_supply(ctx, command, state).await,
        "borrow" => handle_lend_borrow(ctx, command, state).await,
        "status" => handle_lend_status(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_lend_supply(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let amount = sub_opts
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        })
        .unwrap_or(0);

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to supply. Use `/wallet create` first.",
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
    let signature = sign_action(&wallet, &format!("lend:supply:{amount}"));

    match state.devnet.lend_supply(&cell_id, amount, &signature).await {
        Ok(()) => {
            let embed = embeds::success_embed("Supply Successful").field(
                "Supplied",
                format!("{amount} PYN"),
                true,
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Supply Failed", &format!("Could not supply: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_lend_borrow(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let amount = sub_opts
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        })
        .unwrap_or(0);

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to borrow. Use `/wallet create` first.",
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
    let signature = sign_action(&wallet, &format!("lend:borrow:{amount}"));

    match state.devnet.lend_borrow(&cell_id, amount, &signature).await {
        Ok(()) => {
            let embed = embeds::success_embed("Borrow Successful").field(
                "Borrowed",
                format!("{amount} PYN"),
                true,
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Borrow Failed", &format!("Could not borrow: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_lend_status(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to view positions. Use `/wallet create` first.",
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

    match state.devnet.lend_status(&cell_id).await {
        Ok(status) => {
            let embed = embeds::pyana_embed("Lending Positions")
                .field("Supplied", format!("{} PYN", status.supplied), true)
                .field("Borrowed", format!("{} PYN", status.borrowed), true)
                .field(
                    "Collateral Ratio",
                    format!("{:.1}%", status.collateral_ratio * 100.0),
                    true,
                )
                .field(
                    "Accrued Interest",
                    format!("{} PYN", status.accrued_interest),
                    true,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Status Unavailable",
                &format!(
                    "Could not load lending status: {e}\n\nDevnet may be temporarily offline."
                ),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign an action message using BLAKE3.
fn sign_action(wallet: &DerivedWallet, action: &str) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(action.as_bytes());
    msg.extend_from_slice(&wallet.private_key);
    let sig = blake3::hash(&msg);
    hex::encode(sig.as_bytes())
}

fn get_top_string_option(options: &[serenity::all::CommandDataOption], name: &str) -> String {
    options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default()
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
