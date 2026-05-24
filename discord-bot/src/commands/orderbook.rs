//! `/order`, `/book`, `/trades` commands — orderbook interactions.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::wallet::DerivedWallet;

/// Register the /order command.
pub fn register_order() -> CreateCommand {
    CreateCommand::new("order")
        .description("Place or cancel limit orders")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "buy",
                "Place a limit buy order",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "pair",
                    "Trading pair (e.g. PYN/USDC)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Number, "price", "Limit price")
                    .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount to buy")
                    .required(true)
                    .min_int_value(1),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "sell",
                "Place a limit sell order",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "pair",
                    "Trading pair (e.g. PYN/USDC)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Number, "price", "Limit price")
                    .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "amount", "Amount to sell")
                    .required(true)
                    .min_int_value(1),
            ),
        )
        .add_option(
            CreateCommandOption::new(CommandOptionType::SubCommand, "cancel", "Cancel an order")
                .add_sub_option(
                    CreateCommandOption::new(CommandOptionType::String, "id", "Order ID to cancel")
                        .required(true),
                ),
        )
}

/// Register the /book command.
pub fn register_book() -> CreateCommand {
    CreateCommand::new("book")
        .description("Show the orderbook for a trading pair")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "pair",
                "Trading pair (e.g. PYN/USDC)",
            )
            .required(true),
        )
}

/// Register the /trades command.
pub fn register_trades() -> CreateCommand {
    CreateCommand::new("trades")
        .description("Show recent trades for a pair")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "pair",
                "Trading pair (e.g. PYN/USDC)",
            )
            .required(true),
        )
}

/// Handle /order interactions.
pub async fn handle_order(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "buy" => handle_place_order(ctx, command, state, "buy").await,
        "sell" => handle_place_order(ctx, command, state, "sell").await,
        "cancel" => handle_cancel(ctx, command, state).await,
        _ => {}
    }
}

/// Handle /book interactions.
pub async fn handle_book(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let pair = get_top_string_option(&command.data.options, "pair");

    match state.devnet.get_orderbook(&pair).await {
        Ok(book) => {
            let mut bids_str = String::new();
            for level in book.bids.iter().take(5) {
                bids_str.push_str(&format!("{:.4} | {}\n", level.price, level.amount));
            }
            if bids_str.is_empty() {
                bids_str = "No bids".to_string();
            }

            let mut asks_str = String::new();
            for level in book.asks.iter().take(5) {
                asks_str.push_str(&format!("{:.4} | {}\n", level.price, level.amount));
            }
            if asks_str.is_empty() {
                asks_str = "No asks".to_string();
            }

            let embed = embeds::pyana_embed(&format!("Orderbook: {}", book.pair))
                .field("Bids (Price | Amount)", format!("```\n{bids_str}```"), true)
                .field("Asks (Price | Amount)", format!("```\n{asks_str}```"), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Orderbook Unavailable",
                &format!("Could not load orderbook: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Handle /trades interactions.
pub async fn handle_trades(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    let pair = get_top_string_option(&command.data.options, "pair");

    match state.devnet.get_trades(&pair, 10).await {
        Ok(trades) => {
            if trades.is_empty() {
                let embed = embeds::pyana_embed(&format!("Recent Trades: {pair}"))
                    .description("No recent trades for this pair.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for trade in &trades {
                let icon = if trade.side == "buy" {
                    "\u{1f7e2}"
                } else {
                    "\u{1f534}"
                };
                description.push_str(&format!(
                    "{icon} {:.4} | {} | {}\n",
                    trade.price, trade.amount, trade.timestamp
                ));
            }

            let embed = embeds::pyana_embed(&format!("Recent Trades: {pair}"))
                .description(format!("```\n{description}```"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Trades Unavailable",
                &format!("Could not load trades: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_place_order(
    ctx: &Context,
    command: &CommandInteraction,
    state: &BotState,
    side: &str,
) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let pair = sub_opts
        .iter()
        .find(|o| o.name == "pair")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    let price = sub_opts
        .iter()
        .find(|o| o.name == "price")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Number(n) => Some(*n),
            _ => None,
        })
        .unwrap_or(0.0);

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
                "You need a wallet to place orders. Use `/wallet create` first.",
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
    let signature = sign_action(&wallet, &format!("order:{side}:{pair}:{price}:{amount}"));

    match state
        .devnet
        .place_order(&cell_id, &pair, side, price, amount, &signature)
        .await
    {
        Ok(order_id) => {
            let embed = embeds::success_embed("Order Placed")
                .field("Side", side.to_uppercase(), true)
                .field("Pair", &pair, true)
                .field("Price", format!("{price:.4}"), true)
                .field("Amount", amount.to_string(), true)
                .field("Order ID", format!("`{order_id}`"), false);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Order Failed", &format!("Could not place order: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_cancel(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let order_id = sub_opts
        .iter()
        .find(|o| o.name == "id")
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
                "You need a wallet to cancel orders. Use `/wallet create` first.",
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
    let signature = sign_action(&wallet, &format!("cancel:{order_id}"));

    match state
        .devnet
        .cancel_order(&order_id, &cell_id, &signature)
        .await
    {
        Ok(()) => {
            let embed = embeds::success_embed("Order Cancelled").field(
                "Order ID",
                format!("`{order_id}`"),
                true,
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed =
                embeds::error_embed("Cancel Failed", &format!("Could not cancel order: {e}"));
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
