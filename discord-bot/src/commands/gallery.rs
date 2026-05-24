//! `/gallery` command — list artworks, auctions, bid, mybids.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::embeds;
use crate::wallet::DerivedWallet;

/// Register the /gallery command.
pub fn register() -> CreateCommand {
    CreateCommand::new("gallery")
        .description("Browse and bid on devnet artworks")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "List artworks on devnet",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "auctions",
            "Show active auctions",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "bid",
                "Place a bid on an auction",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "auction_id",
                    "Auction ID to bid on",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::Integer, "amount", "Bid amount in PYN")
                    .required(true)
                    .min_int_value(1),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "mybids",
            "Show your active bids",
        ))
}

/// Handle /gallery interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "list" => handle_list(ctx, command, state).await,
        "auctions" => handle_auctions(ctx, command, state).await,
        "bid" => handle_bid(ctx, command, state).await,
        "mybids" => handle_mybids(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_list(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.list_artworks().await {
        Ok(artworks) => {
            if artworks.is_empty() {
                let embed =
                    embeds::pyana_embed("Gallery").description("No artworks on devnet yet.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for art in artworks.iter().take(10) {
                description.push_str(&format!(
                    "**{}** by {}\n{}\nID: `{}`\n\n",
                    art.title, art.artist, art.description, art.id
                ));
            }

            let embed = embeds::pyana_embed("Gallery")
                .description(description)
                .field("Total", artworks.len().to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Gallery Unavailable",
                &format!("Could not load artworks: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_auctions(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    defer_ephemeral(ctx, command).await;

    match state.devnet.list_auctions().await {
        Ok(auctions) => {
            if auctions.is_empty() {
                let embed = embeds::pyana_embed("Active Auctions")
                    .description("No active auctions right now.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for auction in auctions.iter().take(10) {
                let bidder_str = auction
                    .bidder
                    .as_deref()
                    .map(|b| format!("`{}...`", &b[..16.min(b.len())]))
                    .unwrap_or_else(|| "No bids yet".to_string());
                description.push_str(&format!(
                    "**{}** (ID: `{}`)\nCurrent: {} PYN | Top: {}\nEnds: {}\n\n",
                    auction.title, auction.id, auction.current_bid, bidder_str, auction.ends_at,
                ));
            }

            let embed = embeds::pyana_embed("Active Auctions")
                .description(description)
                .field("Total", auctions.len().to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Auctions Unavailable",
                &format!("Could not load auctions: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_bid(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();

    let sub_opts = match &command.data.options[0].value {
        CommandDataOptionValue::SubCommand(opts) => opts.clone(),
        _ => return,
    };

    let auction_id = sub_opts
        .iter()
        .find(|o| o.name == "auction_id")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();

    let amount = sub_opts
        .iter()
        .find(|o| o.name == "amount")
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Integer(n) => Some(*n as u64),
            _ => None,
        })
        .unwrap_or(0);

    defer_ephemeral(ctx, command).await;

    // Ensure user has a wallet.
    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to bid. Use `/wallet create` first.",
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
    let signature = sign_bid(&wallet, &auction_id, amount);

    match state
        .devnet
        .place_bid(&auction_id, &cell_id, amount, &signature)
        .await
    {
        Ok(()) => {
            let embed = embeds::success_embed("Bid Placed")
                .field("Auction", format!("`{auction_id}`"), true)
                .field("Amount", format!("{amount} PYN"), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Bid Failed", &format!("Could not place bid: {e}"));
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_mybids(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();

    defer_ephemeral(ctx, command).await;

    let cell_id = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(id)) => id,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Wallet",
                "You need a wallet to view bids. Use `/wallet create` first.",
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

    match state.devnet.get_user_bids(&cell_id).await {
        Ok(bids) => {
            if bids.is_empty() {
                let embed =
                    embeds::pyana_embed("Your Bids").description("You have no active bids.");
                let _ = command
                    .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                    .await;
                return;
            }

            let mut description = String::new();
            for bid in &bids {
                description.push_str(&format!(
                    "**{}** — {} PYN ({})\nAuction: `{}`\n\n",
                    bid.title, bid.amount, bid.status, bid.auction_id
                ));
            }

            let embed = embeds::pyana_embed("Your Bids")
                .description(description)
                .field("Active", bids.len().to_string(), true);
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Bids Unavailable",
                &format!("Could not load bids: {e}\n\nDevnet may be temporarily offline."),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign a bid message.
fn sign_bid(wallet: &DerivedWallet, auction_id: &str, amount: u64) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(b"bid:");
    msg.extend_from_slice(auction_id.as_bytes());
    msg.extend_from_slice(b":");
    msg.extend_from_slice(&amount.to_le_bytes());
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
