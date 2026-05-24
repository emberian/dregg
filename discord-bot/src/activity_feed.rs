//! Background activity feed — polls devnet for new events and posts to configured channels.
//!
//! Spawns a tokio task that polls every ~5 seconds for new blocks/events, then
//! posts to the designated feed channel(s) using rich embeds. Rate-limited to
//! at most 1 message per 2 seconds to stay within Discord API limits.

use std::sync::Arc;
use std::time::Duration;

use serenity::all::{ChannelId, CreateEmbed, CreateMessage, Http, UserId};
use tokio::time;
use tracing::{debug, info, warn};

use crate::BotState;
use crate::devnet::RecentEvent;

/// Embed colors for different event types.
const COLOR_GREEN: u32 = 0x2A9D8F; // transfers, settlements
const COLOR_BLUE: u32 = 0x0077B6; // new cells, registrations
const COLOR_AMBER: u32 = 0xE9C46A; // auctions, orders
const COLOR_RED: u32 = 0xE63946; // liquidations, slashing

/// Start the activity feed background task.
///
/// This spawns a long-running tokio task that polls the devnet API and posts
/// new events to all configured feed channels.
pub fn start(state: Arc<BotState>, http: Arc<Http>) {
    tokio::spawn(async move {
        info!("Activity feed background task started");

        // Small initial delay to let the bot finish connecting.
        time::sleep(Duration::from_secs(3)).await;

        loop {
            if let Err(e) = poll_and_post(&state, &http).await {
                debug!("Activity feed poll error: {e}");
            }

            time::sleep(Duration::from_secs(5)).await;
        }
    });
}

/// One iteration of the poll loop: fetch new events and post them.
async fn poll_and_post(state: &BotState, http: &Http) -> Result<(), String> {
    let last_height = state
        .db
        .get_last_block_height()
        .await
        .map_err(|e| format!("db error: {e}"))?;

    let response = state
        .devnet
        .get_events_since(last_height)
        .await
        .map_err(|e| format!("devnet error: {e}"))?;

    if response.events.is_empty() {
        // Still update height if it advanced (empty block).
        if response.block_height > last_height {
            let _ = state.db.set_last_block_height(response.block_height).await;
        }
        return Ok(());
    }

    // Get all configured feed channels.
    let channels = state
        .db
        .get_all_feed_channels()
        .await
        .map_err(|e| format!("db error: {e}"))?;

    if channels.is_empty() {
        // No channels configured, just update the height.
        let _ = state.db.set_last_block_height(response.block_height).await;
        return Ok(());
    }

    // Post events (rate-limited: max 1 per 2 seconds, batch if needed).
    let batched = batch_events(&response.events);

    for embed in &batched {
        for (_guild_id, channel_id_str) in &channels {
            let channel_id = match channel_id_str.parse::<u64>() {
                Ok(id) => ChannelId::new(id),
                Err(_) => continue,
            };

            let msg = CreateMessage::new().embed(embed.clone());
            if let Err(e) = channel_id.send_message(http, msg).await {
                warn!("Failed to post to feed channel {channel_id}: {e}");
            }
        }

        // Rate limit: 2 seconds between messages.
        time::sleep(Duration::from_secs(2)).await;
    }

    // Notify watchers via DM.
    notify_watchers(state, http, &response.events).await;

    // Update last seen height.
    let _ = state.db.set_last_block_height(response.block_height).await;

    Ok(())
}

/// Batch events into embeds. If there are many events, group them to avoid
/// exceeding the rate limit. Up to 5 events per embed.
fn batch_events(events: &[RecentEvent]) -> Vec<CreateEmbed> {
    let mut embeds = Vec::new();

    // If few events, one embed per event.
    if events.len() <= 5 {
        for event in events {
            embeds.push(event_to_embed(event));
        }
    } else {
        // Batch into groups of 5.
        for chunk in events.chunks(5) {
            let mut description = String::new();
            let color = event_color(&chunk[0].event_type);

            for event in chunk {
                let icon = event_icon(&event.event_type);
                description.push_str(&format!(
                    "{icon} **{}**: {}\n",
                    event.event_type, event.summary
                ));
                if let Some(hash) = &event.tx_hash {
                    let short = if hash.len() > 12 { &hash[..12] } else { hash };
                    description.push_str(&format!(
                        "  [`{short}...`](https://devnet.pyana.fg-goose.online/explorer/tx/{hash})\n"
                    ));
                }
                description.push('\n');
            }

            let embed = CreateEmbed::new()
                .title("Activity Feed")
                .description(description)
                .color(color)
                .footer(serenity::all::CreateEmbedFooter::new(
                    "pyana devnet explorer",
                ));
            embeds.push(embed);
        }
    }

    embeds
}

/// Convert a single event into a rich embed.
fn event_to_embed(event: &RecentEvent) -> CreateEmbed {
    let color = event_color(&event.event_type);
    let icon = event_icon(&event.event_type);
    let title = format!("{icon} {}", event.event_type);

    let mut embed = CreateEmbed::new()
        .title(&title)
        .description(&event.summary)
        .color(color)
        .footer(serenity::all::CreateEmbedFooter::new(
            "pyana devnet explorer",
        ));

    if !event.timestamp.is_empty() {
        embed = embed.field("Time", &event.timestamp, true);
    }

    if let Some(cell_id) = &event.cell_id {
        let short = if cell_id.len() > 16 {
            &cell_id[..16]
        } else {
            cell_id
        };
        embed = embed.field(
            "Cell",
            format!("[`{short}...`](https://devnet.pyana.fg-goose.online/explorer/cell/{cell_id})"),
            true,
        );
    }

    if let Some(tx_hash) = &event.tx_hash {
        let short = if tx_hash.len() > 12 {
            &tx_hash[..12]
        } else {
            tx_hash
        };
        embed = embed.field(
            "Transaction",
            format!("[`{short}...`](https://devnet.pyana.fg-goose.online/explorer/tx/{tx_hash})"),
            true,
        );
    }

    embed
}

/// Get the embed color for an event type.
fn event_color(event_type: &str) -> u32 {
    match event_type.to_lowercase().as_str() {
        s if s.contains("transfer") || s.contains("settlement") || s.contains("settled") => {
            COLOR_GREEN
        }
        s if s.contains("cell") || s.contains("register") || s.contains("sovereign") => COLOR_BLUE,
        s if s.contains("auction") || s.contains("order") || s.contains("swap") => COLOR_AMBER,
        s if s.contains("liquidat") || s.contains("slash") => COLOR_RED,
        _ => COLOR_BLUE,
    }
}

/// Get the icon for an event type.
fn event_icon(event_type: &str) -> &'static str {
    match event_type.to_lowercase().as_str() {
        s if s.contains("transfer") || s.contains("settlement") || s.contains("settled") => {
            "\u{1f7e2}" // green circle
        }
        s if s.contains("cell") || s.contains("register") || s.contains("sovereign") => {
            "\u{1f535}" // blue circle
        }
        s if s.contains("auction") || s.contains("order") || s.contains("swap") => {
            "\u{1f7e1}" // yellow circle
        }
        s if s.contains("liquidat") || s.contains("slash") => {
            "\u{1f534}" // red circle
        }
        _ => "\u{26aa}", // white circle
    }
}

/// Notify users who are watching cells involved in the events.
async fn notify_watchers(state: &BotState, http: &Http, events: &[RecentEvent]) {
    for event in events {
        let Some(cell_id) = &event.cell_id else {
            continue;
        };

        let watchers = match state.db.get_watchers_for_cell(cell_id).await {
            Ok(w) => w,
            Err(_) => continue,
        };

        if watchers.is_empty() {
            continue;
        }

        let embed = event_to_embed(event);

        for watcher_id_str in &watchers {
            let user_id = match watcher_id_str.parse::<u64>() {
                Ok(id) => UserId::new(id),
                Err(_) => continue,
            };

            // Create DM channel and send.
            match user_id.create_dm_channel(http).await {
                Ok(dm) => {
                    let msg = CreateMessage::new().embed(embed.clone());
                    if let Err(e) = dm.send_message(http, msg).await {
                        debug!("Failed to DM watcher {user_id}: {e}");
                    }
                }
                Err(e) => {
                    debug!("Failed to create DM channel for {user_id}: {e}");
                }
            }

            // Rate limit DMs.
            time::sleep(Duration::from_millis(500)).await;
        }
    }
}
