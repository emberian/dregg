//! Bidirectional integration: Discord actions as capabilities, Discord events as turns.
//!
//! This module defines:
//! 1. `DiscordCapability` — capabilities that, when exercised via CapTP, trigger Discord actions.
//! 2. Event handlers that emit pyana turns when Discord events occur.

use std::collections::HashMap;
use std::sync::Arc;

use serenity::all::{ChannelId, GuildId, Http, Message, MessageId, RoleId, UserId};
use tokio::sync::RwLock;
use tracing::{debug, info, warn};

// =============================================================================
// Discord capabilities (pyana → Discord direction)
// =============================================================================

/// The kind of Discord channel to create.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum ChannelKind {
    Text,
    Voice,
    Forum,
    Announcement,
}

/// Capabilities that, when exercised via CapTP, trigger Discord actions.
/// Each variant is a cell with a sturdy ref. Someone holding the capability
/// can trigger the action by exercising the cap via CapTP from any pyana client.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum DiscordCapability {
    /// Send a message to a channel.
    SendMessage { channel_id: u64, content: String },
    /// Assign a role to a user.
    AssignRole {
        guild_id: u64,
        user_id: u64,
        role_id: u64,
    },
    /// Create a channel in a guild.
    CreateChannel {
        guild_id: u64,
        name: String,
        kind: ChannelKind,
    },
    /// Pin a message.
    PinMessage { channel_id: u64, message_id: u64 },
    /// React to a message.
    AddReaction {
        channel_id: u64,
        message_id: u64,
        emoji: String,
    },
}

/// A registered Discord capability with its cell ID and metadata.
#[derive(Debug, Clone)]
pub struct RegisteredDiscordCap {
    /// The cell ID for this capability.
    pub cell_id: String,
    /// The pyana URI (sturdy ref) for this capability.
    pub uri: Option<String>,
    /// The capability definition.
    pub capability: DiscordCapability,
    /// Guild this belongs to.
    pub guild_id: u64,
    /// Who registered it.
    pub registered_by: u64,
}

/// Registry of Discord capabilities that can be exercised via CapTP.
#[derive(Debug)]
pub struct DiscordCapRegistry {
    /// Map from cell_id to registered capability.
    caps: RwLock<HashMap<String, RegisteredDiscordCap>>,
}

impl DiscordCapRegistry {
    pub fn new() -> Self {
        Self {
            caps: RwLock::new(HashMap::new()),
        }
    }

    /// Register a new Discord capability.
    pub async fn register(&self, cap: RegisteredDiscordCap) {
        let cell_id = cap.cell_id.clone();
        self.caps.write().await.insert(cell_id.clone(), cap);
        info!(cell_id, "Registered Discord capability");
    }

    /// Exercise a capability — execute the Discord action.
    pub async fn exercise(&self, cell_id: &str, http: &Arc<Http>) -> Result<(), DiscordCapError> {
        let caps = self.caps.read().await;
        let cap = caps
            .get(cell_id)
            .ok_or_else(|| DiscordCapError::NotFound(cell_id.to_string()))?;

        match &cap.capability {
            DiscordCapability::SendMessage {
                channel_id,
                content,
            } => {
                let channel = ChannelId::new(*channel_id);
                channel
                    .say(http, content)
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?;
            }
            DiscordCapability::AssignRole {
                guild_id,
                user_id,
                role_id,
            } => {
                let guild = GuildId::new(*guild_id);
                let user = UserId::new(*user_id);
                let role = RoleId::new(*role_id);
                guild
                    .member(http, user)
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?
                    .add_role(http, role)
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?;
            }
            DiscordCapability::CreateChannel {
                guild_id,
                name,
                kind,
            } => {
                let guild = GuildId::new(*guild_id);
                let channel_type = match kind {
                    ChannelKind::Text => serenity::all::ChannelType::Text,
                    ChannelKind::Voice => serenity::all::ChannelType::Voice,
                    ChannelKind::Forum => serenity::all::ChannelType::Forum,
                    ChannelKind::Announcement => serenity::all::ChannelType::News,
                };
                guild
                    .create_channel(
                        http,
                        serenity::all::CreateChannel::new(name).kind(channel_type),
                    )
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?;
            }
            DiscordCapability::PinMessage {
                channel_id,
                message_id,
            } => {
                let channel = ChannelId::new(*channel_id);
                let msg_id = MessageId::new(*message_id);
                channel
                    .pin(http, msg_id)
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?;
            }
            DiscordCapability::AddReaction {
                channel_id,
                message_id,
                emoji,
            } => {
                let channel = ChannelId::new(*channel_id);
                let msg_id = MessageId::new(*message_id);
                let reaction = serenity::all::ReactionType::Unicode(emoji.clone());
                channel
                    .create_reaction(http, msg_id, reaction)
                    .await
                    .map_err(|e| DiscordCapError::DiscordApi(e.to_string()))?;
            }
        }

        debug!(cell_id, "Exercised Discord capability");
        Ok(())
    }

    /// List all registered capabilities for a guild.
    pub async fn list_for_guild(&self, guild_id: u64) -> Vec<RegisteredDiscordCap> {
        self.caps
            .read()
            .await
            .values()
            .filter(|c| c.guild_id == guild_id)
            .cloned()
            .collect()
    }

    /// Unregister a capability.
    pub async fn unregister(&self, cell_id: &str) -> bool {
        self.caps.write().await.remove(cell_id).is_some()
    }
}

/// Errors from Discord capability operations.
#[derive(Debug, Clone)]
pub enum DiscordCapError {
    /// Capability not found in registry.
    NotFound(String),
    /// Discord API error.
    DiscordApi(String),
    /// Unauthorized (invoker doesn't hold the cap).
    Unauthorized(String),
}

impl std::fmt::Display for DiscordCapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiscordCapError::NotFound(id) => write!(f, "capability not found: {id}"),
            DiscordCapError::DiscordApi(e) => write!(f, "Discord API error: {e}"),
            DiscordCapError::Unauthorized(e) => write!(f, "unauthorized: {e}"),
        }
    }
}

impl std::error::Error for DiscordCapError {}

// =============================================================================
// Discord events → Pyana turns (Discord → pyana direction)
// =============================================================================

/// Queue link configuration: maps a Discord channel to a pyana programmable queue.
#[derive(Debug, Clone)]
pub struct ChannelQueueLink {
    /// Discord channel ID.
    pub channel_id: u64,
    /// Guild ID.
    pub guild_id: u64,
    /// Queue name in the pyana namespace.
    pub queue_name: String,
    /// Full namespace path (e.g., /discord/<guild-id>/<name>).
    pub namespace_path: String,
}

/// Event bridge: converts Discord events into pyana turns.
#[derive(Debug)]
pub struct EventBridge {
    /// Active channel-to-queue links.
    channel_links: RwLock<HashMap<u64, ChannelQueueLink>>,
    /// Node URL for submitting turns.
    node_url: String,
    /// HTTP client.
    http: reqwest::Client,
}

impl EventBridge {
    pub fn new(node_url: String) -> Self {
        Self {
            channel_links: RwLock::new(HashMap::new()),
            node_url,
            http: reqwest::Client::new(),
        }
    }

    /// Link a channel to a programmable queue.
    pub async fn link_channel(&self, link: ChannelQueueLink) {
        let channel_id = link.channel_id;
        self.channel_links.write().await.insert(channel_id, link);
        info!(channel_id, "Linked channel to pyana queue");
    }

    /// Unlink a channel.
    pub async fn unlink_channel(&self, channel_id: u64) -> bool {
        self.channel_links
            .write()
            .await
            .remove(&channel_id)
            .is_some()
    }

    /// Handle a Discord message event — enqueue into linked pyana queue if applicable.
    pub async fn on_message(&self, msg: &Message) {
        let channel_id = msg.channel_id.get();
        let links = self.channel_links.read().await;

        if let Some(link) = links.get(&channel_id) {
            let payload = serde_json::json!({
                "type": "message",
                "channel_id": channel_id,
                "guild_id": link.guild_id,
                "author_id": msg.author.id.get(),
                "author_name": msg.author.name,
                "content": msg.content,
                "timestamp": msg.timestamp.to_string(),
                "queue": link.queue_name,
            });

            if let Err(e) = self.submit_turn(&link.namespace_path, payload).await {
                warn!(
                    channel_id,
                    queue = link.queue_name,
                    error = %e,
                    "Failed to enqueue message into pyana queue"
                );
            }
        }
    }

    /// Handle a role change event — emit GrantCapability or RevokeCapability effect.
    pub async fn on_role_change(&self, guild_id: u64, user_id: u64, role_id: u64, added: bool) {
        let effect_type = if added {
            "GrantCapability"
        } else {
            "RevokeCapability"
        };

        let payload = serde_json::json!({
            "type": effect_type,
            "guild_id": guild_id,
            "user_id": user_id,
            "role_id": role_id,
            "added": added,
        });

        let path = format!("/discord/{guild_id}/roles");
        if let Err(e) = self.submit_turn(&path, payload).await {
            warn!(
                guild_id,
                user_id,
                role_id,
                error = %e,
                "Failed to emit role change turn"
            );
        }
    }

    /// Handle a reaction event — if it's on a governance proposal, count as a vote.
    pub async fn on_reaction(
        &self,
        guild_id: u64,
        channel_id: u64,
        message_id: u64,
        user_id: u64,
        emoji: &str,
        added: bool,
    ) {
        let vote = match emoji {
            "\u{1f44d}" | "+1" => Some(true),  // thumbs up = yes
            "\u{1f44e}" | "-1" => Some(false), // thumbs down = no
            _ => None,
        };

        if let Some(vote_yes) = vote {
            let payload = serde_json::json!({
                "type": "ReactionVote",
                "guild_id": guild_id,
                "channel_id": channel_id,
                "message_id": message_id,
                "user_id": user_id,
                "vote": if vote_yes { "yes" } else { "no" },
                "added": added,
            });

            let path = format!("/discord/{guild_id}/governance");
            if let Err(e) = self.submit_turn(&path, payload).await {
                warn!(
                    guild_id,
                    message_id,
                    error = %e,
                    "Failed to emit reaction vote turn"
                );
            }
        }
    }

    /// Submit a turn to the pyana node.
    async fn submit_turn(
        &self,
        namespace_path: &str,
        payload: serde_json::Value,
    ) -> Result<(), String> {
        let url = format!("{}/turns/submit", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "namespace_path": namespace_path,
                "payload": payload,
            }))
            .send()
            .await
            .map_err(|e| e.to_string())?;

        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            return Err(format!("node returned error: {body}"));
        }

        Ok(())
    }
}
