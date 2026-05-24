//! CapTP client: the bot's own identity and capability session management.
//!
//! The bot IS a pyana participant — it has its own keypair, holds live references,
//! and can enliven/export/revoke sturdy refs via its configured pyana node.

use std::collections::HashMap;

use pyana_captp::FederationId as GroupId;
use pyana_captp::uri::PyanaUri;
use tokio::sync::RwLock;
use tracing::{debug, info};

/// A held capability reference with metadata.
#[derive(Debug, Clone)]
pub struct HeldCapability {
    /// The URI of this capability (sturdy ref form).
    pub uri: PyanaUri,
    /// Human-readable label (optional).
    pub label: Option<String>,
    /// Who shared this with us (Discord user ID, if applicable).
    pub shared_by: Option<u64>,
    /// When we acquired this cap.
    pub acquired_at: u64,
    /// Whether this cap is currently live (enlivened).
    pub live: bool,
}

/// A capability we have exported (shared with someone).
#[derive(Debug, Clone)]
pub struct ExportedCapability {
    /// The cell ID we exported.
    pub cell_id: String,
    /// The pyana URI the recipient can use.
    pub uri: PyanaUri,
    /// Who we shared it with (Discord user ID).
    pub shared_with: Option<u64>,
    /// When we exported it.
    pub exported_at: u64,
    /// Whether it's been revoked.
    pub revoked: bool,
}

/// The bot's CapTP client — manages its identity, held caps, and exports.
#[derive(Debug)]
pub struct CapTPClient {
    /// The bot's own federation ID.
    pub federation_id: GroupId,
    /// The bot's cell ID (hex).
    pub bot_cell_id: String,
    /// The configured pyana node URL.
    pub node_url: String,
    /// Held capabilities (keyed by cell ID).
    held: RwLock<HashMap<String, HeldCapability>>,
    /// Exported capabilities (keyed by cell ID).
    exports: RwLock<HashMap<String, ExportedCapability>>,
    /// HTTP client for node communication.
    http: reqwest::Client,
}

impl CapTPClient {
    /// Create a new CapTP client for the bot.
    pub fn new(federation_id: GroupId, bot_cell_id: String, node_url: String) -> Self {
        Self {
            federation_id,
            bot_cell_id,
            node_url,
            held: RwLock::new(HashMap::new()),
            exports: RwLock::new(HashMap::new()),
            http: reqwest::Client::new(),
        }
    }

    /// Export a cell as a sturdy ref, returning the pyana URI.
    pub async fn export_cap(&self, cell_id: &str) -> Result<PyanaUri, CapTPError> {
        // Request the node to create a swiss entry and return the URI.
        let url = format!("{}/captp/export", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "cell_id": cell_id,
                "exporter": self.bot_cell_id,
            }))
            .send()
            .await
            .map_err(|e| CapTPError::NodeUnreachable(e.to_string()))?;

        if !resp.status().is_success() {
            let status = resp.status().as_u16();
            let body = resp.text().await.unwrap_or_default();
            return Err(CapTPError::NodeError {
                status,
                message: body,
            });
        }

        let result: ExportResponse = resp
            .json()
            .await
            .map_err(|e| CapTPError::DeserializationFailed(e.to_string()))?;

        let uri =
            PyanaUri::parse(&result.uri).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;

        // Track the export.
        let export = ExportedCapability {
            cell_id: cell_id.to_string(),
            uri: uri.clone(),
            shared_with: None,
            exported_at: current_epoch(),
            revoked: false,
        };
        self.exports
            .write()
            .await
            .insert(cell_id.to_string(), export);

        info!(cell_id, "Exported capability as sturdy ref");
        Ok(uri)
    }

    /// Enliven a pyana URI — the bot accepts and holds the live reference.
    pub async fn accept_cap(&self, uri_str: &str) -> Result<HeldCapability, CapTPError> {
        let uri = PyanaUri::parse(uri_str).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;

        // Request the node to enliven the URI.
        let url = format!("{}/captp/enliven", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "uri": uri_str,
                "recipient": self.bot_cell_id,
            }))
            .send()
            .await
            .map_err(|e| CapTPError::NodeUnreachable(e.to_string()))?;

        if !resp.status().is_success() {
            let status = resp.status().as_u16();
            let body = resp.text().await.unwrap_or_default();
            return Err(CapTPError::NodeError {
                status,
                message: body,
            });
        }

        let cell_id = hex::encode(uri.cell_id);
        let cap = HeldCapability {
            uri,
            label: None,
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };

        self.held.write().await.insert(cell_id.clone(), cap.clone());
        info!(cell_id, "Enlivened and holding capability");
        Ok(cap)
    }

    /// Create a handoff certificate delegating a capability to a recipient.
    pub async fn delegate_cap(
        &self,
        cell_id: &str,
        recipient_key: &str,
    ) -> Result<String, CapTPError> {
        let url = format!("{}/captp/handoff", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "cell_id": cell_id,
                "introducer": self.bot_cell_id,
                "recipient_key": recipient_key,
            }))
            .send()
            .await
            .map_err(|e| CapTPError::NodeUnreachable(e.to_string()))?;

        if !resp.status().is_success() {
            let status = resp.status().as_u16();
            let body = resp.text().await.unwrap_or_default();
            return Err(CapTPError::NodeError {
                status,
                message: body,
            });
        }

        let result: HandoffResponse = resp
            .json()
            .await
            .map_err(|e| CapTPError::DeserializationFailed(e.to_string()))?;

        debug!(cell_id, recipient_key, "Created handoff certificate");
        Ok(result.certificate)
    }

    /// Revoke a previously exported capability.
    pub async fn revoke_cap(&self, cell_id: &str) -> Result<(), CapTPError> {
        let url = format!("{}/captp/revoke", self.node_url);
        let resp = self
            .http
            .post(&url)
            .json(&serde_json::json!({
                "cell_id": cell_id,
                "revoker": self.bot_cell_id,
            }))
            .send()
            .await
            .map_err(|e| CapTPError::NodeUnreachable(e.to_string()))?;

        if !resp.status().is_success() {
            let status = resp.status().as_u16();
            let body = resp.text().await.unwrap_or_default();
            return Err(CapTPError::NodeError {
                status,
                message: body,
            });
        }

        // Mark as revoked in our local state.
        if let Some(export) = self.exports.write().await.get_mut(cell_id) {
            export.revoked = true;
        }
        // Remove from held if we hold it.
        self.held.write().await.remove(cell_id);

        info!(cell_id, "Revoked capability");
        Ok(())
    }

    /// List all held capabilities.
    pub async fn list_held(&self) -> Vec<(String, HeldCapability)> {
        self.held
            .read()
            .await
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    /// List all exports.
    pub async fn list_exports(&self) -> Vec<(String, ExportedCapability)> {
        self.exports
            .read()
            .await
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
}

// ─── Wire types ─────────────────────────────────────────────────────────────

#[derive(serde::Deserialize)]
struct ExportResponse {
    uri: String,
}

#[derive(serde::Deserialize)]
struct HandoffResponse {
    certificate: String,
}

// ─── Errors ─────────────────────────────────────────────────────────────────

/// Errors from CapTP client operations.
#[derive(Debug, Clone)]
pub enum CapTPError {
    /// Could not reach the configured pyana node.
    NodeUnreachable(String),
    /// The node returned an error.
    NodeError { status: u16, message: String },
    /// Failed to parse a pyana URI.
    InvalidUri(String),
    /// Deserialization of node response failed.
    DeserializationFailed(String),
    /// The requested capability was not found.
    NotFound(String),
}

impl std::fmt::Display for CapTPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapTPError::NodeUnreachable(e) => write!(f, "node unreachable: {e}"),
            CapTPError::NodeError { status, message } => {
                write!(f, "node error (HTTP {status}): {message}")
            }
            CapTPError::InvalidUri(e) => write!(f, "invalid pyana URI: {e}"),
            CapTPError::DeserializationFailed(e) => write!(f, "deserialization failed: {e}"),
            CapTPError::NotFound(id) => write!(f, "capability not found: {id}"),
        }
    }
}

impl std::error::Error for CapTPError {}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn current_epoch() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}
