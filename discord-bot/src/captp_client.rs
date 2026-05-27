//! CapTP client: the bot's own identity and capability session management.
//!
//! The bot IS a dregg participant — it has its own keypair, holds live references,
//! and tracks sturdy refs it has locally exported or accepted. The dregg node does
//! not currently serve `/captp/export`, `/captp/enliven`, `/captp/handoff`, or
//! `/captp/revoke`; this client must not pretend those HTTP endpoints exist.

use std::collections::HashMap;
use std::io::Read;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_captp::FederationId as GroupId;
use dregg_captp::uri::DreggUri;
use tokio::sync::RwLock;
use tracing::{debug, info};

/// A held capability reference with metadata.
#[derive(Debug, Clone)]
pub struct HeldCapability {
    /// The URI of this capability (sturdy ref form).
    pub uri: DreggUri,
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
    /// The dregg URI the recipient can use.
    pub uri: DreggUri,
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
    /// The configured dregg node URL.
    pub node_url: String,
    /// Held capabilities (keyed by cell ID).
    held: RwLock<HashMap<String, HeldCapability>>,
    /// Exported capabilities (keyed by cell ID).
    exports: RwLock<HashMap<String, ExportedCapability>>,
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
        }
    }

    /// Export a cell as a sturdy ref, returning the dregg URI.
    pub async fn export_cap(&self, cell_id: &str) -> Result<DreggUri, CapTPError> {
        let cell_bytes = parse_cell_id(cell_id)?;
        let uri = DreggUri {
            federation_id: self.federation_id.0,
            cell_id: cell_bytes,
            swiss: new_swiss(cell_id, &self.bot_cell_id, self.federation_id.0),
        };

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

    /// Enliven a dregg URI — the bot accepts and holds the live reference.
    pub async fn accept_cap(&self, uri_str: &str) -> Result<HeldCapability, CapTPError> {
        let uri = DreggUri::parse(uri_str).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;

        let cell_id = hex::encode(uri.cell_id);
        let exports = self.exports.read().await;
        let Some(export) = exports.get(&cell_id) else {
            return Err(CapTPError::Unsupported(format!(
                "remote enliven is not implemented; URI `{cell_id}` was not exported by this bot instance"
            )));
        };
        if export.revoked {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (local export is revoked)"
            )));
        }
        if export.uri != uri {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (swiss number does not match this bot's active export)"
            )));
        }
        drop(exports);

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
        debug!(cell_id, recipient_key, "Handoff requested but unsupported");
        Err(CapTPError::Unsupported(
            "CapTP handoff certificates are not available through the node HTTP API yet"
                .to_string(),
        ))
    }

    /// Revoke a previously exported capability.
    pub async fn revoke_cap(&self, cell_id: &str) -> Result<(), CapTPError> {
        parse_cell_id(cell_id)?;

        let mut exports = self.exports.write().await;
        let Some(export) = exports.get_mut(cell_id) else {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (no local export to revoke)"
            )));
        };
        export.revoked = true;
        drop(exports);

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

// ─── Errors ─────────────────────────────────────────────────────────────────

/// Errors from CapTP client operations.
#[derive(Debug, Clone)]
pub enum CapTPError {
    /// Failed to parse a dregg URI.
    InvalidUri(String),
    /// The requested capability was not found.
    NotFound(String),
    /// The operation is not implemented by the current backend.
    Unsupported(String),
}

impl std::fmt::Display for CapTPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapTPError::InvalidUri(e) => write!(f, "invalid dregg URI: {e}"),
            CapTPError::NotFound(id) => write!(f, "capability not found: {id}"),
            CapTPError::Unsupported(message) => write!(f, "unsupported: {message}"),
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

fn parse_cell_id(cell_id: &str) -> Result<[u8; 32], CapTPError> {
    let bytes = hex::decode(cell_id).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
    bytes.try_into().map_err(|bytes: Vec<u8>| {
        CapTPError::InvalidUri(format!("cell ID must be 32 bytes, got {}", bytes.len()))
    })
}

fn new_swiss(cell_id: &str, bot_cell_id: &str, federation_id: [u8; 32]) -> [u8; 32] {
    let mut swiss = [0u8; 32];
    if std::fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut swiss))
        .is_ok()
    {
        return swiss;
    }

    static FALLBACK_COUNTER: AtomicU64 = AtomicU64::new(0);
    let counter = FALLBACK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    *blake3::Hasher::new()
        .update(cell_id.as_bytes())
        .update(bot_cell_id.as_bytes())
        .update(&federation_id)
        .update(&now.to_le_bytes())
        .update(&counter.to_le_bytes())
        .finalize()
        .as_bytes()
}
