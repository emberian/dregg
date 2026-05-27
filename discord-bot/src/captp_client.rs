//! CapTP client: the bot's own identity and capability session management.
//!
//! The bot IS a dregg participant — it has its own keypair, holds live references,
//! and tracks sturdy refs it has locally exported or accepted. The dregg node does
//! not currently serve `/captp/export`, `/captp/enliven`, `/captp/handoff`, or
//! `/captp/revoke`; this client must not pretend those HTTP endpoints exist.
//!
//! Handoffs are Discord-mediated local records: the bot stores a bearer token,
//! recipient identity, sturdy ref, and local signature in a durable JSON file.
//! Redeeming the token enlivens the same sturdy ref for the intended recipient.

use std::collections::HashMap;
use std::io::Read;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_captp::FederationId as GroupId;
use dregg_captp::uri::DreggUri;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::info;

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

/// Status of a Discord-mediated CapTP handoff token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HandoffStatus {
    /// Token has been minted and can be redeemed by the recipient identity.
    Pending,
    /// Token has already been redeemed.
    Redeemed,
    /// Source capability was revoked before redemption.
    Revoked,
}

impl HandoffStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Redeemed => "redeemed",
            Self::Revoked => "revoked",
        }
    }
}

/// A persistent local handoff record.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandoffRecord {
    /// Bearer token presented to `/cap-accept`.
    pub token: String,
    /// Cell ID being handed off.
    pub cell_id: String,
    /// Sturdy ref being handed off.
    pub uri: String,
    /// Recipient cell/public identity bound by Discord identity lookup.
    pub recipient_key: String,
    /// Bot-local signature binding token, cell, recipient, and URI.
    pub local_signature: String,
    /// Current token status.
    pub status: HandoffStatus,
    /// Creation timestamp.
    pub created_at: u64,
    /// Redemption timestamp, if redeemed.
    pub redeemed_at: Option<u64>,
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
    /// Durable handoff records (keyed by token).
    handoffs: RwLock<HashMap<String, HandoffRecord>>,
    /// Path to the durable handoff store.
    handoff_store_path: PathBuf,
}

impl CapTPClient {
    /// Create a new CapTP client for the bot.
    pub fn new(federation_id: GroupId, bot_cell_id: String, node_url: String) -> Self {
        let handoff_store_path = handoff_store_path();
        let handoffs = load_handoffs(&handoff_store_path).unwrap_or_default();
        Self {
            federation_id,
            bot_cell_id,
            node_url,
            held: RwLock::new(HashMap::new()),
            exports: RwLock::new(HashMap::new()),
            handoffs: RwLock::new(handoffs),
            handoff_store_path,
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
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(cell_id)?;
        parse_cell_id(recipient_key)?;

        let uri = {
            let exports = self.exports.read().await;
            match exports.get(cell_id) {
                Some(export) if !export.revoked => export.uri.clone(),
                Some(_) => {
                    return Err(CapTPError::NotFound(format!(
                        "{cell_id} (local export is revoked)"
                    )));
                }
                None => {
                    drop(exports);
                    self.export_cap(cell_id).await?
                }
            }
        };

        let token = format!("dregg-handoff-{}", hex::encode(new_secret()));
        let uri_string = uri.to_string();
        let local_signature = sign_handoff(
            &self.bot_cell_id,
            self.federation_id.0,
            &token,
            cell_id,
            recipient_key,
            &uri_string,
        );
        let record = HandoffRecord {
            token: token.clone(),
            cell_id: cell_id.to_string(),
            uri: uri_string,
            recipient_key: recipient_key.to_string(),
            local_signature,
            status: HandoffStatus::Pending,
            created_at: current_epoch(),
            redeemed_at: None,
        };

        let mut handoffs = self.handoffs.write().await;
        handoffs.insert(token.clone(), record.clone());
        persist_handoffs(&self.handoff_store_path, &handoffs)?;

        info!(cell_id, recipient_key, token, "Created local CapTP handoff");
        Ok(record)
    }

    /// Return a handoff record by token.
    pub async fn handoff_status(&self, token: &str) -> Option<HandoffRecord> {
        self.handoffs.read().await.get(token).cloned()
    }

    /// Redeem a Discord-mediated local handoff token for the recipient identity.
    pub async fn redeem_handoff(
        &self,
        token: &str,
        recipient_key: &str,
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(recipient_key)?;

        let mut handoffs = self.handoffs.write().await;
        let Some(record) = handoffs.get_mut(token) else {
            return Err(CapTPError::NotFound(format!("{token} (handoff token)")));
        };

        if record.recipient_key != recipient_key {
            return Err(CapTPError::Forbidden(
                "handoff token is bound to a different recipient identity".to_string(),
            ));
        }
        if record.status != HandoffStatus::Pending {
            return Err(CapTPError::Unsupported(format!(
                "handoff token is {}",
                record.status.as_str()
            )));
        }

        let expected = sign_handoff(
            &self.bot_cell_id,
            self.federation_id.0,
            &record.token,
            &record.cell_id,
            &record.recipient_key,
            &record.uri,
        );
        if record.local_signature != expected {
            return Err(CapTPError::InvalidUri(
                "handoff record signature does not verify".to_string(),
            ));
        }

        let uri =
            DreggUri::parse(&record.uri).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
        let cap = HeldCapability {
            uri,
            label: Some(format!("handoff:{}", &record.token)),
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };

        record.status = HandoffStatus::Redeemed;
        record.redeemed_at = Some(current_epoch());
        let redeemed = record.clone();
        self.held
            .write()
            .await
            .insert(redeemed.cell_id.clone(), cap);
        persist_handoffs(&self.handoff_store_path, &handoffs)?;

        info!(
            token,
            cell_id = redeemed.cell_id,
            "Redeemed local CapTP handoff"
        );
        Ok(redeemed)
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

        let mut handoffs = self.handoffs.write().await;
        for record in handoffs.values_mut() {
            if record.cell_id == cell_id && record.status == HandoffStatus::Pending {
                record.status = HandoffStatus::Revoked;
            }
        }
        persist_handoffs(&self.handoff_store_path, &handoffs)?;
        drop(handoffs);

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

    /// List all local handoff records.
    pub async fn list_handoffs(&self) -> Vec<HandoffRecord> {
        self.handoffs.read().await.values().cloned().collect()
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
    /// The caller is not allowed to exercise this handoff.
    Forbidden(String),
    /// Durable local handoff store failed.
    Storage(String),
}

impl std::fmt::Display for CapTPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapTPError::InvalidUri(e) => write!(f, "invalid dregg URI: {e}"),
            CapTPError::NotFound(id) => write!(f, "capability not found: {id}"),
            CapTPError::Unsupported(message) => write!(f, "unsupported: {message}"),
            CapTPError::Forbidden(message) => write!(f, "forbidden: {message}"),
            CapTPError::Storage(message) => write!(f, "storage error: {message}"),
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
    new_secret_with_fallback(cell_id.as_bytes(), bot_cell_id.as_bytes(), &federation_id)
}

fn new_secret() -> [u8; 32] {
    new_secret_with_fallback(b"handoff-token", b"", b"")
}

fn new_secret_with_fallback(seed_a: &[u8], seed_b: &[u8], seed_c: &[u8]) -> [u8; 32] {
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
        .update(seed_a)
        .update(seed_b)
        .update(seed_c)
        .update(&now.to_le_bytes())
        .update(&counter.to_le_bytes())
        .finalize()
        .as_bytes()
}

fn sign_handoff(
    bot_cell_id: &str,
    federation_id: [u8; 32],
    token: &str,
    cell_id: &str,
    recipient_key: &str,
    uri: &str,
) -> String {
    hex::encode(
        blake3::Hasher::new()
            .update(b"dregg-discord-captp-local-handoff-v1")
            .update(bot_cell_id.as_bytes())
            .update(&federation_id)
            .update(token.as_bytes())
            .update(cell_id.as_bytes())
            .update(recipient_key.as_bytes())
            .update(uri.as_bytes())
            .finalize()
            .as_bytes(),
    )
}

fn handoff_store_path() -> PathBuf {
    if let Ok(path) = std::env::var("CAPTP_HANDOFF_STORE") {
        return PathBuf::from(path);
    }

    if let Ok(database_url) = std::env::var("DATABASE_URL") {
        if let Some(path) = database_url.strip_prefix("sqlite:") {
            return PathBuf::from(format!("{path}.captp-handoffs.json"));
        }
    }

    PathBuf::from("bot.captp-handoffs.json")
}

fn load_handoffs(path: &PathBuf) -> Result<HashMap<String, HandoffRecord>, CapTPError> {
    if !path.exists() {
        return Ok(HashMap::new());
    }

    let bytes = std::fs::read(path).map_err(|e| CapTPError::Storage(e.to_string()))?;
    let records: Vec<HandoffRecord> =
        serde_json::from_slice(&bytes).map_err(|e| CapTPError::Storage(e.to_string()))?;
    Ok(records
        .into_iter()
        .map(|record| (record.token.clone(), record))
        .collect())
}

fn persist_handoffs(
    path: &PathBuf,
    handoffs: &HashMap<String, HandoffRecord>,
) -> Result<(), CapTPError> {
    let mut records: Vec<_> = handoffs.values().cloned().collect();
    records.sort_by(|a, b| a.created_at.cmp(&b.created_at).then(a.token.cmp(&b.token)));
    let json =
        serde_json::to_vec_pretty(&records).map_err(|e| CapTPError::Storage(e.to_string()))?;

    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent).map_err(|e| CapTPError::Storage(e.to_string()))?;
    }
    std::fs::write(path, json).map_err(|e| CapTPError::Storage(e.to_string()))
}
