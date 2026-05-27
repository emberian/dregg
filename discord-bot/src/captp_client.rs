//! CapTP client: the bot's own identity and capability session management.
//!
//! The bot IS a dregg participant — it has its own keypair, holds live references,
//! and tracks sturdy refs it has locally exported or accepted. The dregg node does
//! not currently serve `/captp/export`, `/captp/enliven`, `/captp/handoff`, or
//! `/captp/revoke`; this client must not pretend those HTTP endpoints exist.
//!
//! Handoffs are Discord-mediated local records: the bot stores a bearer token,
//! recipient identity, sturdy ref, and local signature through the bot database.
//! Redeeming the token enlivens the same sturdy ref for the intended recipient.

use std::io::Read;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::db::{CaptpExportRecord, CaptpHeldRecord, CaptpLocalHandoffRecord, Database};
use dregg_captp::FederationId as GroupId;
use dregg_captp::uri::DreggUri;
use serde::{Deserialize, Serialize};
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

    fn from_str(value: &str) -> Option<Self> {
        match value {
            "pending" => Some(Self::Pending),
            "redeemed" => Some(Self::Redeemed),
            "revoked" => Some(Self::Revoked),
            _ => None,
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
}

impl CapTPClient {
    /// Create a new CapTP client for the bot.
    pub fn new(federation_id: GroupId, bot_cell_id: String, node_url: String) -> Self {
        Self {
            federation_id,
            bot_cell_id,
            node_url,
        }
    }

    /// Export a cell as a sturdy ref, returning the dregg URI.
    pub async fn export_cap(&self, db: &Database, cell_id: &str) -> Result<DreggUri, CapTPError> {
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
        db.upsert_captp_export(&CaptpExportRecord::from(&export))
            .await
            .map_err(storage_error)?;

        info!(cell_id, "Exported capability as sturdy ref");
        Ok(uri)
    }

    /// Enliven a dregg URI — the bot accepts and holds the live reference.
    pub async fn accept_cap(
        &self,
        db: &Database,
        uri_str: &str,
    ) -> Result<HeldCapability, CapTPError> {
        let uri = DreggUri::parse(uri_str).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;

        let cell_id = hex::encode(uri.cell_id);
        let Some(export) = db
            .get_captp_export(&cell_id)
            .await
            .map_err(storage_error)?
            .map(export_from_record)
            .transpose()?
        else {
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

        let cap = HeldCapability {
            uri,
            label: None,
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };

        db.upsert_captp_held_ref(&CaptpHeldRecord::from_cap(&cell_id, &cap))
            .await
            .map_err(storage_error)?;
        info!(cell_id, "Enlivened and holding capability");
        Ok(cap)
    }

    /// Create a handoff certificate delegating a capability to a recipient.
    pub async fn delegate_cap(
        &self,
        db: &Database,
        cell_id: &str,
        recipient_key: &str,
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(cell_id)?;
        parse_cell_id(recipient_key)?;

        let uri = match db
            .get_captp_export(cell_id)
            .await
            .map_err(storage_error)?
            .map(export_from_record)
            .transpose()?
        {
            Some(export) if !export.revoked => export.uri,
            Some(_) => {
                return Err(CapTPError::NotFound(format!(
                    "{cell_id} (local export is revoked)"
                )));
            }
            None => self.export_cap(db, cell_id).await?,
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

        db.upsert_captp_local_handoff(&CaptpLocalHandoffRecord::from(&record))
            .await
            .map_err(storage_error)?;

        info!(cell_id, recipient_key, token, "Created local CapTP handoff");
        Ok(record)
    }

    /// Return a handoff record by token.
    pub async fn handoff_status(&self, db: &Database, token: &str) -> Option<HandoffRecord> {
        db.get_captp_local_handoff(token)
            .await
            .ok()
            .flatten()
            .and_then(handoff_from_record)
    }

    /// Redeem a Discord-mediated local handoff token for the recipient identity.
    pub async fn redeem_handoff(
        &self,
        db: &Database,
        token: &str,
        recipient_key: &str,
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(recipient_key)?;

        let Some(mut record) = db
            .get_captp_local_handoff(token)
            .await
            .map_err(storage_error)?
            .and_then(handoff_from_record)
        else {
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
        db.upsert_captp_held_ref(&CaptpHeldRecord::from_cap(&redeemed.cell_id, &cap))
            .await
            .map_err(storage_error)?;
        db.upsert_captp_local_handoff(&CaptpLocalHandoffRecord::from(&redeemed))
            .await
            .map_err(storage_error)?;

        info!(
            token,
            cell_id = redeemed.cell_id,
            "Redeemed local CapTP handoff"
        );
        Ok(redeemed)
    }

    /// Revoke a previously exported capability.
    pub async fn revoke_cap(&self, db: &Database, cell_id: &str) -> Result<(), CapTPError> {
        parse_cell_id(cell_id)?;

        if !db
            .revoke_captp_export(cell_id)
            .await
            .map_err(storage_error)?
        {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (no local export to revoke)"
            )));
        };

        db.revoke_pending_captp_local_handoffs_for_cell(cell_id, current_epoch() as i64)
            .await
            .map_err(storage_error)?;
        db.delete_captp_held_ref(cell_id)
            .await
            .map_err(storage_error)?;

        info!(cell_id, "Revoked capability");
        Ok(())
    }

    /// List all held capabilities.
    pub async fn list_held(
        &self,
        db: &Database,
    ) -> Result<Vec<(String, HeldCapability)>, CapTPError> {
        db.list_captp_held_refs()
            .await
            .map_err(storage_error)?
            .into_iter()
            .map(held_from_record)
            .collect()
    }

    /// List all exports.
    pub async fn list_exports(
        &self,
        db: &Database,
    ) -> Result<Vec<(String, ExportedCapability)>, CapTPError> {
        Ok(db
            .list_captp_exports()
            .await
            .map_err(storage_error)?
            .into_iter()
            .map(export_from_record)
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(|export| (export.cell_id.clone(), export))
            .collect())
    }

    /// List all local handoff records.
    pub async fn list_handoffs(&self, db: &Database) -> Result<Vec<HandoffRecord>, CapTPError> {
        Ok(db
            .list_captp_local_handoffs()
            .await
            .map_err(storage_error)?
            .into_iter()
            .filter_map(handoff_from_record)
            .collect())
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

fn storage_error(error: sqlx::Error) -> CapTPError {
    CapTPError::Storage(error.to_string())
}

impl From<&ExportedCapability> for CaptpExportRecord {
    fn from(export: &ExportedCapability) -> Self {
        Self {
            cell_id: export.cell_id.clone(),
            sturdy_uri: export.uri.to_string(),
            shared_with: export.shared_with.map(|id| id.to_string()),
            exported_at: export.exported_at as i64,
            revoked: export.revoked,
        }
    }
}

impl CaptpHeldRecord {
    fn from_cap(cell_id: &str, cap: &HeldCapability) -> Self {
        Self {
            cell_id: cell_id.to_string(),
            sturdy_uri: cap.uri.to_string(),
            label: cap.label.clone(),
            shared_by: cap.shared_by.map(|id| id.to_string()),
            acquired_at: cap.acquired_at as i64,
            live: cap.live,
        }
    }
}

impl From<&HandoffRecord> for CaptpLocalHandoffRecord {
    fn from(record: &HandoffRecord) -> Self {
        Self {
            token_id: record.token.clone(),
            cell_id: record.cell_id.clone(),
            sturdy_uri: record.uri.clone(),
            recipient_cell_id: record.recipient_key.clone(),
            local_signature: record.local_signature.clone(),
            status: record.status.as_str().to_string(),
            created_at: record.created_at as i64,
            redeemed_at: record.redeemed_at.map(|value| value as i64),
        }
    }
}

fn export_from_record(record: CaptpExportRecord) -> Result<ExportedCapability, CapTPError> {
    Ok(ExportedCapability {
        cell_id: record.cell_id,
        uri: DreggUri::parse(&record.sturdy_uri)
            .map_err(|e| CapTPError::InvalidUri(e.to_string()))?,
        shared_with: record
            .shared_with
            .as_deref()
            .and_then(|value| value.parse().ok()),
        exported_at: record.exported_at as u64,
        revoked: record.revoked,
    })
}

fn held_from_record(record: CaptpHeldRecord) -> Result<(String, HeldCapability), CapTPError> {
    let uri =
        DreggUri::parse(&record.sturdy_uri).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
    Ok((
        record.cell_id,
        HeldCapability {
            uri,
            label: record.label,
            shared_by: record
                .shared_by
                .as_deref()
                .and_then(|value| value.parse().ok()),
            acquired_at: record.acquired_at as u64,
            live: record.live,
        },
    ))
}

fn handoff_from_record(record: CaptpLocalHandoffRecord) -> Option<HandoffRecord> {
    Some(HandoffRecord {
        token: record.token_id,
        cell_id: record.cell_id,
        uri: record.sturdy_uri,
        recipient_key: record.recipient_cell_id,
        local_signature: record.local_signature,
        status: HandoffStatus::from_str(&record.status)?,
        created_at: record.created_at as u64,
        redeemed_at: record.redeemed_at.map(|value| value as u64),
    })
}
