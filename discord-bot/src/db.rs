//! Database layer (SQLite via sqlx).

use serde::Serialize;
use sqlx::{Pool, Row, Sqlite, SqlitePool};

/// How a Discord user identity is bound to a dregg cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentityMode {
    /// The bot deterministically derives and can sign for this cell.
    Hosted,
    /// The user has requested an external link but has not completed ownership proof.
    ExternalPending,
    /// The user proved control of the external cell.
    ExternalVerified,
}

impl IdentityMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Hosted => "hosted",
            Self::ExternalPending => "external_pending",
            Self::ExternalVerified => "external_verified",
        }
    }

    fn from_db(value: &str) -> Self {
        match value {
            "external_pending" => Self::ExternalPending,
            "external_verified" => Self::ExternalVerified,
            _ => Self::Hosted,
        }
    }
}

/// User identity record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserIdentity {
    pub cell_id: String,
    pub mode: IdentityMode,
    pub link_challenge: Option<String>,
}

/// Materialized Starbridge app activity recorded by the Discord host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeActivity {
    pub id: i64,
    pub app: String,
    pub action: String,
    pub actor_discord_id: String,
    pub guild_id: Option<String>,
    pub subject: Option<String>,
    pub status: String,
    pub details_json: String,
    pub timestamp: i64,
}

/// Discord namespace path backed by a devnet programmable queue.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeQueue {
    pub namespace_path: String,
    pub guild_id: String,
    pub name: String,
    pub queue_id: String,
    pub created_by: String,
    pub acl_role: Option<String>,
    pub rate_limit: Option<i64>,
    pub min_deposit: Option<i64>,
    pub created_at: i64,
}

/// Discord user subscription to a Starbridge queue.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StarbridgeQueueSubscription {
    pub namespace_path: String,
    pub discord_id: String,
    pub subscribed_at: i64,
}

/// Durable Discord-mediated CapTP handoff state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpHandoffRecord {
    pub token_id: String,
    pub cell_id: String,
    pub sturdy_uri: String,
    pub from_discord_id: String,
    pub to_discord_id: String,
    pub recipient_cell_id: String,
    pub status: String,
    pub issued_at: i64,
    pub redeemed_at: Option<i64>,
    pub revoked_at: Option<i64>,
    pub token_json: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpExportRecord {
    pub cell_id: String,
    pub sturdy_uri: String,
    pub shared_with: Option<String>,
    pub exported_at: i64,
    pub revoked: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpHeldRecord {
    pub cell_id: String,
    pub sturdy_uri: String,
    pub label: Option<String>,
    pub shared_by: Option<String>,
    pub acquired_at: i64,
    pub live: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CaptpLocalHandoffRecord {
    pub token_id: String,
    pub cell_id: String,
    pub sturdy_uri: String,
    pub recipient_cell_id: String,
    pub local_signature: String,
    pub status: String,
    pub created_at: i64,
    pub redeemed_at: Option<i64>,
}

/// Credential material held locally for a hosted Discord identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HeldCredential {
    pub credential_id: String,
    pub discord_id: String,
    pub holder_cell_id: String,
    pub issuer_cell_id: String,
    pub schema: String,
    pub issued_at: i64,
    pub turn_hash: Option<String>,
    pub encoded_credential: String,
    pub attributes_json: String,
    pub created_at: i64,
}

/// Locally recorded presentation request/placeholder state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CredentialPresentation {
    pub request_id: String,
    pub verifier_discord_id: String,
    pub subject_discord_id: String,
    pub subject_cell_id: String,
    pub predicate: String,
    pub status: String,
    pub credential_id: Option<String>,
    pub presentation_json: String,
    pub created_at: i64,
}

/// Database handle wrapping a SQLite connection pool.
#[derive(Clone)]
pub struct Database {
    pool: Pool<Sqlite>,
}

impl Database {
    /// Connect to the database and run migrations.
    pub async fn connect(url: &str) -> Result<Self, sqlx::Error> {
        let pool = SqlitePool::connect(url).await?;

        // Run schema initialization.
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS kv (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS feed_channels (
                guild_id TEXT PRIMARY KEY,
                channel_id TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS watchers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id TEXT NOT NULL,
                cell_id TEXT NOT NULL,
                UNIQUE(user_id, cell_id)
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS users (
                discord_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                identity_mode TEXT NOT NULL DEFAULT 'hosted',
                link_challenge TEXT
            )",
        )
        .execute(&pool)
        .await?;

        ensure_column(
            &pool,
            "users",
            "identity_mode",
            "TEXT NOT NULL DEFAULT 'hosted'",
        )
        .await?;
        ensure_column(&pool, "users", "link_challenge", "TEXT").await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                from_user TEXT NOT NULL,
                to_user TEXT NOT NULL,
                amount INTEGER NOT NULL,
                tx_hash TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_activity (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                app TEXT NOT NULL,
                action TEXT NOT NULL,
                actor_discord_id TEXT NOT NULL,
                guild_id TEXT,
                subject TEXT,
                status TEXT NOT NULL,
                details_json TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_activity_recent
             ON starbridge_activity (timestamp DESC, id DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_activity_app_recent
             ON starbridge_activity (app, timestamp DESC, id DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_queues (
                namespace_path TEXT PRIMARY KEY,
                guild_id TEXT NOT NULL,
                name TEXT NOT NULL,
                queue_id TEXT NOT NULL,
                created_by TEXT NOT NULL,
                acl_role TEXT,
                rate_limit INTEGER,
                min_deposit INTEGER,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_starbridge_queues_guild
             ON starbridge_queues (guild_id, name)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS starbridge_queue_subscriptions (
                namespace_path TEXT NOT NULL,
                discord_id TEXT NOT NULL,
                subscribed_at INTEGER NOT NULL,
                PRIMARY KEY (namespace_path, discord_id)
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_handoffs (
                token_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                sturdy_uri TEXT NOT NULL,
                from_discord_id TEXT NOT NULL,
                to_discord_id TEXT NOT NULL,
                recipient_cell_id TEXT NOT NULL,
                status TEXT NOT NULL,
                issued_at INTEGER NOT NULL,
                redeemed_at INTEGER,
                revoked_at INTEGER,
                token_json TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_captp_handoffs_recipient_status
             ON captp_handoffs (to_discord_id, status, issued_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS identity_held_credentials (
                credential_id TEXT PRIMARY KEY,
                discord_id TEXT NOT NULL,
                holder_cell_id TEXT NOT NULL,
                issuer_cell_id TEXT NOT NULL,
                schema TEXT NOT NULL,
                issued_at INTEGER NOT NULL,
                turn_hash TEXT,
                encoded_credential TEXT NOT NULL,
                attributes_json TEXT NOT NULL,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_identity_held_credentials_holder
             ON identity_held_credentials (discord_id, holder_cell_id, issued_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS identity_presentations (
                request_id TEXT PRIMARY KEY,
                verifier_discord_id TEXT NOT NULL,
                subject_discord_id TEXT NOT NULL,
                subject_cell_id TEXT NOT NULL,
                predicate TEXT NOT NULL,
                status TEXT NOT NULL,
                credential_id TEXT,
                presentation_json TEXT NOT NULL,
                created_at INTEGER NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_identity_presentations_subject
             ON identity_presentations (subject_discord_id, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_exports (
                cell_id TEXT PRIMARY KEY,
                sturdy_uri TEXT NOT NULL,
                shared_with TEXT,
                exported_at INTEGER NOT NULL,
                revoked INTEGER NOT NULL DEFAULT 0
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_held_refs (
                cell_id TEXT PRIMARY KEY,
                sturdy_uri TEXT NOT NULL,
                label TEXT,
                shared_by TEXT,
                acquired_at INTEGER NOT NULL,
                live INTEGER NOT NULL DEFAULT 1
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE TABLE IF NOT EXISTS captp_local_handoffs (
                token_id TEXT PRIMARY KEY,
                cell_id TEXT NOT NULL,
                sturdy_uri TEXT NOT NULL,
                recipient_cell_id TEXT NOT NULL,
                local_signature TEXT NOT NULL,
                status TEXT NOT NULL,
                created_at INTEGER NOT NULL,
                redeemed_at INTEGER
            )",
        )
        .execute(&pool)
        .await?;

        sqlx::query(
            "CREATE INDEX IF NOT EXISTS idx_captp_local_handoffs_cell_status
             ON captp_local_handoffs (cell_id, status, created_at DESC)",
        )
        .execute(&pool)
        .await?;

        Ok(Self { pool })
    }

    // ─── User / cclerk methods ──────────────────────────────────────────────

    /// Check if a user has a cclerk.
    pub async fn user_exists(&self, user_id: &str) -> Result<bool, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT cell_id FROM users WHERE discord_id = ?")
                .bind(user_id)
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.is_some())
    }

    /// Get a user's cell_id.
    pub async fn get_cell_id(&self, discord_id: &str) -> Result<Option<String>, sqlx::Error> {
        Ok(self
            .get_user_identity(discord_id)
            .await?
            .map(|identity| identity.cell_id))
    }

    /// Get a user's full identity record.
    pub async fn get_user_identity(
        &self,
        discord_id: &str,
    ) -> Result<Option<UserIdentity>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT cell_id, identity_mode, link_challenge FROM users WHERE discord_id = ?",
        )
        .bind(discord_id)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(|row| UserIdentity {
            cell_id: row.get("cell_id"),
            mode: IdentityMode::from_db(row.get::<String, _>("identity_mode").as_str()),
            link_challenge: row.get("link_challenge"),
        }))
    }

    /// Return all known user identities for read surfaces and dashboards.
    pub async fn list_user_identities(&self) -> Result<Vec<UserIdentity>, sqlx::Error> {
        let rows =
            sqlx::query("SELECT cell_id, identity_mode, link_challenge FROM users ORDER BY rowid")
                .fetch_all(&self.pool)
                .await?;

        Ok(rows
            .into_iter()
            .map(|row| UserIdentity {
                cell_id: row.get("cell_id"),
                mode: IdentityMode::from_db(row.get::<String, _>("identity_mode").as_str()),
                link_challenge: row.get("link_challenge"),
            })
            .collect())
    }

    // ─── Activity feed methods ──────────────────────────────────────────────

    /// Get last processed block height for activity feed.
    pub async fn get_last_block_height(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT value FROM kv WHERE key = 'last_block_height'")
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.and_then(|(v,)| v.parse::<u64>().ok()).unwrap_or(0))
    }

    /// Set last processed block height.
    pub async fn set_last_block_height(&self, height: u64) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO kv (key, value) VALUES ('last_block_height', ?)")
            .bind(height.to_string())
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Set the activity feed channel for a guild.
    pub async fn set_feed_channel(
        &self,
        guild_id: &str,
        channel_id: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO feed_channels (guild_id, channel_id) VALUES (?, ?)")
            .bind(guild_id)
            .bind(channel_id)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Get all configured feed channels.
    pub async fn get_all_feed_channels(&self) -> Result<Vec<(String, String)>, sqlx::Error> {
        let rows: Vec<(String, String)> =
            sqlx::query_as("SELECT guild_id, channel_id FROM feed_channels")
                .fetch_all(&self.pool)
                .await?;
        Ok(rows)
    }

    // ─── Watch subscription methods ─────────────────────────────────────────

    /// Add a watch subscription.
    pub async fn add_watch(&self, discord_id: &str, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("INSERT OR IGNORE INTO watchers (user_id, cell_id) VALUES (?, ?)")
            .bind(discord_id)
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Remove a watch subscription.
    pub async fn remove_watch(&self, discord_id: &str, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("DELETE FROM watchers WHERE user_id = ? AND cell_id = ?")
            .bind(discord_id)
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Get users watching a specific cell.
    pub async fn get_watchers_for_cell(&self, cell_id: &str) -> Result<Vec<String>, sqlx::Error> {
        let rows: Vec<(String,)> = sqlx::query_as("SELECT user_id FROM watchers WHERE cell_id = ?")
            .bind(cell_id)
            .fetch_all(&self.pool)
            .await?;
        Ok(rows.into_iter().map(|(id,)| id).collect())
    }

    // ─── Cipherclerk / user registration ────────────────────────────────────────────

    /// Register a user's cell_id.
    pub async fn register_user(&self, discord_id: &str, cell_id: &str) -> Result<(), sqlx::Error> {
        self.register_user_with_mode(discord_id, cell_id, IdentityMode::Hosted, None)
            .await
    }

    /// Register a user's cell_id with explicit identity mode metadata.
    pub async fn register_user_with_mode(
        &self,
        discord_id: &str,
        cell_id: &str,
        mode: IdentityMode,
        link_challenge: Option<&str>,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO users (discord_id, cell_id, identity_mode, link_challenge) VALUES (?, ?, ?, ?)",
        )
            .bind(discord_id)
            .bind(cell_id)
            .bind(mode.as_str())
            .bind(link_challenge)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    /// Start an external identity link. This does not mark the identity usable
    /// until a later proof verifier promotes it to `external_verified`.
    pub async fn create_pending_external_link(
        &self,
        discord_id: &str,
        cell_id: &str,
        challenge: &str,
    ) -> Result<(), sqlx::Error> {
        self.register_user_with_mode(
            discord_id,
            cell_id,
            IdentityMode::ExternalPending,
            Some(challenge),
        )
        .await
    }

    /// Unlink a user's cell_id (remove from users table).
    pub async fn unlink_user(&self, discord_id: &str) -> Result<(), sqlx::Error> {
        sqlx::query("DELETE FROM users WHERE discord_id = ?")
            .bind(discord_id)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    // ─── Identity holder store ───────────────────────────────────────────

    pub async fn store_held_credential(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        issuer_cell_id: &str,
        credential_id: &str,
        schema: &str,
        issued_at: i64,
        turn_hash: Option<&str>,
        encoded_credential: &str,
        attributes_json: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO identity_held_credentials
             (credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(credential_id)
        .bind(discord_id)
        .bind(holder_cell_id)
        .bind(issuer_cell_id)
        .bind(schema)
        .bind(issued_at)
        .bind(turn_hash)
        .bind(encoded_credential)
        .bind(attributes_json)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn list_held_credentials(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        limit: u32,
    ) -> Result<Vec<HeldCredential>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
             FROM identity_held_credentials
             WHERE discord_id = ? AND holder_cell_id = ?
             ORDER BY issued_at DESC, created_at DESC
             LIMIT ?",
        )
        .bind(discord_id)
        .bind(holder_cell_id)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(held_credential_from_row).collect())
    }

    pub async fn find_held_credential_for_predicate(
        &self,
        discord_id: &str,
        holder_cell_id: &str,
        predicate: &str,
    ) -> Result<Option<HeldCredential>, sqlx::Error> {
        let schema_hint = predicate
            .split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '-')
            .find(|part| !part.is_empty());
        let row = if let Some(hint) = schema_hint {
            sqlx::query(
                "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
                 FROM identity_held_credentials
                 WHERE discord_id = ? AND holder_cell_id = ?
                   AND (schema = ? OR attributes_json LIKE ?)
                 ORDER BY issued_at DESC, created_at DESC
                 LIMIT 1",
            )
            .bind(discord_id)
            .bind(holder_cell_id)
            .bind(hint)
            .bind(format!("%\"{hint}\"%"))
            .fetch_optional(&self.pool)
            .await?
        } else {
            None
        };

        if row.is_some() {
            return Ok(row.map(held_credential_from_row));
        }

        let row = sqlx::query(
            "SELECT credential_id, discord_id, holder_cell_id, issuer_cell_id, schema, issued_at, turn_hash, encoded_credential, attributes_json, created_at
             FROM identity_held_credentials
             WHERE discord_id = ? AND holder_cell_id = ?
             ORDER BY issued_at DESC, created_at DESC
             LIMIT 1",
        )
        .bind(discord_id)
        .bind(holder_cell_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(held_credential_from_row))
    }

    pub async fn create_identity_presentation(
        &self,
        verifier_discord_id: &str,
        subject_discord_id: &str,
        subject_cell_id: &str,
        predicate: &str,
        status: &str,
        credential_id: Option<&str>,
        presentation_json: &str,
    ) -> Result<CredentialPresentation, sqlx::Error> {
        let request_id = format!(
            "discord-proof-{}-{}",
            chrono_now(),
            short_local_hash(&format!(
                "{verifier_discord_id}:{subject_discord_id}:{predicate}"
            ))
        );
        let created_at = chrono_now();
        sqlx::query(
            "INSERT INTO identity_presentations
             (request_id, verifier_discord_id, subject_discord_id, subject_cell_id, predicate, status, credential_id, presentation_json, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(&request_id)
        .bind(verifier_discord_id)
        .bind(subject_discord_id)
        .bind(subject_cell_id)
        .bind(predicate)
        .bind(status)
        .bind(credential_id)
        .bind(presentation_json)
        .bind(created_at)
        .execute(&self.pool)
        .await?;

        Ok(CredentialPresentation {
            request_id,
            verifier_discord_id: verifier_discord_id.to_string(),
            subject_discord_id: subject_discord_id.to_string(),
            subject_cell_id: subject_cell_id.to_string(),
            predicate: predicate.to_string(),
            status: status.to_string(),
            credential_id: credential_id.map(str::to_string),
            presentation_json: presentation_json.to_string(),
            created_at,
        })
    }

    // ─── Faucet rate limiting ───────────────────────────────────────────────────

    /// Get the timestamp of the user's last faucet claim. Returns None if never claimed.
    pub async fn get_last_faucet_claim(
        &self,
        discord_id: &str,
    ) -> Result<Option<i64>, sqlx::Error> {
        let row: Option<(String,)> = sqlx::query_as("SELECT value FROM kv WHERE key = ?")
            .bind(format!("faucet:{discord_id}"))
            .fetch_optional(&self.pool)
            .await?;
        Ok(row.and_then(|(v,)| v.parse::<i64>().ok()))
    }

    /// Record a faucet claim timestamp.
    pub async fn set_faucet_claim(
        &self,
        discord_id: &str,
        timestamp: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query("INSERT OR REPLACE INTO kv (key, value) VALUES (?, ?)")
            .bind(format!("faucet:{discord_id}"))
            .bind(timestamp.to_string())
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    // ─── Transaction history ────────────────────────────────────────────────────

    /// Record a transaction in the local ledger.
    pub async fn record_transaction(
        &self,
        from_discord_id: &str,
        to_discord_id: &str,
        amount: u64,
        tx_hash: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO transactions (from_user, to_user, amount, tx_hash, timestamp) VALUES (?, ?, ?, ?, ?)",
        )
        .bind(from_discord_id)
        .bind(to_discord_id)
        .bind(amount as i64)
        .bind(tx_hash)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Get recent transactions for a user (as sender or receiver).
    pub async fn get_user_transactions(
        &self,
        discord_id: &str,
        limit: u32,
    ) -> Result<Vec<TransactionRecord>, sqlx::Error> {
        let rows: Vec<TransactionRecord> = sqlx::query_as(
            "SELECT from_user, to_user, amount, tx_hash, timestamp FROM transactions WHERE from_user = ? OR to_user = ? ORDER BY timestamp DESC LIMIT ?",
        )
        .bind(discord_id)
        .bind(discord_id)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    /// Get recent transactions across all users.
    pub async fn get_recent_transactions(
        &self,
        limit: u32,
    ) -> Result<Vec<TransactionRecord>, sqlx::Error> {
        let rows: Vec<TransactionRecord> = sqlx::query_as(
            "SELECT from_user, to_user, amount, tx_hash, timestamp FROM transactions ORDER BY timestamp DESC LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    /// Get top holders (by number of faucet claims — proxy for balance in local ledger).
    pub async fn get_leaderboard(&self, limit: u32) -> Result<Vec<(String, i64)>, sqlx::Error> {
        let rows: Vec<(String, i64)> = sqlx::query_as(
            "SELECT to_user, SUM(amount) as total FROM transactions GROUP BY to_user ORDER BY total DESC LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;
        Ok(rows)
    }

    // ─── Starbridge app materialized activity ──────────────────────────────

    pub async fn record_starbridge_activity(
        &self,
        app: &str,
        action: &str,
        actor_discord_id: &str,
        guild_id: Option<&str>,
        subject: Option<&str>,
        status: &str,
        details: serde_json::Value,
    ) -> Result<i64, sqlx::Error> {
        let details_json = details.to_string();
        let result = sqlx::query(
            "INSERT INTO starbridge_activity
             (app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(app)
        .bind(action)
        .bind(actor_discord_id)
        .bind(guild_id)
        .bind(subject)
        .bind(status)
        .bind(details_json)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;

        Ok(result.last_insert_rowid())
    }

    pub async fn get_recent_starbridge_activity(
        &self,
        limit: u32,
    ) -> Result<Vec<StarbridgeActivity>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id, app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp
             FROM starbridge_activity
             ORDER BY timestamp DESC, id DESC
             LIMIT ?",
        )
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(activity_from_row).collect())
    }

    pub async fn get_recent_starbridge_activity_for_app(
        &self,
        app: &str,
        limit: u32,
    ) -> Result<Vec<StarbridgeActivity>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT id, app, action, actor_discord_id, guild_id, subject, status, details_json, timestamp
             FROM starbridge_activity
             WHERE app = ?
             ORDER BY timestamp DESC, id DESC
             LIMIT ?",
        )
        .bind(app)
        .bind(limit)
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(activity_from_row).collect())
    }

    // ─── Starbridge programmable queue host state ─────────────────────────

    pub async fn upsert_starbridge_queue(
        &self,
        namespace_path: &str,
        guild_id: &str,
        name: &str,
        queue_id: &str,
        created_by: &str,
        acl_role: Option<&str>,
        rate_limit: Option<i64>,
        min_deposit: Option<i64>,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO starbridge_queues
             (namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        )
        .bind(namespace_path)
        .bind(guild_id)
        .bind(name)
        .bind(queue_id)
        .bind(created_by)
        .bind(acl_role)
        .bind(rate_limit)
        .bind(min_deposit)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_starbridge_queue(
        &self,
        namespace_path: &str,
    ) -> Result<Option<StarbridgeQueue>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at
             FROM starbridge_queues
             WHERE namespace_path = ?",
        )
        .bind(namespace_path)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(queue_from_row))
    }

    pub async fn list_starbridge_queues(&self) -> Result<Vec<StarbridgeQueue>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT namespace_path, guild_id, name, queue_id, created_by, acl_role, rate_limit, min_deposit, created_at
             FROM starbridge_queues
             ORDER BY guild_id, name",
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(rows.into_iter().map(queue_from_row).collect())
    }

    pub async fn subscribe_starbridge_queue(
        &self,
        namespace_path: &str,
        discord_id: &str,
    ) -> Result<bool, sqlx::Error> {
        let result = sqlx::query(
            "INSERT OR IGNORE INTO starbridge_queue_subscriptions
             (namespace_path, discord_id, subscribed_at)
             VALUES (?, ?, ?)",
        )
        .bind(namespace_path)
        .bind(discord_id)
        .bind(chrono_now())
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn list_starbridge_queue_subscriptions(
        &self,
    ) -> Result<Vec<StarbridgeQueueSubscription>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT namespace_path, discord_id, subscribed_at
             FROM starbridge_queue_subscriptions
             ORDER BY namespace_path, subscribed_at DESC, discord_id",
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(rows
            .into_iter()
            .map(|row| StarbridgeQueueSubscription {
                namespace_path: row.get("namespace_path"),
                discord_id: row.get("discord_id"),
                subscribed_at: row.get("subscribed_at"),
            })
            .collect())
    }

    pub async fn count_starbridge_queue_subscribers(
        &self,
        namespace_path: &str,
    ) -> Result<i64, sqlx::Error> {
        let row: (i64,) = sqlx::query_as(
            "SELECT COUNT(*) FROM starbridge_queue_subscriptions WHERE namespace_path = ?",
        )
        .bind(namespace_path)
        .fetch_one(&self.pool)
        .await?;
        Ok(row.0)
    }

    // ─── CapTP durable handoffs ───────────────────────────────────────────

    pub async fn create_captp_handoff(
        &self,
        token_id: &str,
        cell_id: &str,
        sturdy_uri: &str,
        from_discord_id: &str,
        to_discord_id: &str,
        recipient_cell_id: &str,
        token_json: &str,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO captp_handoffs
             (token_id, cell_id, sturdy_uri, from_discord_id, to_discord_id, recipient_cell_id, status, issued_at, redeemed_at, revoked_at, token_json)
             VALUES (?, ?, ?, ?, ?, ?, 'pending', ?, NULL, NULL, ?)",
        )
        .bind(token_id)
        .bind(cell_id)
        .bind(sturdy_uri)
        .bind(from_discord_id)
        .bind(to_discord_id)
        .bind(recipient_cell_id)
        .bind(chrono_now())
        .bind(token_json)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_handoff(
        &self,
        token_id: &str,
    ) -> Result<Option<CaptpHandoffRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, from_discord_id, to_discord_id, recipient_cell_id, status, issued_at, redeemed_at, revoked_at, token_json
             FROM captp_handoffs
             WHERE token_id = ?",
        )
        .bind(token_id)
        .fetch_optional(&self.pool)
        .await?;

        Ok(row.map(captp_handoff_from_row))
    }

    pub async fn redeem_captp_handoff(
        &self,
        token_id: &str,
        to_discord_id: &str,
    ) -> Result<bool, sqlx::Error> {
        let result = sqlx::query(
            "UPDATE captp_handoffs
             SET status = 'redeemed', redeemed_at = ?
             WHERE token_id = ? AND to_discord_id = ? AND status = 'pending'",
        )
        .bind(chrono_now())
        .bind(token_id)
        .bind(to_discord_id)
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn revoke_captp_handoffs_for_cell(
        &self,
        cell_id: &str,
        from_discord_id: &str,
    ) -> Result<u64, sqlx::Error> {
        let result = sqlx::query(
            "UPDATE captp_handoffs
             SET status = 'revoked', revoked_at = ?
             WHERE cell_id = ? AND from_discord_id = ? AND status = 'pending'",
        )
        .bind(chrono_now())
        .bind(cell_id)
        .bind(from_discord_id)
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected())
    }

    pub async fn upsert_captp_export(&self, record: &CaptpExportRecord) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_exports (cell_id, sturdy_uri, shared_with, exported_at, revoked)
             VALUES (?, ?, ?, ?, ?)
             ON CONFLICT(cell_id) DO UPDATE SET
                sturdy_uri = excluded.sturdy_uri,
                shared_with = excluded.shared_with,
                exported_at = excluded.exported_at,
                revoked = excluded.revoked",
        )
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.shared_with)
        .bind(record.exported_at)
        .bind(record.revoked)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_export(
        &self,
        cell_id: &str,
    ) -> Result<Option<CaptpExportRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT cell_id, sturdy_uri, shared_with, exported_at, revoked
             FROM captp_exports WHERE cell_id = ?",
        )
        .bind(cell_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(captp_export_from_row))
    }

    pub async fn list_captp_exports(&self) -> Result<Vec<CaptpExportRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT cell_id, sturdy_uri, shared_with, exported_at, revoked
             FROM captp_exports ORDER BY exported_at DESC, cell_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_export_from_row).collect())
    }

    pub async fn revoke_captp_export(&self, cell_id: &str) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("UPDATE captp_exports SET revoked = 1 WHERE cell_id = ?")
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(result.rows_affected() > 0)
    }

    pub async fn upsert_captp_held_ref(&self, record: &CaptpHeldRecord) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_held_refs (cell_id, sturdy_uri, label, shared_by, acquired_at, live)
             VALUES (?, ?, ?, ?, ?, ?)
             ON CONFLICT(cell_id) DO UPDATE SET
                sturdy_uri = excluded.sturdy_uri,
                label = excluded.label,
                shared_by = excluded.shared_by,
                acquired_at = excluded.acquired_at,
                live = excluded.live",
        )
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.label)
        .bind(&record.shared_by)
        .bind(record.acquired_at)
        .bind(record.live)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn list_captp_held_refs(&self) -> Result<Vec<CaptpHeldRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT cell_id, sturdy_uri, label, shared_by, acquired_at, live
             FROM captp_held_refs ORDER BY acquired_at DESC, cell_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_held_from_row).collect())
    }

    pub async fn delete_captp_held_ref(&self, cell_id: &str) -> Result<(), sqlx::Error> {
        sqlx::query("DELETE FROM captp_held_refs WHERE cell_id = ?")
            .bind(cell_id)
            .execute(&self.pool)
            .await?;
        Ok(())
    }

    pub async fn upsert_captp_local_handoff(
        &self,
        record: &CaptpLocalHandoffRecord,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT INTO captp_local_handoffs
             (token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at)
             VALUES (?, ?, ?, ?, ?, ?, ?, ?)
             ON CONFLICT(token_id) DO UPDATE SET
                cell_id = excluded.cell_id,
                sturdy_uri = excluded.sturdy_uri,
                recipient_cell_id = excluded.recipient_cell_id,
                local_signature = excluded.local_signature,
                status = excluded.status,
                created_at = excluded.created_at,
                redeemed_at = excluded.redeemed_at",
        )
        .bind(&record.token_id)
        .bind(&record.cell_id)
        .bind(&record.sturdy_uri)
        .bind(&record.recipient_cell_id)
        .bind(&record.local_signature)
        .bind(&record.status)
        .bind(record.created_at)
        .bind(record.redeemed_at)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    pub async fn get_captp_local_handoff(
        &self,
        token_id: &str,
    ) -> Result<Option<CaptpLocalHandoffRecord>, sqlx::Error> {
        let row = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at
             FROM captp_local_handoffs WHERE token_id = ?",
        )
        .bind(token_id)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(captp_local_handoff_from_row))
    }

    pub async fn list_captp_local_handoffs(
        &self,
    ) -> Result<Vec<CaptpLocalHandoffRecord>, sqlx::Error> {
        let rows = sqlx::query(
            "SELECT token_id, cell_id, sturdy_uri, recipient_cell_id, local_signature, status, created_at, redeemed_at
             FROM captp_local_handoffs ORDER BY created_at DESC, token_id",
        )
        .fetch_all(&self.pool)
        .await?;
        Ok(rows.into_iter().map(captp_local_handoff_from_row).collect())
    }

    pub async fn revoke_pending_captp_local_handoffs_for_cell(
        &self,
        cell_id: &str,
        revoked_at: i64,
    ) -> Result<(), sqlx::Error> {
        sqlx::query(
            "UPDATE captp_local_handoffs
             SET status = 'revoked', redeemed_at = COALESCE(redeemed_at, ?)
             WHERE cell_id = ? AND status = 'pending'",
        )
        .bind(revoked_at)
        .bind(cell_id)
        .execute(&self.pool)
        .await?;
        Ok(())
    }

    /// Ensure extra tables exist (called from connect).
    pub async fn ensure_extra_tables(&self) -> Result<(), sqlx::Error> {
        sqlx::query(
            "CREATE TABLE IF NOT EXISTS transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                from_user TEXT NOT NULL,
                to_user TEXT NOT NULL,
                amount INTEGER NOT NULL,
                tx_hash TEXT NOT NULL,
                timestamp INTEGER NOT NULL
            )",
        )
        .execute(&self.pool)
        .await?;
        Ok(())
    }
}

fn queue_from_row(row: sqlx::sqlite::SqliteRow) -> StarbridgeQueue {
    StarbridgeQueue {
        namespace_path: row.get("namespace_path"),
        guild_id: row.get("guild_id"),
        name: row.get("name"),
        queue_id: row.get("queue_id"),
        created_by: row.get("created_by"),
        acl_role: row.get("acl_role"),
        rate_limit: row.get("rate_limit"),
        min_deposit: row.get("min_deposit"),
        created_at: row.get("created_at"),
    }
}

fn activity_from_row(row: sqlx::sqlite::SqliteRow) -> StarbridgeActivity {
    StarbridgeActivity {
        id: row.get("id"),
        app: row.get("app"),
        action: row.get("action"),
        actor_discord_id: row.get("actor_discord_id"),
        guild_id: row.get("guild_id"),
        subject: row.get("subject"),
        status: row.get("status"),
        details_json: row.get("details_json"),
        timestamp: row.get("timestamp"),
    }
}

fn captp_handoff_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpHandoffRecord {
    CaptpHandoffRecord {
        token_id: row.get("token_id"),
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        from_discord_id: row.get("from_discord_id"),
        to_discord_id: row.get("to_discord_id"),
        recipient_cell_id: row.get("recipient_cell_id"),
        status: row.get("status"),
        issued_at: row.get("issued_at"),
        redeemed_at: row.get("redeemed_at"),
        revoked_at: row.get("revoked_at"),
        token_json: row.get("token_json"),
    }
}

fn captp_export_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpExportRecord {
    CaptpExportRecord {
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        shared_with: row.get("shared_with"),
        exported_at: row.get("exported_at"),
        revoked: row.get::<i64, _>("revoked") != 0,
    }
}

fn captp_held_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpHeldRecord {
    CaptpHeldRecord {
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        label: row.get("label"),
        shared_by: row.get("shared_by"),
        acquired_at: row.get("acquired_at"),
        live: row.get::<i64, _>("live") != 0,
    }
}

fn captp_local_handoff_from_row(row: sqlx::sqlite::SqliteRow) -> CaptpLocalHandoffRecord {
    CaptpLocalHandoffRecord {
        token_id: row.get("token_id"),
        cell_id: row.get("cell_id"),
        sturdy_uri: row.get("sturdy_uri"),
        recipient_cell_id: row.get("recipient_cell_id"),
        local_signature: row.get("local_signature"),
        status: row.get("status"),
        created_at: row.get("created_at"),
        redeemed_at: row.get("redeemed_at"),
    }
}

fn held_credential_from_row(row: sqlx::sqlite::SqliteRow) -> HeldCredential {
    HeldCredential {
        credential_id: row.get("credential_id"),
        discord_id: row.get("discord_id"),
        holder_cell_id: row.get("holder_cell_id"),
        issuer_cell_id: row.get("issuer_cell_id"),
        schema: row.get("schema"),
        issued_at: row.get("issued_at"),
        turn_hash: row.get("turn_hash"),
        encoded_credential: row.get("encoded_credential"),
        attributes_json: row.get("attributes_json"),
        created_at: row.get("created_at"),
    }
}

/// A recorded transaction.
#[derive(Debug, Clone, sqlx::FromRow)]
pub struct TransactionRecord {
    pub from_user: String,
    pub to_user: String,
    pub amount: i64,
    pub tx_hash: String,
    pub timestamp: i64,
}

fn chrono_now() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

fn short_local_hash(input: &str) -> String {
    let hash = blake3::hash(input.as_bytes()).to_hex().to_string();
    hash[..12.min(hash.len())].to_string()
}

async fn ensure_column(
    pool: &Pool<Sqlite>,
    table: &str,
    column: &str,
    definition: &str,
) -> Result<(), sqlx::Error> {
    let pragma = format!("PRAGMA table_info({table})");
    let rows = sqlx::query(&pragma).fetch_all(pool).await?;
    let exists = rows
        .iter()
        .any(|row| row.get::<String, _>("name") == column);

    if !exists {
        let alter = format!("ALTER TABLE {table} ADD COLUMN {column} {definition}");
        sqlx::query(&alter).execute(pool).await?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Database, IdentityMode};

    #[tokio::test]
    async fn hosted_identity_records_mode() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.register_user("42", "abc").await.unwrap();

        let identity = db.get_user_identity("42").await.unwrap().unwrap();
        assert_eq!(identity.cell_id, "abc");
        assert_eq!(identity.mode, IdentityMode::Hosted);
        assert_eq!(identity.link_challenge, None);
    }

    #[tokio::test]
    async fn pending_external_link_is_not_hosted() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.create_pending_external_link("42", "def", "challenge")
            .await
            .unwrap();

        let identity = db.get_user_identity("42").await.unwrap().unwrap();
        assert_eq!(identity.cell_id, "def");
        assert_eq!(identity.mode, IdentityMode::ExternalPending);
        assert_eq!(identity.link_challenge.as_deref(), Some("challenge"));
    }

    #[tokio::test]
    async fn starbridge_activity_roundtrips() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.record_starbridge_activity(
            "nameservice",
            "register",
            "42",
            Some("7"),
            Some("alice"),
            "submitted",
            serde_json::json!({"name":"alice"}),
        )
        .await
        .unwrap();

        let rows = db.get_recent_starbridge_activity(10).await.unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].app, "nameservice");
        assert_eq!(rows[0].action, "register");
        assert_eq!(rows[0].guild_id.as_deref(), Some("7"));
        assert_eq!(rows[0].subject.as_deref(), Some("alice"));
    }

    #[tokio::test]
    async fn identity_holder_store_roundtrips() {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        db.store_held_credential(
            "42",
            "holder",
            "issuer",
            "cred1",
            "kyc-v1",
            123,
            Some("turn"),
            "{\"encoded\":\"credential\"}",
            "{\"age\":21}",
        )
        .await
        .unwrap();

        let rows = db.list_held_credentials("42", "holder", 10).await.unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].credential_id, "cred1");
        assert_eq!(rows[0].schema, "kyc-v1");

        let matched = db
            .find_held_credential_for_predicate("42", "holder", "age>=18")
            .await
            .unwrap()
            .unwrap();
        assert_eq!(matched.credential_id, "cred1");

        let presentation = db
            .create_identity_presentation(
                "7",
                "42",
                "holder",
                "age>=18",
                "presentation_unavailable",
                Some("cred1"),
                "{\"status\":\"presentation_unavailable\"}",
            )
            .await
            .unwrap();
        assert_eq!(presentation.credential_id.as_deref(), Some("cred1"));
    }
}
