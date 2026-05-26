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
}
