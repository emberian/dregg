//! Database layer (SQLite via sqlx).

use sqlx::{Pool, Sqlite, SqlitePool};

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
                cell_id TEXT NOT NULL
            )",
        )
        .execute(&pool)
        .await?;

        Ok(Self { pool })
    }

    // ─── User / wallet methods ──────────────────────────────────────────────

    /// Check if a user has a wallet.
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
        let row: Option<(String,)> =
            sqlx::query_as("SELECT cell_id FROM users WHERE discord_id = ?")
                .bind(discord_id)
                .fetch_optional(&self.pool)
                .await?;
        Ok(row.map(|(id,)| id))
    }

    // ─── Activity feed methods ──────────────────────────────────────────────

    /// Get last processed block height for activity feed.
    pub async fn get_last_block_height(&self) -> Result<u64, sqlx::Error> {
        let row: Option<(String,)> =
            sqlx::query_as("SELECT value FROM kv WHERE key = 'last_block_height'")
                .fetch_optional(&self.pool)
                .await?;
        Ok(row
            .and_then(|(v,)| v.parse::<u64>().ok())
            .unwrap_or(0))
    }

    /// Set last processed block height.
    pub async fn set_last_block_height(&self, height: u64) -> Result<(), sqlx::Error> {
        sqlx::query(
            "INSERT OR REPLACE INTO kv (key, value) VALUES ('last_block_height', ?)",
        )
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
        sqlx::query(
            "INSERT OR REPLACE INTO feed_channels (guild_id, channel_id) VALUES (?, ?)",
        )
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
        let result = sqlx::query(
            "INSERT OR IGNORE INTO watchers (user_id, cell_id) VALUES (?, ?)",
        )
        .bind(discord_id)
        .bind(cell_id)
        .execute(&self.pool)
        .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Remove a watch subscription.
    pub async fn remove_watch(
        &self,
        discord_id: &str,
        cell_id: &str,
    ) -> Result<bool, sqlx::Error> {
        let result =
            sqlx::query("DELETE FROM watchers WHERE user_id = ? AND cell_id = ?")
                .bind(discord_id)
                .bind(cell_id)
                .execute(&self.pool)
                .await?;
        Ok(result.rows_affected() > 0)
    }

    /// Get users watching a specific cell.
    pub async fn get_watchers_for_cell(&self, cell_id: &str) -> Result<Vec<String>, sqlx::Error> {
        let rows: Vec<(String,)> =
            sqlx::query_as("SELECT user_id FROM watchers WHERE cell_id = ?")
                .bind(cell_id)
                .fetch_all(&self.pool)
                .await?;
        Ok(rows.into_iter().map(|(id,)| id).collect())
    }
}
