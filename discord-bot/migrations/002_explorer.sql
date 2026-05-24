-- Explorer feature: activity feed configuration and watch subscriptions.

-- Activity feed configuration (which channel to post to, per guild)
CREATE TABLE IF NOT EXISTS explorer_config (
    guild_id TEXT PRIMARY KEY,
    feed_channel_id TEXT NOT NULL,
    large_transfer_threshold INTEGER NOT NULL DEFAULT 1000,
    created_at TEXT NOT NULL DEFAULT (datetime('now'))
);

-- Last seen block height (for polling new blocks)
CREATE TABLE IF NOT EXISTS explorer_state (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
);

-- Watch subscriptions (DM users on cell activity)
CREATE TABLE IF NOT EXISTS explorer_watches (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    discord_id TEXT NOT NULL,
    cell_id TEXT NOT NULL,
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    UNIQUE(discord_id, cell_id)
);
