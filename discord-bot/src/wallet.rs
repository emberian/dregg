//! Custodial wallet: deterministic key derivation and cell management.
//!
//! Keys are derived from `BLAKE3_derive_key("pyana-discord-bot-v1", bot_secret || discord_user_id)`.
//! This means the same Discord user always maps to the same cell — no recovery needed.

/// A derived wallet for a Discord user.
pub struct DerivedWallet {
    /// The 32-byte private key.
    pub private_key: [u8; 32],
    /// The 32-byte public key (derived from private key via BLAKE3).
    pub public_key: [u8; 32],
    /// The cell ID (derived from public key + domain).
    pub cell_id: [u8; 32],
}

impl DerivedWallet {
    /// Derive a wallet for the given Discord user ID using the bot secret.
    pub fn derive(bot_secret: &[u8; 32], discord_user_id: u64) -> Self {
        // Step 1: Derive the private key
        let user_id_bytes = discord_user_id.to_le_bytes();
        let mut input = Vec::with_capacity(32 + 8);
        input.extend_from_slice(bot_secret);
        input.extend_from_slice(&user_id_bytes);

        let private_key = blake3::derive_key("pyana-discord-bot-v1", &input);

        // Step 2: Derive the public key from private key
        let public_key = blake3::derive_key("pyana-discord-bot-pubkey-v1", &private_key);

        // Step 3: Derive cell ID (matches pyana-types CellId::derive_raw logic)
        let token_domain = blake3::derive_key("pyana-discord-bot-domain-v1", b"devnet");
        let mut cell_input = Vec::with_capacity(64);
        cell_input.extend_from_slice(&public_key);
        cell_input.extend_from_slice(&token_domain);
        let cell_id = blake3::derive_key("pyana-cell-id-v1", &cell_input);

        Self {
            private_key,
            public_key,
            cell_id,
        }
    }

    /// Return the cell ID as a hex string.
    pub fn cell_id_hex(&self) -> String {
        hex::encode(self.cell_id)
    }

    /// Return the private key as a hex string (for export).
    pub fn private_key_hex(&self) -> String {
        hex::encode(self.private_key)
    }

    /// Return the public key as a hex string.
    pub fn public_key_hex(&self) -> String {
        hex::encode(self.public_key)
    }

    /// Short display of cell ID (first 8 bytes / 16 hex chars).
    pub fn cell_id_short(&self) -> String {
        hex::encode(&self.cell_id[..8])
    }
}
