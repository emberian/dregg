//! Custodial wallet: deterministic per-user wallets backed by the canonical
//! `pyana_app_framework::AppWallet` (and underneath, `pyana_sdk::AgentWallet`).
//!
//! Each Discord user maps to a deterministic 32-byte seed:
//!
//! ```text
//! seed = BLAKE3_derive_key("pyana-discord-bot-v1", bot_secret || discord_user_id)
//! ```
//!
//! The seed is fed into `AgentWallet::from_key_bytes` to produce a real
//! Ed25519 signing identity. The Discord user's `CellId` is then
//! `AppWallet::cell_id()` — the canonical pyana derivation (public_key +
//! BLAKE3(domain)). No bespoke key derivation, no parallel cell-id
//! derivation: the bot is a peer of the SDK rather than a separate
//! implementation.
//!
//! # Wire-signature transition gap
//!
//! The legacy devnet wire format (still in use for `/api/turns/submit`,
//! `/api/gallery/auctions/<id>/bid`, `/api/identity/credentials/issue`, etc.)
//! expects a hex-encoded `signature` field defined as
//! `blake3(action_bytes || raw_secret)`. That scheme is *not* Ed25519, and
//! `AppWallet` deliberately hides the raw secret to keep apps from
//! reaching past the framework. Until the devnet endpoints accept
//! canonical signed `Action`s / `Turn`s, this wallet retains the raw
//! 32-byte seed alongside the `AppWallet` and exposes it via
//! [`UserWallet::legacy_secret`] for the BLAKE3-MAC wire-signature path.
//! Once the devnet wire format moves to canonical actions, that field
//! and its accessor should be deleted in favor of `AppWallet::sign_action`.

use pyana_app_framework::AppWallet;
use pyana_sdk::AgentWallet;
use zeroize::Zeroizing;

/// A deterministic per-user wallet handle.
///
/// Wraps a canonical [`AppWallet`] derived from the bot secret + Discord
/// user id. The raw seed is retained for the legacy BLAKE3-MAC wire
/// signature path (see module docs).
pub struct UserWallet {
    /// Canonical app-level wallet handle (Ed25519, framework-bound).
    pub app: AppWallet,
    /// Raw 32-byte seed (== Ed25519 secret key). Held only for the
    /// legacy BLAKE3-MAC wire signature; do not use for new signing
    /// paths — call `app.sign_action(...)` / `app.make_action(...)`.
    legacy_secret: [u8; 32],
    /// Cached hex-encoded ed25519 public key.
    public_key_hex_cached: String,
    /// Cached cell-id bytes.
    cell_id_bytes_cached: [u8; 32],
    /// Cached cell-id hex.
    cell_id_hex_cached: String,
}

impl UserWallet {
    /// Derive a wallet for the given Discord user.
    ///
    /// * `bot_secret` — the bot's master secret (32 bytes from env).
    /// * `discord_user_id` — the Discord snowflake id.
    /// * `federation_id` — the federation this bot binds signed
    ///   actions to (the bot's configured pyana node group). Used by
    ///   `AppWallet` to bind action signatures against cross-federation
    ///   replay.
    pub fn derive(bot_secret: &[u8; 32], discord_user_id: u64, federation_id: [u8; 32]) -> Self {
        // Step 1: derive the deterministic 32-byte seed (matches the
        // legacy scheme so existing user→cell mappings persist).
        let user_id_bytes = discord_user_id.to_le_bytes();
        let mut input = Vec::with_capacity(32 + 8);
        input.extend_from_slice(bot_secret);
        input.extend_from_slice(&user_id_bytes);
        let seed = blake3::derive_key("pyana-discord-bot-v1", &input);

        // Step 2: build a canonical AgentWallet from the seed. Wrapping
        // the secret in `Zeroizing` here ensures the temporary copy
        // we hand to `from_key_bytes` is wiped after construction.
        let secret = Zeroizing::new(seed);
        let agent = AgentWallet::from_key_bytes(secret);

        // Step 3: wrap in an AppWallet bound to this bot's federation.
        // The default domain ("default") is what AgentWallet::cell_id
        // uses for its identity-cell derivation; we use that same
        // domain here so callers can call `wallet.cell_id()` without
        // threading a domain string.
        let public_key_hex_cached = hex::encode(agent.public_key().0);
        let app = AppWallet::new(agent, federation_id);
        let cell_id = app.cell_id();
        let cell_id_bytes_cached = cell_id.0;
        let cell_id_hex_cached = hex::encode(cell_id_bytes_cached);

        Self {
            app,
            legacy_secret: seed,
            public_key_hex_cached,
            cell_id_bytes_cached,
            cell_id_hex_cached,
        }
    }

    /// The user's cell id (32 bytes).
    pub fn cell_id_bytes(&self) -> [u8; 32] {
        self.cell_id_bytes_cached
    }

    /// The user's cell id as lowercase hex.
    pub fn cell_id_hex(&self) -> &str {
        &self.cell_id_hex_cached
    }

    /// Short cell-id display (first 8 bytes / 16 hex chars).
    pub fn cell_id_short(&self) -> String {
        hex::encode(&self.cell_id_bytes_cached[..8])
    }

    /// The user's Ed25519 public key as lowercase hex.
    pub fn public_key_hex(&self) -> &str {
        &self.public_key_hex_cached
    }

    /// The raw secret bytes (== Ed25519 secret) — exposed only for the
    /// legacy BLAKE3-MAC wire signature path used by current devnet
    /// endpoints. See module docs.
    pub fn legacy_secret(&self) -> &[u8; 32] {
        &self.legacy_secret
    }

    /// Hex-encode the legacy secret for `/wallet export`.
    ///
    /// Discord users see this as their "private key"; it is the
    /// Ed25519 secret. Once the wire format migration completes, this
    /// continues to be a valid export (matches `AgentWallet::from_key_bytes`).
    pub fn private_key_hex(&self) -> String {
        hex::encode(self.legacy_secret)
    }
}

/// Sign a string action using the legacy BLAKE3-MAC scheme accepted by
/// the current devnet endpoints. Returns a hex-encoded 32-byte MAC.
///
/// This is the wire signature path described in the module docs — it
/// will be deleted once the devnet endpoints accept canonical signed
/// `Action`s (built via `wallet.app.make_action(...)`).
pub fn sign_legacy(wallet: &UserWallet, action_bytes: &[u8]) -> String {
    let mut msg = Vec::with_capacity(action_bytes.len() + 32);
    msg.extend_from_slice(action_bytes);
    msg.extend_from_slice(wallet.legacy_secret());
    let sig = blake3::hash(&msg);
    hex::encode(sig.as_bytes())
}
