//! Nameservice commands — the demoable starbridge-app flow over a live node.
//!
//! These commands drive the `starbridge-nameservice` state machine through the
//! node's `/turn/submit` JSON ingress, which carries a real signed call-forest
//! and runs the canonical (Lean-producer, when enabled) commit path. A name is
//! a fixed slot schema written into a cell with `SetField` + `EmitEvent`
//! effects:
//!
//! | Slot | Meaning            | Encoding                                   |
//! |:---:|---------------------|--------------------------------------------|
//! | 2   | `name_hash`         | `blake3(name)`                             |
//! | 3   | `owner_hash`        | `blake3(owner_pubkey_hex_or_string)`       |
//! | 4   | `expiry`            | big-endian u64 in the trailing 8 bytes     |
//! | 5   | `revoked` tombstone | `blake3("dregg-nameservice-revoked:"+name)`|
//! | 6   | `resolve_target`    | `blake3(target_uri)`                        |
//!
//! These encodings mirror `starbridge_nameservice::{name_hash, expiry_field,
//! revoked_tombstone, resolve_target}` and `app-framework`'s
//! `field_from_bytes` / `field_from_u64` byte-for-byte, so the slots this CLI
//! writes are exactly what the executor (and the app's inspectors) read back.
//!
//! Registration writes into the operator's own agent cell by default — the
//! cell `dregg turn` already acts on — so a newcomer can `dregg name register`
//! against a freshly-faucet-funded node with no extra setup.

use clap::Subcommand;

use crate::config::Config;
use crate::output::Context;

use super::{get_json, post_json};

// Slot schema — mirrors starbridge-apps/nameservice/src/lib.rs.
const NAME_HASH_SLOT: usize = 2;
const OWNER_HASH_SLOT: usize = 3;
const EXPIRY_SLOT: usize = 4;
/// Public: `demo` recycles this slot between runs on the program-less demo cell.
pub(crate) const REVOKED_SLOT: usize = 5;
const RESOLVE_TARGET_SLOT: usize = 6;

#[derive(Subcommand)]
pub enum NameCommand {
    /// Register a name into a cell (slots: name / owner / expiry).
    ///
    /// Writes `blake3(name)`, `blake3(owner)`, and the expiry height, then emits
    /// a `name-registered` event — all through one signed turn on the verified
    /// commit path.
    ///
    /// One name lives per cell (the slot schema is fixed). Registering a second
    /// name into the same cell overwrites the first; pass a distinct `--cell`
    /// (faucet-minted) per name. The default cell is your agent cell — handy for
    /// a single-name quickstart.
    ///
    ///   dregg name register alice.dregg --expiry 1000000
    Register {
        /// The name to register (e.g. `alice.dregg`).
        name: String,
        /// Rent expiry block height.
        #[arg(long, default_value_t = 1_000_000)]
        expiry: u64,
        /// Owner identifier (defaults to the operator's public key).
        #[arg(long)]
        owner: Option<String>,
        /// Cell to register into (defaults to your agent cell).
        #[arg(long)]
        cell: Option<String>,
        /// Turn fee (computron budget cap; charged in full from the cell).
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Resolve a name: read its slots back from the cell and show its state.
    ///
    ///   dregg name resolve alice.dregg
    Resolve {
        /// The name to resolve.
        name: String,
        /// Cell holding the name (defaults to your agent cell).
        #[arg(long)]
        cell: Option<String>,
    },

    /// Point a name at a target URI (writes the resolve-target slot).
    ///
    ///   dregg name set-target alice.dregg --target dregg://cell/abcd...
    SetTarget {
        /// The name.
        name: String,
        /// Target URI to resolve to.
        #[arg(long)]
        target: String,
        /// Cell holding the name (defaults to your agent cell).
        #[arg(long)]
        cell: Option<String>,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Renew a name (push its expiry forward — Monotonic-safe).
    Renew {
        /// The name.
        name: String,
        /// New expiry block height (must be >= current).
        #[arg(long)]
        expiry: u64,
        /// Cell holding the name.
        #[arg(long)]
        cell: Option<String>,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Transfer a name to a new owner (rewrites the owner-hash slot).
    Transfer {
        /// The name.
        name: String,
        /// New owner identifier.
        #[arg(long = "to")]
        new_owner: String,
        /// Cell holding the name.
        #[arg(long)]
        cell: Option<String>,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },

    /// Revoke a name (one-way tombstone into the revoked slot).
    Revoke {
        /// The name.
        name: String,
        /// Cell holding the name.
        #[arg(long)]
        cell: Option<String>,
        /// Turn fee.
        #[arg(long, default_value_t = 1000)]
        fee: u64,
    },
}

pub async fn run(
    cmd: NameCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        NameCommand::Register {
            name,
            expiry,
            owner,
            cell,
            fee,
        } => register(cfg, ctx, &name, expiry, owner, cell, fee).await,
        NameCommand::Resolve { name, cell } => resolve(cfg, ctx, &name, cell).await,
        NameCommand::SetTarget {
            name,
            target,
            cell,
            fee,
        } => set_target(cfg, ctx, &name, &target, cell, fee).await,
        NameCommand::Renew {
            name,
            expiry,
            cell,
            fee,
        } => renew(cfg, ctx, &name, expiry, cell, fee).await,
        NameCommand::Transfer {
            name,
            new_owner,
            cell,
            fee,
        } => transfer(cfg, ctx, &name, &new_owner, cell, fee).await,
        NameCommand::Revoke { name, cell, fee } => revoke(cfg, ctx, &name, cell, fee).await,
    }
}

// ─── Canonical field-element encodings (mirror app-framework/src/fields.rs) ──

/// `blake3(bytes)` → 64-char hex field element. Mirrors `field_from_bytes`.
pub fn field_from_bytes_hex(bytes: &[u8]) -> String {
    hex::encode(blake3::hash(bytes).as_bytes())
}

/// big-endian u64 in trailing 8 bytes → 64-char hex. Mirrors `field_from_u64`.
pub fn field_from_u64_hex(value: u64) -> String {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    hex::encode(out)
}

pub fn name_hash_hex(name: &str) -> String {
    field_from_bytes_hex(name.as_bytes())
}

pub fn owner_hash_hex(owner: &str) -> String {
    field_from_bytes_hex(owner.as_bytes())
}

pub fn revoked_tombstone_hex(name: &str) -> String {
    let mut input = b"dregg-nameservice-revoked:".to_vec();
    input.extend_from_slice(name.as_bytes());
    field_from_bytes_hex(&input)
}

mod hex {
    pub fn encode(bytes: impl AsRef<[u8]>) -> String {
        bytes.as_ref().iter().map(|b| format!("{b:02x}")).collect()
    }
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/// Resolve the target cell: explicit `--cell`, else the operator's agent cell.
async fn target_cell(
    cfg: &Config,
    cell: Option<String>,
) -> Result<String, Box<dyn std::error::Error>> {
    if let Some(c) = cell {
        return Ok(c);
    }
    let ident = get_json(cfg, "/api/node/identity")
        .await
        .map_err(|e| format!("could not read operator identity (is the node unlocked?): {e}"))?;
    ident["agent_cell"]
        .as_str()
        .map(|s| s.to_string())
        .ok_or_else(|| "node identity did not return an agent_cell".into())
}

/// Default owner: the operator's own public key (from node identity).
async fn default_owner(cfg: &Config) -> Result<String, Box<dyn std::error::Error>> {
    let ident = get_json(cfg, "/api/node/identity").await?;
    Ok(ident["public_key"]
        .as_str()
        .unwrap_or("operator")
        .to_string())
}

/// Submit a single-action turn carrying the given effects, render the outcome.
async fn submit_effects(
    cfg: &Config,
    target: &str,
    method: &str,
    effects: Vec<serde_json::Value>,
    fee: u64,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    use serde_json::json;
    let req = json!({
        "agent": "00".repeat(32),
        "nonce": 0,
        "fee": fee,
        "memo": serde_json::Value::Null,
        "actions": [{ "target": target, "method": method, "effects": effects }],
    });
    // `/api/turns/submit` is the node's alias for `/turn/submit` — same
    // handler, same auth — but it also passes gateway proxies that only
    // forward `/api/*` (the public devnet's Caddy).
    let data = post_json(cfg, "/api/turns/submit", &req).await?;
    Ok(data)
}

/// Render a submitted turn's outcome and return whether the node accepted it.
///
/// Callers must propagate a `false` as an `Err` — swallowing it made
/// `dregg demo` print its success banner after every mutating step was
/// rejected (and left the standalone `dregg name …` commands exiting 0 on
/// rejection).
#[must_use]
fn render_turn(ctx: &Context, data: &serde_json::Value, action: &str) -> bool {
    let accepted = data["accepted"].as_bool().unwrap_or(false);
    let turn_hash = data["turn_hash"].as_str().unwrap_or("?");
    let proof_status = data["proof_status"].as_str().unwrap_or("unknown");
    if accepted {
        ctx.success(&format!("{action} committed"));
    } else {
        let err = data["error"].as_str().unwrap_or(turn_hash);
        ctx.error(&format!("{action} rejected: {err}"));
    }
    ctx.kv("Turn", &crate::output::abbrev_hex(turn_hash, 8, 4));
    let lowered = proof_status.to_lowercase();
    let proof_line = match lowered.as_str() {
        "proved" => "PROVED (real STARK verified)",
        "not_required" => {
            "not required (coordination; signature attestation only, no validity proof)"
        }
        other => other,
    };
    ctx.kv("Proof", proof_line);
    accepted
}

/// Turn a rejected submission into a hard error naming the failed action.
fn rejected(action: &str) -> Box<dyn std::error::Error> {
    format!("{action} was rejected by the node (see the error above)").into()
}

// ─── Commands ────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
async fn register(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    expiry: u64,
    owner: Option<String>,
    cell: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let target = target_cell(cfg, cell).await?;
    let owner = match owner {
        Some(o) => o,
        None => default_owner(cfg).await?,
    };
    let name_h = name_hash_hex(name);
    let owner_h = owner_hash_hex(&owner);
    let expiry_h = field_from_u64_hex(expiry);

    if !cfg.is_json() {
        ctx.header(&format!("Register '{name}'"));
        ctx.kv("Cell", &crate::output::abbrev_hex(&target, 8, 4));
        ctx.kv("name_hash", &crate::output::abbrev_hex(&name_h, 8, 4));
        ctx.kv("owner_hash", &crate::output::abbrev_hex(&owner_h, 8, 4));
        ctx.kv("expiry", &expiry.to_string());
    }

    let effects = vec![
        json!({ "kind": "set_field", "index": NAME_HASH_SLOT, "value": name_h }),
        json!({ "kind": "set_field", "index": OWNER_HASH_SLOT, "value": owner_h }),
        json!({ "kind": "set_field", "index": EXPIRY_SLOT, "value": expiry_h }),
        json!({ "kind": "emit_event", "topic": "name-registered", "data": [name_hash_hex(name), owner_hash_hex(&owner)] }),
    ];
    let spinner = ctx.spinner("Submitting registration (sign → execute → prove)...");
    let data = submit_effects(cfg, &target, "register", effects, fee).await?;
    spinner.finish_and_clear();

    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    if !render_turn(ctx, &data, "Registration") {
        return Err(rejected("Registration"));
    }
    ctx.info(&format!(
        "  Resolve it:  dregg name resolve {name} --cell {target}"
    ));
    Ok(())
}

async fn resolve(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    cell: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let target = target_cell(cfg, cell).await?;
    let spinner = ctx.spinner("Reading name slots from the cell...");
    let detail = get_json(cfg, &format!("/api/cell/{target}")).await?;
    spinner.finish_and_clear();

    let found = detail["found"].as_bool().unwrap_or(false);
    let fields = detail["fields"].as_array().cloned().unwrap_or_default();
    let slot = |i: usize| -> String {
        fields
            .get(i)
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string()
    };

    let expected_name = name_hash_hex(name);
    let actual_name = slot(NAME_HASH_SLOT);
    let owner = slot(OWNER_HASH_SLOT);
    let expiry_hex = slot(EXPIRY_SLOT);
    let revoked = slot(REVOKED_SLOT);
    let resolve_target = slot(RESOLVE_TARGET_SLOT);
    let zero = "0".repeat(64);

    let bound = actual_name == expected_name;
    let is_revoked = !revoked.is_empty() && revoked != zero;
    let expiry = u64_from_field_hex(&expiry_hex);

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "name": name,
            "cell": target,
            "found": found,
            "bound": bound,
            "revoked": is_revoked,
            "name_hash": actual_name,
            "owner_hash": owner,
            "expiry": expiry,
            "resolve_target": resolve_target,
        }));
        return Ok(());
    }

    ctx.header(&format!("Resolve '{name}'"));
    ctx.kv("Cell", &crate::output::abbrev_hex(&target, 8, 4));
    if !found {
        ctx.error("Cell not found in the ledger.");
        return Ok(());
    }
    if !bound {
        ctx.warn(&format!(
            "name_hash slot ({}) does not match blake3('{name}')",
            crate::output::abbrev_hex(&actual_name, 6, 4)
        ));
        ctx.info("  This cell does not hold this name (yet). Register it first.");
        return Ok(());
    }
    if is_revoked {
        ctx.error("REVOKED — this name has been tombstoned (one-way).");
    } else {
        ctx.success(&format!("'{name}' is bound and active"));
    }
    ctx.kv("Owner", &crate::output::abbrev_hex(&owner, 8, 4));
    ctx.kv("Expiry", &expiry.to_string());
    if !resolve_target.is_empty() && resolve_target != zero {
        ctx.kv("Target", &crate::output::abbrev_hex(&resolve_target, 8, 4));
    } else {
        ctx.kv_dim("Target", "(unset)");
    }
    Ok(())
}

/// Decode a BE-padded u64 field-element hex back into the integer.
fn u64_from_field_hex(hexstr: &str) -> u64 {
    if hexstr.len() != 64 {
        return 0;
    }
    // trailing 8 bytes = trailing 16 hex chars, big-endian.
    let tail = &hexstr[48..];
    u64::from_str_radix(tail, 16).unwrap_or(0)
}

async fn set_target(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    target_uri: &str,
    cell: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let target = target_cell(cfg, cell).await?;
    let target_h = field_from_bytes_hex(target_uri.as_bytes());
    let effects = vec![
        json!({ "kind": "set_field", "index": RESOLVE_TARGET_SLOT, "value": target_h }),
        json!({ "kind": "emit_event", "topic": "name-target-set", "data": [name_hash_hex(name)] }),
    ];
    let spinner = ctx.spinner("Setting resolve target...");
    let data = submit_effects(cfg, &target, "set-target", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header(&format!("Set target for '{name}'"));
    ctx.kv("Target URI", target_uri);
    if !render_turn(ctx, &data, "Set-target") {
        return Err(rejected("Set-target"));
    }
    Ok(())
}

async fn renew(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    expiry: u64,
    cell: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let target = target_cell(cfg, cell).await?;
    let effects = vec![
        json!({ "kind": "set_field", "index": EXPIRY_SLOT, "value": field_from_u64_hex(expiry) }),
        json!({ "kind": "emit_event", "topic": "name-renewed", "data": [name_hash_hex(name)] }),
    ];
    let spinner = ctx.spinner("Renewing...");
    let data = submit_effects(cfg, &target, "renew", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header(&format!("Renew '{name}'"));
    ctx.kv("New expiry", &expiry.to_string());
    if !render_turn(ctx, &data, "Renewal") {
        return Err(rejected("Renewal"));
    }
    Ok(())
}

async fn transfer(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    new_owner: &str,
    cell: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let target = target_cell(cfg, cell).await?;
    let effects = vec![
        json!({ "kind": "set_field", "index": OWNER_HASH_SLOT, "value": owner_hash_hex(new_owner) }),
        json!({ "kind": "emit_event", "topic": "name-transferred", "data": [name_hash_hex(name), owner_hash_hex(new_owner)] }),
    ];
    let spinner = ctx.spinner("Transferring ownership...");
    let data = submit_effects(cfg, &target, "transfer", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header(&format!("Transfer '{name}'"));
    ctx.kv(
        "New owner",
        &crate::output::abbrev_hex(&owner_hash_hex(new_owner), 8, 4),
    );
    if !render_turn(ctx, &data, "Transfer") {
        return Err(rejected("Transfer"));
    }
    Ok(())
}

async fn revoke(
    cfg: &Config,
    ctx: &Context,
    name: &str,
    cell: Option<String>,
    fee: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    use serde_json::json;
    let target = target_cell(cfg, cell).await?;
    let effects = vec![
        json!({ "kind": "set_field", "index": REVOKED_SLOT, "value": revoked_tombstone_hex(name) }),
        json!({ "kind": "emit_event", "topic": "name-revoked", "data": [name_hash_hex(name)] }),
    ];
    let spinner = ctx.spinner("Revoking (one-way tombstone)...");
    let data = submit_effects(cfg, &target, "revoke", effects, fee).await?;
    spinner.finish_and_clear();
    if cfg.is_json() {
        ctx.json_stdout(&data);
        return Ok(());
    }
    ctx.header(&format!("Revoke '{name}'"));
    if !render_turn(ctx, &data, "Revocation") {
        return Err(rejected("Revocation"));
    }
    Ok(())
}
